open Term
open Recordops

(* type direction = DLeft | DRight *)
(*
let lift_spine n (th, tl) = 
 (lift n th, List.map (lift n) tl)

      
(* imported from Evarutil *)
let whd_head_evar_stack sigma c =
  let rec whrec (c, l as s) =
    match kind_of_term c with
      | Evar (evk,args as ev) when Evd.is_defined sigma evk
	  -> whrec (existential_value sigma ev, l)
      | Cast (c,_,_) -> whrec (c, l)
      | App (f,args) -> whrec (f, Array.fold_right (fun a l -> a::l) args l)
      | _ -> s
  in
  whrec (c, [])
       


let option_fold_right f l =
  let rec fold_me l' =
    match l' with
    | [] -> Some []
    | a :: l'' -> 
	f a >>= fun b -> 
	fold_me l'' >>= fun l''' -> return (b :: l''')
  in fold_me l

let option_fold_rightA f a =
  let a' = Array.copy a in
  let rec fold_me i =
    match i with
    | 0 -> return a'
    | n -> 
	f a.(n-1) >>= fun b -> 
	fold_me (n-1) >>= fun a'' -> return a''
  in fold_me (Array.length a)



(* Removes all the items in nc with index listed in rml.
   E.g. filter [x,y,z] [1] = [x, z] *)
let filter nc rml =
  let rec rechyps i rml nc =
    if rml = [] then
      nc
    else if i < List.hd rml then
      (List.hd nc) :: (rechyps (i+1) rml (List.tl nc))
    else
      rechyps (i+1) (List.tl rml) (List.tl nc)
  in 
  if rml = [] 
  then nc
  else rechyps 0 rml nc


let collect_vars =
  let rec aux vars c = match kind_of_term c with
  | Var id -> Idset.add id vars
  | _ -> fold_constr aux vars c in
  aux Idset.empty


let free_vars_in sigma tm vars = 
  Idset.for_all (fun v -> List.mem v vars) (collect_vars (nf_evar sigma tm))


let make_safe sigma nc =
  let rec mksafe vars nc i = 
    match vars, nc with
    | [], [] -> [], []
    | (_ :: vars'), (id, body, ty as t) :: nc' ->
	let rml, res = mksafe vars' nc' (i+1) in
	if (free_vars_in sigma ty vars' &&
	   match body with
	   | None -> true
	   | Some tm -> free_vars_in sigma tm vars')
	then rml, t :: res
	else i :: rml, res
    | _ -> assert false
  in mksafe (ids_of_named_context nc) nc 0


let instantiate_restriction sigma ev rml =
  let evi = Evd.find_undefined sigma ev in
  let rml', nc = make_safe sigma (filter (evar_filtered_context evi) rml) in
  if not (free_vars_in sigma evi.evar_concl (ids_of_named_context nc)) then
(* I actually have to restrict evars appearing in the type, since prunning might work *)
    None
  else 
    let res = 
(*
      let v = new_untyped_evar () in
      let evi' =
      { evi with 
	evar_body = Evar_empty;
	evar_hyps = val_of_named_context nc;
	evar_filter = Array.to_list (Array.init (List.length nc) (fun _-> true));
	evar_candidates = None }
      in
      let sigma' = Evd.add sigma v evi' in
      let idsubst = id_substitution nc in
      let t = mkEvar (v, idsubst) in
*)
      let (sigma', ev) = Evarutil.new_evar_instance nc sigma (evar_concl evi)  in
      Some (v, Evd.define ev t sigma', rml')
    in res

*)

let ise_list2 evd f l1 l2 =
  let rec ise_list2 i l1 l2 =
    match l1,l2 with
      [], [] -> (true, i)
    | [x], [y] -> f i x y
    | x::l1, y::l2 ->
        let (b, i') = f i x y in
        if b then ise_list2 i' l1 l2 else (false, evd)
    | _ -> (false, evd) in
  ise_list2 evd l1 l2

let ise_array2 evd f v1 v2 =
  let l1 = Array.length v1 in
  let l2 = Array.length v2 in
  assert (l1 <= l2) ;
  let diff = l2 - l1 in
  let rec allrec evdi n = 
    if n >= l1 then (true, evdi)
    else
      let (b, evdi') = f evdi v1.(n) v2.(n+diff) in
      if b then allrec evdi' (n+1) else (false, evd)
  in
  allrec evd 0

let (>>=) opt f = 
  match opt with
  | Some(x) -> f x
  | None -> None
   
let return x = Some x

let (&&=) opt f = 
  match opt with
  | (true, x) -> f x
  | _ -> opt

let (||=) opt f = 
  match opt with
  | (false, _) -> f ()
  | _ -> opt

let success s = (true, s)

let err s = (false, s)


let id_substitution nc = 
  let s = Sign.fold_named_context (fun (n,_,_) s -> mkVar n :: s) nc ~init:[] in
  Array.of_list s

(* pre: isVar v1 *)
let is_same_var v1 v2 =  isVar v2 && (destVar v1 = destVar v2)

(* pre: isRel v1 *)
let is_same_rel v1 v2 = isRel v2 && destRel v1 = destRel v2

let is_same_evar i1 ev2 =
  match kind_of_term ev2 with
  | Evar (i2, _) -> i1 = i2
  | _ -> false

let isVarOrRel c = isVar c || isRel c

let is_variable_subs = Util.array_for_all (fun c -> isVar c || isRel c)

let is_variable_args = List.for_all (fun c -> isVar c || isRel c)    

let find_unique test dest id s =
  let (i, j) = List.fold_right (fun c (i, j) -> 
    if test c && dest c = id
    then (i+1, j-1)
    else (i, if i > 0 then j else j-1))
    s (0, List.length s)
  in
  if i = 1 then Some j else None

let find_unique_var = find_unique isVar destVar

let find_unique_rel = find_unique isRel destRel


let var_is_def ts env var = 
  if not (Closure.is_transparent_variable ts var) then 
    false
  else
    let (_, v,_) = Environ.lookup_named var env in
    match v with
      | Some _ -> true
      | _ -> false
	
let var_value env var = 
  let (_, v,_) = Environ.lookup_named var env in
  match v with
  | Some c -> c
  | _ -> assert false
	
let const_is_def ts env c = 
  Closure.is_transparent_constant ts c && Environ.evaluable_constant c env
    
let const_value env c = Environ.constant_value env c
    
let rel_is_def ts env n =
  let (_,v,_) = Environ.lookup_rel n env in
  match v with
  | Some _ -> true
  | _ -> false
	
let rel_value env n =
  let (_,v,_) = Environ.lookup_rel n env in 
  match v with
  | Some v -> (lift n) v
  | _ -> assert false

let eq_rigid ts env sigma c l1 l2 unif is_def get_value =
  if is_def ts env c then
    begin
      let v = get_value env c
      in unif ts env sigma (applist (v, l1)) (applist (v, l2))
    end
  else
    err sigma
	
let transp_matchL ts env sigma c l t unif get_value =
  let v = get_value env c
  in unif ts env sigma (applist (v, l)) t
    
let transp_matchR ts env sigma c l t unif get_value =
  let v = get_value env c
  in unif ts env sigma t (applist (v, l))


(* pre: |s1| = |s2| 
   pos: None if s1 or s2 are not var to var subs
        Some l with l list of indexes where s1 and s2 do not agree *)
let intersect s1 s2 =
  let n = Array.length s1 in
  let rec intsct i =
    if i < n then
      if (isVarOrRel s1.(i) && isVarOrRel s2.(i)) then
	intsct (i+1) >>= fun l ->
	if (isVar s1.(i) && is_same_var s1.(i) s2.(i)) ||
	   (isRel s1.(i) && is_same_rel s1.(i) s2.(i)) 
	then Some l
	else Some (i :: l)
      else None
    else Some []
  in 
  assert (Array.length s2 = n) ;
  intsct 0

(* pre: ev is a not-defined evar *)
let unify_same env sigma ev subs1 subs2 =
  match intersect subs1 subs2 with
  | Some [] -> success sigma
  | _ -> err sigma


(*
(* pre: ev is a not-defined evar *)
let unify_same env sigma ev subs1 subs2 =
  match intersect subs1 subs2 with
  | Some [] -> (Debug.execute "Meta-Same-Same"; success sigma)
  | Some rml -> 
      let res =
	match instantiate_restriction sigma ev rml with
	| Some (_, sigma', _) -> success sigma'
	| None -> err sigma
      in (Debug.execute "Meta-Same" ; res)
  | None -> err sigma




let subseteq s1 s2 = List.for_all (fun v -> List.mem v s2) s1

let hat = List.map (fun (x, _, _) -> mkVar x)

let is_none m =
  match m with
  | None -> true
  | _ -> false

let get m =
  match m with
  | Some v -> v
  | _ -> raise PreconditionViolation

let fv m = 
  let rec fv' m i =
    match kind_of_term m with 
    | Var x -> [m]
    | Rel j when j > i -> [m]
    | _ -> 
      fold_constr_with_binders succ (fun i s c -> s @ fv' c i) i [] m
  in fv' m 0

let head sigma m =
  let (h, _) = whd_beta_stack sigma m in h
(*
  let rec head' m =
    match kind_of_term m with 
    | Cast (c, _, _) -> head' c
    | LetIn (_, _, c) -> head' c
    | App (c, _) -> head' c
    | Case (_, _ , c, _) -> head' c
    | _ -> m
  in head' m
*)

exception CannotPrune
let prune_context sigma rho tao psi =
  let rec pctxt tao psi =
    match (tao, psi) with
    | ([], []) -> Some []
    | (m :: tao', (x, t, a) :: psi1) -> 
      pctxt tao' psi1 >>= fun psi2 ->
      let hpsi2 = hat psi2 in
      if subseteq (fv m) rho && subseteq (fv a) hpsi2 && (is_none t || subseteq (fv (get t)) hpsi2) then
        Some ((x, t, a) :: psi2)
      else if isVarOrRel (head sigma m) && not (List.mem (head sigma m) rho) then
        Some psi2
      else
        None
    | _ -> raise PreconditionViolation
  in pctxt tao psi

let prune rsigma rho m =
  let rec pruneme m i =
    let m = whd_evar !rsigma m in
    match kind_of_term m with
    | Evar (u, tao) -> 
      let ui = Evd.find_undefined !rsigma u in
      let psi1 = evar_filtered_context ui in
      let opsi2 = prune_context !rsigma rho (Array.to_list tao) psi1 in
      if is_none opsi2 then
        false
      else 
        let psi2 = get opsi2 in
        if psi1 = psi2 then
          true
        else if subseteq (fv ui.evar_concl) (hat psi2) then
          let v = new_untyped_evar () in
          let evi' =
          { ui with 
            evar_body = Evar_empty;
            evar_hyps = val_of_named_context psi2;
            evar_filter = Array.to_list (Array.init (List.length psi2) (fun _-> true));
            evar_candidates = None }
          in
          let id_psi2 = id_substitution psi2 in
          let body = mkEvar (v, id_psi2) in
          rsigma := Evd.add !rsigma v evi' ;
          rsigma := Evd.define u body !rsigma ;
          true
        else
          false
 
    | Var x -> List.mem m rho

    | Rel j when j > i -> List.mem (mkRel (j-i)) rho 

    | _ -> 
      fold_constr_with_binders succ (fun i b c -> 
        b && pruneme c i) i true m
  in pruneme m 0


let rec define_evar_as_lambdas env sigma (ev, evargs) n =
    if n = 0 then
      sigma
    else
      let sigma', lam = define_evar_as_lambda env sigma (ev, evargs) in
      let _, _, ev' = destLambda lam in
      define_evar_as_lambdas env sigma (destEvar ev') (n-1)
*)

let (-.) n m =
  if n > m then n - m
  else 0

(* pre: |nc| = |s|
   nc is the context of the evar
   t is the term to invert
   s is the substitution of the evar
   args are the arguments of the evar *)
let invert nc t s args = 
  let sargs = s @ args in
  let nclength = List.length nc in
  let argslength = List.length args in
  let rec invert' t i =
    match kind_of_term t with
    | Var id -> 
	find_unique_var id sargs >>= fun j -> 
        if j < nclength then
	  let (name, _, _) = List.nth nc j in
	  return (mkVar name)
	else
	  return (mkRel (nclength+argslength - j))
    | Rel j when j > i-> 
	find_unique_rel (j-i) sargs >>= fun k -> 
        if k < nclength then
	  let (name, _, _) = List.nth nc k in
	  return (mkVar name)
	else
	  return (mkRel (nclength+argslength - k))
    | _ -> 
	try Some (map_constr_with_binders succ (fun i c -> 
	    match invert' c i with
	    | Some c' -> c'
	    | None -> raise Exit) i t)
	with Exit -> None
  in
  invert' t 0

(* given a list of arguments [x1 .. xn] with types [A1 .. An] and a
   [body] with free indices [1 .. n], it returns [fun x1 : A1 => .. =>
   fun xn : An => body].
*)
let fill_lambdas env sigma args body =
  List.fold_right (fun arg bdy-> 
    let ty = Retyping.get_type_of env sigma arg in
    mkLambda (Names.Anonymous, ty, bdy)) args body

(* [check_conv_record (t1,l1) (t2,l2)] tries to decompose the problem
   (t1 l1) = (t2 l2) into a problem

     l1 = params1@c1::extra_args1
     l2 = us2@extra_args2
     (t1 params1 c1) = (proji params (c xs))
     (t2 us2) = (cstr us)
     extra_args1 = extra_args2

   by finding a record R and an object c := [xs:bs](Build_R params v1..vn)
   with vi = (cstr us), for which we know that the i-th projection proji
   satisfies

      (proji params (c xs)) = (cstr us)

   Rem: such objects, usable for conversion, are defined in the objdef
   table; practically, it amounts to "canonically" equip t2 into a
   object c in structure R (since, if c1 were not an evar, the
   projection would have been reduced) *)

let check_conv_record (t1,l1) (t2,l2) =
  try
    let proji = Libnames.global_of_constr t1 in
    let canon_s,l2_effective =
      try
	match kind_of_term t2 with
	    Prod (_,a,b) -> (* assert (l2=[]); *)
      	      if Termops.dependent (mkRel 1) b then raise Not_found
	      else lookup_canonical_conversion (proji, Prod_cs),[a;Termops.pop b]
	  | Sort s ->
	      lookup_canonical_conversion
		(proji, Sort_cs (family_of_sort s)),[]
	  | _ ->
	      let c2 = Libnames.global_of_constr t2 in
		Recordops.lookup_canonical_conversion (proji, Const_cs c2),l2
      with Not_found ->
	lookup_canonical_conversion (proji, Default_cs),[]
    in
    let { o_DEF = c; o_INJ=n; o_TABS = bs;
          o_TPARAMS = params; o_NPARAMS = nparams; o_TCOMPS = us } = canon_s in
    let params1, c1, extra_args1 =
      match Util.list_chop nparams l1 with
	| params1, c1::extra_args1 -> params1, c1, extra_args1
	| _ -> raise Not_found in
    let us2,extra_args2 = Util.list_chop (List.length us) l2_effective in
    c,bs,(params,params1),(us,us2),(extra_args1,extra_args2),c1,
    (n,applist(t2,l2))
  with Failure _ | Not_found ->
    raise Not_found



(* pre: c and c' are in whdnf with our definition of whd *)
let rec unify ?(conv_t=Reduction.CONV) ts env sigma0 t t' =
  let t = Evarutil.whd_head_evar sigma0 t in
  let t' = Evarutil.whd_head_evar sigma0 t' in
  if Evarutil.is_ground_term sigma0 t && Evarutil.is_ground_term sigma0 t' 
    && Reductionops.is_trans_fconv conv_t ts env sigma0 t t' 
  then success sigma0
  else
    let (c, l as tapp) = decompose_app t in
    let (c', l' as tapp') = decompose_app t' in
    match (kind_of_term c, kind_of_term c') with
    | Evar _, _ 
    | _, Evar _ ->
      one_is_meta ts conv_t env sigma0 tapp tapp'

    (* Prop-Same, Set-Same, Type-Same *)
    | Sort s1, Sort s2 -> 
      begin
      try
	let sigma1 = match conv_t with
        | Reduction.CONV -> Evd.set_eq_sort sigma0 s1 s2 
        | _ -> Evd.set_leq_sort sigma0 s1 s2
        in (true, sigma1)
      with Univ.UniverseInconsistency _ -> err sigma0
      end
    (* Lam-Same *)
    | Lambda (name, t1, c1), Lambda (_, t2, c2) 
      when l = [] && l' = [] ->
      let env' = Environ.push_rel (name, None, t1) env in
      unify ts env sigma0 t1 t2 &&= fun sigma1 ->
      unify ts env' sigma1 c1 c2 &&= fun sigma2 ->
      success sigma2

    (* Prod-Same *)
    | Prod (name, t1, c1), Prod (_, t2, c2) ->
      unify ts env sigma0 t1 t2 &&= fun sigma1 ->
      unify ~conv_t ts (Environ.push_rel (name,None,t1) env) sigma1 c1 c2

    (* Let-Same *)
    | LetIn (name, trm1, ty1, body1), LetIn (_, trm2, ty2, body2) 
      when l = [] && l'= [] ->
      unify ts env sigma0 trm1 trm2 &&= fun sigma1 ->
      unify ~conv_t ts (Environ.push_rel (name, Some trm1, ty1) env) 
      sigma1 body1 body2

    (* Rigid-Same *)
    | Rel n1, Rel n2 when n1 = n2 && l = [] && l' = [] ->
      success sigma0
    | Var id1, Var id2 when id1 = id2 && l = [] && l' = [] -> 
      success sigma0
    | Const c1, Const c2 when Names.eq_constant c1 c2 && l = [] && l' = [] ->
      success sigma0
    | Ind c1, Ind c2 when Names.eq_ind c1 c2 && l = [] && l' = [] ->
      success sigma0
    | Construct c1, Construct c2 
      when Names.eq_constructor c1 c2 && l = [] && l' = []  ->
      success sigma0

    | CoFix (i1,(_,tys1,bds1 as recdef1)), CoFix (i2,(_,tys2,bds2))
      when i1 = i2 && l = [] && l' = [] ->
      ise_array2 sigma0 (fun i -> unify ts env i) tys1 tys2 &&= fun sigma1 ->
      ise_array2 sigma1 (fun i -> unify ts (Environ.push_rec_types recdef1 env) i) bds1 bds2

    | Case (_, p1, c1, cl1), Case (_, p2, c2, cl2) 
      when l = [] && l' = [] ->
      (
	unify ts env sigma0 p1 p2 &&= fun sigma1 ->
	unify ts env sigma1 c1 c2 &&= fun sigma2 ->
	ise_array2 sigma2 (fun i -> unify ts env i) cl1 cl2
      ) 
      ||= fun _ ->
	reduce_iota_and_unify ts env sigma0 tapp tapp'

    | Fix (li1, (_, tys1, bds1 as recdef1)), Fix (li2, (_, tys2, bds2)) 
      when li1 = li2 && l = [] && l' = [] ->
      ise_array2 sigma0 (fun i -> unify ts env i) tys1 tys2 &&= fun sigma1 ->
      ise_array2 sigma1 (fun i -> unify ts (Environ.push_rec_types recdef1 env) i) bds1 bds2

    | _, _  ->
      (
	if (isConst c || isConst c') && not (eq_constr c c') then
	  try conv_record ts env sigma0 tapp tapp'
	  with Not_found ->
	    try conv_record ts env sigma0 tapp' tapp
	    with Not_found -> err sigma0
	else
	  err sigma0
      ) ||= fun _ ->
      (
	let n = List.length l in
	let m = List.length l' in
	if n = m && n > 0 then
	  unify ~conv_t ts env sigma0 c c' &&= fun sigma1 ->
          ise_list2 sigma1 (fun i -> unify ts env i) l l'
	else
	  err sigma0
      ) ||= fun _ ->
      (
	try_step conv_t ts env sigma0 tapp tapp'
      )

and one_is_meta ts conv_t env sigma0 (c, l as t) (c', l' as t') =
  if isEvar c && isEvar c' then
    let (k1, s1 as e1), (k2, s2 as e2) = destEvar c, destEvar c' in
    if k1 = k2 then
      (* Meta-Same *)
      unify_same env sigma0 k1 s1 s2 &&= fun sigma1 ->
      ise_list2 sigma1 (fun i -> unify ts env i) l l'
    else
      (* Meta-Meta *)
      if k1 > k2 then
	instantiate ts conv_t env sigma0 e1 l t' ||= fun _ ->
	instantiate ts conv_t env sigma0 e2 l' t
      else
	instantiate ts conv_t env sigma0 e2 l' t ||= fun _ ->
	instantiate ts conv_t env sigma0 e1 l t'
  else
    (* Meta-InstL *)
    if isEvar c then
      let e1 = destEvar c in
      instantiate ts conv_t env sigma0 e1 l t'
    else
      (* Meta-InstR *)
      let e2 = destEvar c' in
      instantiate ts conv_t env sigma0 e2 l' t 

and try_step conv_t ts env sigma0 (c, l as t) (c', l' as t') =
  match (kind_of_term c, kind_of_term c') with
  (* Lam-BetaL *)
  | Lambda (_, _, trm), _ when l <> [] ->
    let t1 = applist (subst1 (List.hd l) trm, List.tl l) in
    let t2 = applist t' in
    unify ~conv_t ts env sigma0 t1 t2

  (* Lam-BetaR *)
  | _, Lambda (_, _, trm) when l' <> [] ->
    let t1 = applist t in
    let t2 = applist (subst1 (List.hd l') trm, List.tl l') in
    unify ~conv_t ts env sigma0 t1 t2 

  (* Let-ZetaL *)
  | LetIn (_, trm, _, body), _ ->
    let t1 = applist (subst1 trm body, l) in
    let t2 = applist t' in
    unify ~conv_t ts env sigma0 t1 t2

  (* Let-ZetaR *)
  | _, LetIn (_, trm, _, body) ->
    let t1 = applist t in
    let t2 = applist (subst1 trm body, l') in
    unify ~conv_t ts env sigma0 t1 t2

  (* Rigid-Same-Delta *)	    
  | Rel n1, Rel n2 when n1 = n2 ->
      eq_rigid ts env sigma0 n1 l l' (unify ~conv_t) rel_is_def rel_value
  | Var id1, Var id2 when id1 = id2 -> 
      eq_rigid ts env sigma0 id1 l l' (unify ~conv_t) var_is_def var_value
  | Const c1, Const c2 when Names.eq_constant c1 c2 ->
      eq_rigid ts env sigma0 c1 l l' (unify ~conv_t) const_is_def const_value

  (* Rigid-DeltaL *)
  | Rel n1, _ when rel_is_def ts env n1 ->
      transp_matchL ts env sigma0 n1 l (applist t') (unify ~conv_t) rel_value
  | Var id1, _ when var_is_def ts env id1 ->
      transp_matchL ts env sigma0 id1 l (applist t') (unify ~conv_t) var_value
  | Const c1, _ when const_is_def ts env c1 ->
      transp_matchL ts env sigma0 c1 l (applist t') (unify ~conv_t) const_value

  (* Rigid-DeltaR *)
  | _, Rel n2 when rel_is_def ts env n2 ->
      transp_matchR ts env sigma0 n2 l' (applist t) (unify ~conv_t) rel_value
  | _, Var id2 when var_is_def ts env id2 ->
      transp_matchR ts env sigma0 id2 l' (applist t) (unify ~conv_t) var_value
  | _, Const c2 when const_is_def ts env c2 ->
      transp_matchR ts env sigma0 c2 l' (applist t) (unify ~conv_t) const_value
(*      
  (* Lam-EtaL *)
  | Lambda (name, t1, c1), _ when l = [] ->
      eta_match ts env sigma0 (name, t1, c1) t'
  (* Lam-EtaR *)
  | _, Lambda (name, t1, c1) when l' = [] ->
      eta_match ts env sigma0 (name, t1, c1) t
*)
  | _, _ -> reduce_iota_and_unify ts env sigma0 t t'

and reduce_iota_and_unify ts env sigma (_, l1 as t1) (_, l2 as t2) =
  let t1, t2 = applist t1, applist t2 in
  let t1' = Reductionops.whd_betadeltaiota env sigma t1 in
  let t2' = Reductionops.whd_betadeltaiota env sigma t2 in
  if t1 <> t1' || t2 <> t2' then
    unify ts env sigma t1' t2'
  else err sigma

and instantiate' ts conv_t env sigma0 (ev, subs as uv) args (h, args' as t) =
  let evi = Evd.find_undefined sigma0 ev in
  let nc = Evd.evar_filtered_context evi in
  let res = 
    let t = applist t in
    let subsl = Array.to_list subs in
    invert nc (Reductionops.nf_evar sigma0 t) subsl args >>= fun t' ->
    let t' = fill_lambdas env sigma0 args t' in
    let t'' = Evd.instantiate_evar nc t' subsl in
    let ty' = Retyping.get_type_of env sigma0 t'' in
    let ty = Evd.existential_type sigma0 uv in
    Some (
      unify ~conv_t:Reduction.CUMUL ts env sigma0 ty' ty &&= fun sigma2 ->
	let t' = Reductionops.nf_evar sigma2 t' in
	if Termops.occur_meta t' then 
	  (Printf.printf "hay meta" ; err sigma2)
	else if Termops.occur_evar ev t' then
	  (Printf.printf "hay ciclo" ; err sigma2)
	else
	  (* needed only if an inferred type *)
	  let t' = Termops.refresh_universes t' in
	  success (Evd.define ev t' sigma2))
  in
  match res with
  | Some r -> r (* Meta-Inst *)
  | None -> 
    (* Meta-Reduce: before giving up we see if we can reduce on the right *)
    let t = applist t in
    let t' = Reductionops.nf_betadeltaiota env sigma0 t in
    if t <> t' then
      begin
        let ev = mkEvar uv in
        unify ~conv_t ts env sigma0 ev t'
      end
    else err sigma0

(* by invariant, we know that ev is uninstantiated *)
and instantiate ts conv_t env sigma 
    (ev, subs as evsubs) args (h, args' as t) =
  if is_variable_subs subs then
    if is_variable_args args then
      instantiate' ts conv_t env sigma evsubs args t
    else 
      if should_try_fo args (h, args') then
	(* Meta-FO *)
	meta_fo ts env sigma (evsubs, args) (h, args')
      else
	err sigma
  else
    err sigma
    
and should_try_fo args (h, args') =
  List.length args' >= List.length args

and meta_fo ts env sigma (evsubs, args) (h, args') =
  let arr = Array.of_list args in
  let arr' = Array.of_list args' in
  unify ts env sigma (mkEvar evsubs)  
    (mkApp (h, (Array.sub arr' 0 (Array.length arr' - Array.length arr)))) 
  &&= fun sigma' ->
  ise_array2 sigma' (fun i -> unify ts env i) arr arr'


(* unifies ty with a product type from {name : a} to some Type *)
and check_product ts env sigma ty (name, a) =
  let nc = Environ.named_context env in
  let naid = Namegen.next_name_away name (Termops.ids_of_named_context nc) in
  let nc' = (naid, None, a) :: nc in
  let v = Evarutil.new_untyped_evar () in
  let sigma', univ = Evd.new_univ_variable sigma in
  let evi = Evd.make_evar (Environ.val_of_named_context nc') (mkType univ) in 
  let sigma'' = Evd.add sigma' v evi in
  let idsubst = Array.append [| mkRel 1 |] (id_substitution nc) in
  unify ts env sigma'' ty (mkProd (Names.Name naid, a, mkEvar(v, idsubst)))

and eta_match ts env sigma0 (name, a, t1) (th, tl as t) =
  let env' = Environ.push_rel (name, None, a) env in
  let ty = Retyping.get_type_of env sigma0 (applist t) in
  let t' = applist (lift 1 th, List.map (lift 1) tl @ [mkRel 1]) in
  check_product ts env sigma0 ty (name, a) &&= fun sigma1 ->
  unify ts env' sigma1 t1 t'

and conv_record trs env evd t t' =
  let (c,bs,(params,params1),(us,us2),(ts,ts1),c1,(n,t2)) = check_conv_record t t' in
  let (evd',ks,_) =
    List.fold_left
      (fun (i,ks,m) b ->
	 if m=n then (i,t2::ks, m-1) else
	 let dloc = (Util.dummy_loc, Evd.InternalHole) in
         let (i',ev) = Evarutil.new_evar i env ~src:dloc (substl ks b) in
	 (i', ev :: ks, m - 1))
      (evd,[],List.length bs - 1) bs
  in
  ise_list2 evd' (fun i x1 x -> unify trs env i x1 (substl ks x))
    params1 params &&= fun i ->
  ise_list2 i (fun i u1 u -> unify trs env i u1 (substl ks u))
    us2 us &&= fun i -> 
  unify trs env i c1 (applist (c,(List.rev ks))) &&= fun i ->
  ise_list2 i (fun i -> unify trs env i) ts ts1

let swap (a, b) = (b, a) 

let unify_evar_conv ?(conv_t=Reduction.CONV) ts env sigma0 t t' =
  swap (unify ~conv_t:conv_t ts env sigma0 t t')
