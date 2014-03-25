open Term
open Recordops

let debug = ref false

let set_debug b = debug := b

let get_debug () = !debug

let (>>=) opt f = 
  match opt with
  | Some(x) -> f x
  | None -> None
   
let return x = Some x

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

let eq_rigid ts env sigma c l1 l2 unif get_value =
  let v = get_value env c in 
  unif ts env sigma (applist (v, l1)) (applist (v, l2))
	
let transp_matchL ts env sigma c l t unif get_value =
  let v = get_value env c
  in unif ts env sigma (applist (v, l)) t
    
let transp_matchR ts env sigma c l t unif get_value =
  let v = get_value env c
  in unif ts env sigma t (applist (v, l))

exception Unfoldable
let unfold_value ts env sigma c =
  if isVar c && var_is_def ts env (destVar c) then
    var_value env (destVar c)
  else if isRel c && rel_is_def ts env (destRel c) then
    rel_value env (destRel c)
  else if isConst c && const_is_def ts env (destConst c) then
    const_value env (destConst c)
  else
    raise Unfoldable

let (-.) n m =
  if n > m then n - m
  else 0

(* pre: |ctx| = |subs| and subs and args are both a list of vars or rels.
   ctx is the (named) context of the evar
   t is the term to invert
   subs is the substitution of the evar
   args are the arguments of the evar
   map is an Intmap mapping evars with list of positions.
   Given a problem of the form
     ?e[subs] args = t
   this function returns t' equal to t, except that every free
   variable (or rel) x in t is replaced by
   - If x appears (uniquely) in subs, then x is replaced by Var n, where
     n is the name of the variable in ctx in the position where x was
     found in s.
   - If x appears (uniquely) in args, then x is replaced by Rel j, were
     j is the position of x in args.
   As a side effect, it populates the map with evars that sould be prunned.
   Prunning is needed to avoid failing when there is hope: the unification 
   problem
     ?e[x] = ?e'[x, z]
   is solvable if we prune z from ?e'.  However, this is not the case in the 
   following example:
     ?e[x] = ?e'[x, ?e''[z]]
   The problem lies on the two different options: we can either prune the 
   second element of the substitution of ?e', or we can prune the one element 
   in the substitution of ?e''.  To make the distinction, we use a boolean 
   parameter [inside_evar] to mark that we should fail instead of prunning.
  
   Finally, note in the example above that we can also try instantiating ?e' 
   with ?e instead of the other way round, and this is in fact tried by the
   unification algorithm.
*)
let invert map ctx t subs args = 
  let sargs = subs @ args in
  let in_subs j = j < List.length ctx in
  let rec invert' inside_evar t i =
    match kind_of_term t with
      | Var id -> 
	find_unique_var id sargs >>= fun j -> 
	if in_subs j then
	  let (name, _, _) = List.nth ctx j in
	  return (mkVar name)
	else
	  return (mkRel (List.length sargs - j))
      | Rel j when j > i-> 
	find_unique_rel (j-i) sargs >>= fun k -> 
	if in_subs k then
	  let (name, _, _) = List.nth ctx k in
	  return (mkVar name)
	else
	  return (mkRel (List.length sargs - k + i))
            
      | Evar (ev, evargs) ->
	begin
	  let f (j : int) c  = 
            match invert' true c i with
              | Some c' -> c'
              | _ -> 
		if (not inside_evar) && (isVar c || isRel c) then
		  begin
		    (if not (Util.Intmap.mem ev !map) then
			map := Util.Intmap.add ev [j] !map
		     else
			map := Util.Intmap.add ev (j :: Util.Intmap.find ev !map) !map)
                    ; c
		  end
		else
		  raise Exit
	  in
	  try return (mkEvar (ev, Array.mapi f evargs))
	  with Exit -> None
	end
      | _ -> 
	try return (map_constr_with_binders succ (fun i c -> 
	  match invert' inside_evar c i with
	    | Some c' -> c'
	    | None -> raise Exit) i t)
	with Exit -> None
  in
  invert' false t 0 >>= fun c' ->
  return c'

(** removes the positions in the list *)
let remove l pos =
  let rec remove' i l =
    match l with
      | [] -> []
      | (x :: s) -> 
        if List.mem i pos then
          remove' (i+1) s
        else
          (x :: remove' (i+1) s)
  in remove' 0 l

let collect_vars =
  let rec aux vars c = match kind_of_term c with
  | Var id -> Names.Idset.add id vars
  | _ -> fold_constr aux vars c in
  aux Names.Idset.empty

let free_vars_in tm vars = 
  Names.Idset.for_all (fun v -> List.mem v vars) (collect_vars tm)

exception CannotPrune
(** ev is the evar and plist the indices to prune.  from ?ev : T[env]
    it creates a new evar ?ev' with a shorter context env' such that
    ?ev := ?ev'[id_env']. If the prunning is unsuccessful, it throws
    the exception CannotPrune. *)
let prune evd (ev, plist) =
  let evi = Evd.find_undefined evd ev in
  let env = Evd.evar_filtered_context evi in
  let env' = remove env plist in
  let env_val' = (List.fold_right Environ.push_named_context_val env' 
                    Environ.empty_named_context_val) in
  let concl = Reductionops.nf_evar evd (Evd.evar_concl evi) in
  if free_vars_in concl (Termops.ids_of_named_context env') then
    let evd', ev' = Evarutil.new_evar_instance env_val' evd 
      concl (Array.to_list (id_substitution env')) in
    Evd.define ev ev' evd'
  else raise CannotPrune

let prune_all map evd =
  List.fold_left prune evd (Util.Intmap.bindings map)

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
  | Some l -> begin
              try 
		success (prune sigma (ev, l))
              with CannotPrune -> err sigma
              end
  | _ -> err sigma



(* given a list of arguments [x1 .. xn] with types [A1 .. An] and a
   [body] with free indices [1 .. n], it returns [fun x1 : A1^-1 => .. =>
   fun xn : An^-1 => body].
*)
let fill_lambdas_invert_types map env sigma nc body subst args =
  List.fold_right (fun arg bdy-> bdy >>= fun bdy ->
    let ty = Retyping.get_type_of env sigma arg in
    invert map nc ty subst args >>= fun ty ->
    return (mkLambda (Names.Anonymous, ty, bdy))) args (return body)

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

let run_function = ref (fun _ _ _ -> None)
let set_run f = run_function := f

let lift_constr = ref (lazy mkProp)
let set_lift_constr c = lift_constr := c

let is_lift c = 
  try eq_constr c (Lazy.force !lift_constr)
  with Not_found -> false


let rec pad l = if l <= 0 then () else (Printf.printf "_"; pad (l-1))

let print_bar l = if l > 0 then Printf.printf "%s" "|" else ()
    
let debug_str s l =
  if !debug then 
    begin
      print_bar l;
      Printf.printf "%s\n" s
    end
  else
    ()

let debug_eq env c1 c2 l = 
  if !debug then 
    begin
      print_bar l;
      pad l;
      Pp.msg (Termops.print_constr c1);
      Printf.printf "%s" " =?= ";
      Pp.msg (Termops.print_constr c2);
      Printf.printf "\n" 
    end
  else
    ()
  
type stucked = NotStucked | StuckedLeft | StuckedRight

(* pre: c and c' are in whdnf with our definition of whd *)
let rec unify' ?(conv_t=Reduction.CONV) dbg ts env sigma0 t t' =
  let t = Evarutil.whd_head_evar sigma0 t in
  let t' = Evarutil.whd_head_evar sigma0 t' in
  debug_eq env t t' dbg;
  if Evarutil.is_ground_term sigma0 t && Evarutil.is_ground_term sigma0 t' 
    && Reductionops.is_trans_fconv conv_t ts env sigma0 t t' 
  then success sigma0
  else
    let (c, l as tapp) = decompose_app t in
    let (c', l' as tapp') = decompose_app t' in
    match (kind_of_term c, kind_of_term c') with
    | Evar _, _ 
    | _, Evar _ ->
      one_is_meta dbg ts conv_t env sigma0 tapp tapp'

    (* Prop-Same, Set-Same, Type-Same, Type-Same-LE *)
    | Sort s1, Sort s2 -> 
      begin
      try
	let sigma1 = match conv_t with
        | Reduction.CONV -> Evd.set_eq_sort sigma0 s1 s2 
        | _ -> Evd.set_leq_sort sigma0 s1 s2
        in (true, sigma1)
      with _ -> err sigma0 
      end

    (* Lam-Same *)
    | Lambda (name, t1, c1), Lambda (_, t2, c2) 
      when l = [] && l' = [] ->
      let env' = Environ.push_rel (name, None, t1) env in
      unify' (dbg+1) ts env sigma0 t1 t2 &&= fun sigma1 ->
      unify' ~conv_t (dbg+1) ts env' sigma1 c1 c2 &&= fun sigma2 ->
      success sigma2

    (* Prod-Same *)
    | Prod (name, t1, c1), Prod (_, t2, c2) ->
      unify' (dbg+1) ts env sigma0 t1 t2 &&= fun sigma1 ->
      unify' ~conv_t (dbg+1) ts (Environ.push_rel (name,None,t1) env) sigma1 c1 c2

    (* Let-Same *)
    | LetIn (name, trm1, ty1, body1), LetIn (_, trm2, ty2, body2) 
      when l = [] && l'= [] ->
      (
        let env' = Environ.push_rel (name, Some trm1, ty1) env in
        unify' (dbg+1) ts env sigma0 trm1 trm2 &&= fun sigma1 ->
        unify' ~conv_t (dbg+1) ts env' sigma1 body1 body2
      ) ||= (fun _ ->
          let body1 = subst1 trm1 body1 in
          let body2 = subst1 trm2 body2 in
        unify' ~conv_t (dbg+1) ts env sigma0 body1 body2
      )

(* ALREADY CONSIDERED IN THE CONV RULE! 
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
*)

    | CoFix (i1,(_,tys1,bds1 as recdef1)), CoFix (i2,(_,tys2,bds2))
      when i1 = i2 && l = [] && l' = [] ->
      ise_array2 sigma0 (fun i -> unify' (dbg+1) ts env i) tys1 tys2 &&= fun sigma1 ->
      ise_array2 sigma1 (fun i -> unify' (dbg+1) ts (Environ.push_rec_types recdef1 env) i) bds1 bds2

    | Case (_, p1, c1, cl1), Case (_, p2, c2, cl2) 
      when l = [] && l' = [] ->
      (
	unify' (dbg+1) ts env sigma0 p1 p2 &&= fun sigma1 ->
	unify' (dbg+1) ts env sigma1 c1 c2 &&= fun sigma2 ->
	ise_array2 sigma2 (fun i -> unify' (dbg+1) ts env i) cl1 cl2
      ) 
      ||= fun _ ->
	reduce_and_unify dbg ts env sigma0 tapp tapp'

    | Fix (li1, (_, tys1, bds1 as recdef1)), Fix (li2, (_, tys2, bds2)) 
      when li1 = li2 && l = [] && l' = [] ->
      ise_array2 sigma0 (fun i -> unify' (dbg+1) ts env i) tys1 tys2 &&= fun sigma1 ->
      ise_array2 sigma1 (fun i -> unify' (dbg+1) ts (Environ.push_rec_types recdef1 env) i) bds1 bds2

    | _, _  ->
      (
	if (isConst c || isConst c') && not (eq_constr c c') then
         if is_lift c && List.length l = 3 then
           run_and_unify dbg ts env sigma0 l (applist tapp')
         else if is_lift c' && List.length l' = 3 then
           run_and_unify dbg ts env sigma0 l' (applist tapp)
         else
           err sigma0
       else
         err sigma0
      ) ||= fun _ ->
      (
       if (isConst c || isConst c') && not (eq_constr c c') then
	  try conv_record dbg ts env sigma0 tapp tapp'
	  with Not_found ->
	    try conv_record dbg ts env sigma0 tapp' tapp
	    with Not_found -> err sigma0
	else
	  err sigma0
      ) ||= fun _ ->
      (
	let n = List.length l in
	let m = List.length l' in
	if n = m && n > 0 then
	  unify' ~conv_t (dbg+1) ts env sigma0 c c' &&= fun sigma1 ->
          ise_list2 sigma1 (fun i -> unify' (dbg+1) ts env i) l l'
	else
	  err sigma0
      ) ||= fun _ ->
      (
	try_step dbg conv_t ts env sigma0 tapp tapp'
      )

and run_and_unify dbg ts env sigma0 args ty =
  let a, f, v = List.nth args 0, List.nth args 1, List.nth args 2 in
  unify' ~conv_t:Reduction.CUMUL (dbg+1) ts env sigma0 a ty &&= fun sigma1 ->
  match !run_function env sigma1 f with
  | Some (sigma2, v') -> unify' (dbg+1) ts env sigma2 v v'
  | _ -> err sigma0

and one_is_meta dbg ts conv_t env sigma0 (c, l as t) (c', l' as t') =
  if isEvar c && isEvar c' then
    let (k1, s1 as e1), (k2, s2 as e2) = destEvar c, destEvar c' in
    if k1 = k2 then
      (* Meta-Same *)
      unify_same env sigma0 k1 s1 s2 &&= fun sigma1 ->
      ise_list2 sigma1 (fun i -> unify' (dbg+1) ts env i) l l'
    else
      (* Meta-Meta *)
      if k1 > k2 then
	instantiate dbg ts conv_t env sigma0 e1 l t' ||= fun _ ->
	instantiate dbg ts conv_t env sigma0 e2 l' t
      else
	instantiate dbg ts conv_t env sigma0 e2 l' t ||= fun _ ->
	instantiate dbg ts conv_t env sigma0 e1 l t'
  else
    if isEvar c then
      if is_lift c' && List.length l' = 3 then
        run_and_unify dbg ts env sigma0 l' (applist t)
      else
	(* Meta-InstL *)
	let e1 = destEvar c in
	instantiate dbg ts conv_t env sigma0 e1 l t'
    else
      if is_lift c && List.length l = 3 then
        run_and_unify dbg ts env sigma0 l (applist t')
      else
        (* Meta-InstR *)
	let e2 = destEvar c' in
	instantiate dbg ts conv_t env sigma0 e2 l' t 

and try_step ?(stuck=NotStucked) dbg conv_t ts env sigma0 (c, l as t) (c', l' as t') =
  match (kind_of_term c, kind_of_term c') with
  (* Lam-BetaR *)
  | _, Lambda (_, _, trm) when l' <> [] ->
    let t1 = applist t in
    let t2 = applist (subst1 (List.hd l') trm, List.tl l') in
    unify' ~conv_t (dbg+1) ts env sigma0 t1 t2 
  (* Lam-BetaL *)
  | Lambda (_, _, trm), _ when l <> [] ->
    let t1 = applist (subst1 (List.hd l) trm, List.tl l) in
    let t2 = applist t' in
    unify' ~conv_t (dbg+1) ts env sigma0 t1 t2

  (* Let-ZetaR *)
  | _, LetIn (_, trm, _, body) ->
    let t1 = applist t in
    let t2 = applist (subst1 trm body, l') in
    unify' ~conv_t (dbg+1) ts env sigma0 t1 t2
  (* Let-ZetaL *)
  | LetIn (_, trm, _, body), _ ->
    let t1 = applist (subst1 trm body, l) in
    let t2 = applist t' in
    unify' ~conv_t (dbg+1) ts env sigma0 t1 t2

  (* Rigid-Same-Delta *)	    
  | Rel n1, Rel n2 when n1 = n2 && rel_is_def ts env n1 ->
      eq_rigid ts env sigma0 n1 l l' (unify' ~conv_t (dbg+1)) rel_value
  | Var id1, Var id2 when id1 = id2 && var_is_def ts env id1 -> 
      eq_rigid ts env sigma0 id1 l l' (unify' ~conv_t (dbg+1)) var_value
  | Const c1, Const c2 when Names.eq_constant c1 c2 && const_is_def ts env c1 ->
      eq_rigid ts env sigma0 c1 l l' (unify' ~conv_t (dbg+1)) const_value

  (* Rigid-DeltaR *)
  | _, Rel n2 when rel_is_def ts env n2 ->
      transp_matchR ts env sigma0 n2 l' (applist t) (unify' ~conv_t (dbg+1)) rel_value
  | _, Var id2 when var_is_def ts env id2 ->
      transp_matchR ts env sigma0 id2 l' (applist t) (unify' ~conv_t (dbg+1)) var_value
  (* Rigid-DeltaL *)
  | Rel n1, _ when rel_is_def ts env n1 ->
      transp_matchL ts env sigma0 n1 l (applist t') (unify' ~conv_t (dbg+1)) rel_value
  | Var id1, _ when var_is_def ts env id1 ->
      transp_matchL ts env sigma0 id1 l (applist t') (unify' ~conv_t (dbg+1)) var_value

  | _, Case _ | _, Fix _ when stuck <> StuckedRight ->
    let t'' = applist t' in
    let t2 = Reductionops.whd_betadeltaiota env sigma0 t'' in
    if t'' <> t2 then
      (* WhdR *)
      unify' ~conv_t (dbg+1) ts env sigma0 (applist t) t2
    else if stuck = NotStucked then
      try_step ~stuck:StuckedRight dbg conv_t ts env sigma0 t t'
    else err sigma0

  | Case _, _ | Fix _, _ when stuck <> StuckedLeft ->
    let t'' = applist t in
    let t2 = Reductionops.whd_betadeltaiota env sigma0 t'' in
    if t'' <> t2 then
      (* WhdL *)
      unify' ~conv_t (dbg+1) ts env sigma0 t2 (applist t')
    else if stuck = NotStucked then
      try_step ~stuck:StuckedLeft dbg conv_t ts env sigma0 t t'
    else err sigma0

  (* Constants get unfolded after everything else *)
  | _, Const c2 when const_is_def ts env c2 && stuck = NotStucked ->
      if Recordops.is_canonical_projector (Libnames.global_of_constr c') then
	try_step ~stuck:StuckedRight dbg conv_t ts env sigma0 t t'
      else
	transp_matchR ts env sigma0 c2 l' (applist t) (unify' ~conv_t (dbg+1)) const_value
  | Const c1, _ when const_is_def ts env c1 && stuck = NotStucked ->
      if Recordops.is_canonical_projector (Libnames.global_of_constr c) then
	try_step ~stuck:StuckedLeft dbg conv_t ts env sigma0 t t'
      else
	transp_matchL ts env sigma0 c1 l (applist t') (unify' ~conv_t (dbg+1)) const_value
  | _, Const c2 when const_is_def ts env c2 && stuck = StuckedLeft ->
      transp_matchR ts env sigma0 c2 l' (applist t) (unify' ~conv_t (dbg+1)) const_value
  | Const c1, _ when const_is_def ts env c1 && stuck = StuckedRight ->
      transp_matchL ts env sigma0 c1 l (applist t') (unify' ~conv_t (dbg+1)) const_value

  | _, Const c2 when const_is_def ts env c2 ->
      transp_matchR ts env sigma0 c2 l' (applist t) (unify' ~conv_t (dbg+1)) const_value
  | Const c1, _ when const_is_def ts env c1 ->
      transp_matchL ts env sigma0 c1 l (applist t') (unify' ~conv_t (dbg+1)) const_value

(*      
  (* Lam-EtaL *)
  | Lambda (name, t1, c1), _ when l = [] ->
      eta_match ts env sigma0 (name, t1, c1) t'
  (* Lam-EtaR *)
  | _, Lambda (name, t1, c1) when l' = [] ->
      eta_match ts env sigma0 (name, t1, c1) t
*)
  | _, _ -> err sigma0 (* reduce_and_unify dbg ts env sigma0 t t' *)

and reduce_and_unify dbg ts env sigma t t' =
  let t, t' = applist t, applist t' in
  let t2 = Reductionops.whd_betadeltaiota env sigma t' in
  if t' <> t2 then
    (* WhdR *)
    unify' (dbg+1) ts env sigma t t2
  else
    let t1 = Reductionops.whd_betadeltaiota env sigma t in
    if t <> t1 then
      (* WhdL *)
      unify' (dbg+1) ts env sigma t1 t'
    else
      err sigma

and instantiate' dbg ts conv_t env sigma0 (ev, subs as uv) args (h, args' as t) =
  let evi = Evd.find_undefined sigma0 ev in
  let nc = Evd.evar_filtered_context evi in
  let res = 
    let t = applist t in
    let subsl = Array.to_list subs in
    let map = ref Util.Intmap.empty in
    invert map nc (Reductionops.nf_evar sigma0 t) subsl args >>= fun t' ->
    fill_lambdas_invert_types map env sigma0 nc t' subsl args >>= fun t' ->
    let sigma1 = prune_all !map sigma0 in
    let t'' = Evd.instantiate_evar nc t' subsl in
    let ty' = Retyping.get_type_of env sigma1 t'' in
    let ty = Evd.existential_type sigma1 uv in
    let p = unify' (dbg+1) ~conv_t:Reduction.CUMUL ts env sigma1 ty' ty &&= fun sigma2 ->
      let t' = Reductionops.nf_evar sigma2 t' in
      if Termops.occur_meta t' || Termops.occur_evar ev t' then 
	err sigma2
      else
        (* needed only if an inferred type *)
	let t' = Termops.refresh_universes t' in
	success (Evd.define ev t' sigma2)
    in
    Some p
  in 
  match res with
    | Some r -> r
    | None -> 
        if should_try_fo args t then
  	  (* Meta-FO *)
	  meta_fo dbg ts env sigma0 (uv, args) t
        else
	  err sigma0

(*
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
        let r = unify' ~conv_t ts env sigma0 ev t' in
	Printf.println "reducing help";
	r
      end
    else err sigma0
      *)
(* by invariant, we know that ev is uninstantiated *)
and instantiate dbg ts conv_t env sigma 
    (ev, subs as evsubs) args (h, args' as t) =
  if is_variable_subs subs then
    if is_variable_args args then
      try 
	instantiate' dbg ts conv_t env sigma evsubs args t
      with CannotPrune -> err sigma
    else 
      if should_try_fo args (h, args') then
	(* Meta-FO *)
	meta_fo dbg ts env sigma (evsubs, args) (h, args')
      else
	err sigma
  else
    err sigma
    
and should_try_fo args (h, args') = false
  (* List.length args' >= List.length args *)

and meta_fo dbg ts env sigma (evsubs, args) (h, args') =
  let arr = Array.of_list args in
  let arr' = Array.of_list args' in
  unify' (dbg+1) ts env sigma (mkEvar evsubs)  
    (mkApp (h, (Array.sub arr' 0 (Array.length arr' - Array.length arr)))) 
  &&= fun sigma' ->
  ise_array2 sigma' (fun i -> unify' (dbg+1) ts env i) arr arr'


(* unifies ty with a product type from {name : a} to some Type *)
(*
and check_product ts env sigma ty (name, a) =
  let nc = Environ.named_context env in
  let naid = Namegen.next_name_away name (Termops.ids_of_named_context nc) in
  let nc' = (naid, None, a) :: nc in
  let v = Evarutil.new_untyped_evar () in
  let sigma', univ = Evd.new_univ_variable sigma in
  let evi = Evd.make_evar (Environ.val_of_named_context nc') (mkType univ) in 
  let sigma'' = Evd.add sigma' v evi in
  let idsubst = Array.append [| mkRel 1 |] (id_substitution nc) in
  unify' ts env sigma'' ty (mkProd (Names.Name naid, a, mkEvar(v, idsubst)))
*)
(*
and eta_match ts env sigma0 (name, a, t1) (th, tl as t) =
  let env' = Environ.push_rel (name, None, a) env in
  let ty = Retyping.get_type_of env sigma0 (applist t) in
  let t' = applist (lift 1 th, List.map (lift 1) tl @ [mkRel 1]) in
  check_product ts env sigma0 ty (name, a) &&= fun sigma1 ->
  unify' ts env' sigma1 t1 t'
*)
and conv_record dbg trs env evd t t' =
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
  ise_list2 evd' (fun i x1 x -> unify' (dbg+1) trs env i x1 (substl ks x))
    params1 params &&= fun i ->
  ise_list2 i (fun i u1 u -> unify' (dbg+1) trs env i u1 (substl ks u))
    us2 us &&= fun i -> 
  unify' (dbg+1) trs env i c1 (applist (c,(List.rev ks))) &&= fun i ->
  ise_list2 i (fun i -> unify' (dbg+1) trs env i) ts ts1

let unify ?(conv_t=Reduction.CONV) = unify' ~conv_t:conv_t 0

let swap (a, b) = (b, a) 

let unify_evar_conv ?(conv_t=Reduction.CONV) ts env sigma0 t t' =
  swap (unify ~conv_t:conv_t ts env sigma0 t t')
