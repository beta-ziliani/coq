open Term
open Recordops

let debug = ref false
let munify_on = ref true
let aggressive = ref true
let hash = ref false
let try_solving_eqn = ref false

let use_munify () = !munify_on
let set_use_munify b = munify_on := b

let set_debug b = debug := b
let get_debug () = !debug

let is_aggressive () = !aggressive
let set_aggressive b = aggressive := b

let set_hash b = hash := b
let use_hash () = !hash

let set_solving_eqn b = try_solving_eqn := b
let get_solving_eqn () = !try_solving_eqn

let _ = Goptions.declare_bool_option {
  Goptions.optsync = true; 
  Goptions.optdepr = false;
  Goptions.optname = "Enable use of new unification algorithm";
  Goptions.optkey = ["Use";"Munify"];
  Goptions.optread = use_munify;
  Goptions.optwrite = set_use_munify;
}

let _ = Goptions.declare_bool_option {
  Goptions.optsync  = true;
  Goptions.optdepr  = false;
  Goptions.optname  = "Debugging for unification";
  Goptions.optkey   = ["Munify";"Debug"];
  Goptions.optread  = get_debug;
  Goptions.optwrite = set_debug 
}

let _ = Goptions.declare_bool_option {
  Goptions.optsync = true; 
  Goptions.optdepr = false;
  Goptions.optname = "Enable more aggressive prunning";
  Goptions.optkey = ["Aggressive"];
  Goptions.optread = is_aggressive;
  Goptions.optwrite = set_aggressive;
}

let _ = Goptions.declare_bool_option {
  Goptions.optsync = true; 
  Goptions.optdepr = false;
  Goptions.optname = "Use a hash table of failures";
  Goptions.optkey = ["Use";"Hash"];
  Goptions.optread = use_hash;
  Goptions.optwrite = set_hash;
}

let _ = Goptions.declare_bool_option {
  Goptions.optsync  = true;
  Goptions.optdepr  = false;
  Goptions.optname  = "Try using original algorithm to solve equations ?x = t";
  Goptions.optkey   = ["Try"; "Solving";"Eqn"];
  Goptions.optread  = get_solving_eqn;
  Goptions.optwrite = set_solving_eqn 
}


(*** HACK ***)
(* Shouldn't be a boolean option! *)
let stat_unif_problems = ref Big_int.zero_big_int
let stat_solve_simple_eqn = ref Big_int.zero_big_int

let _ = Goptions.declare_bool_option {
  Goptions.optsync  = false;
  Goptions.optdepr  = false;
  Goptions.optname  = "Print stats";
  Goptions.optkey   = ["Print";"Stats"];
  Goptions.optread  = (fun _ -> false);
  Goptions.optwrite = (fun _ -> 
    Printf.printf "STATS:\t%s\t\t%s\n" 
      (Big_int.string_of_big_int !stat_unif_problems) 
      (Big_int.string_of_big_int !stat_solve_simple_eqn))
}


let evarconv_for_cs = ref true
let get_evarconv_for_cs = fun _ -> !evarconv_for_cs

let _ = Goptions.declare_bool_option {
  Goptions.optsync  = false;
  Goptions.optdepr  = false;
  Goptions.optname  = "Use Evarconv for CS";
  Goptions.optkey   = ["Use";"Evarconv";"For";"CS"];
  Goptions.optread  = get_evarconv_for_cs;
  Goptions.optwrite = fun b -> evarconv_for_cs := b 
}


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

let is_success s = match s with (true, _) -> true | _ -> false

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

exception NotUnique
let find_unique test dest id s =
  let (i, j) = List.fold_right (fun c (i, j) -> 
    if test c && dest c = id
    then (i+1, j-1)
    else (i, if i > 0 then j else j-1))
    s (0, List.length s)
  in
  if i = 1 then Some j 
  else if i > 1 then raise NotUnique 
  else  None

let find_unique_var = find_unique isVar destVar

let find_unique_rel = find_unique isRel destRel


let has_definition ts env t = 
  if isVar t then
    let var = destVar t in
    if not (Closure.is_transparent_variable ts var) then 
      false
    else
      let (_, v,_) = Environ.lookup_named var env in
      match v with
	| Some _ -> true
	| _ -> false
  else if isRel t then
    let n = destRel t in
    let (_,v,_) = Environ.lookup_rel n env in
    match v with
      | Some _ -> true
      | _ -> false
  else if isConst t then
    let c = destConst t in
    Closure.is_transparent_constant ts c && Environ.evaluable_constant c env
  else
    false

let get_definition env t =
  if isVar t then
    let var = destVar t in
    let (_, v,_) = Environ.lookup_named var env in
    match v with
      | Some c -> c
      | _ -> Util.anomaly "get_definition for var didn't have definition!"
  else if isRel t then
    let n = destRel t in
    let (_,v,_) = Environ.lookup_rel n env in 
    match v with
      | Some v -> (lift n) v
      | _ -> Util.anomaly "get_definition for rel didn't have definition!"
  else if isConst t then
    let c = destConst t in
    Environ.constant_value env c
  else
    Util.anomaly "get_definition didn't have definition!"

let get_def_app_stack env (c, args) =
  let (d, dargs) = decompose_app (get_definition env c) in
  (d, dargs @ args)

let try_unfolding ts env t =
  if has_definition ts env t then
    get_definition env t
  else
    t


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
let invert map sigma ctx t subs args ev' = 
  let sargs = subs @ args in
  let in_subs j = j < List.length ctx in
  let rmap = ref map in
  let rec invert' inside_evar t i =
    let t = Evarutil.whd_head_evar sigma t in
    match kind_of_term t with
      | Var id -> 
	find_unique_var id sargs >>= fun j -> 
	if in_subs j then
	  let (name, _, _) = List.nth ctx j in
	  return (mkVar name)
	else
	  return (mkRel (List.length sargs - j + i))
      | Rel j when j > i-> 
	find_unique_rel (j-i) sargs >>= fun k -> 
	if in_subs k then
	  let (name, _, _) = List.nth ctx k in
	  return (mkVar name)
	else
	  return (mkRel (List.length sargs - k + i))

      | Evar (ev, evargs) when ev = ev' ->
        None

      | Evar (ev, evargs) ->
	begin
	  let f (j : int) c  = 
            match invert' true c i with
              | Some c' -> c'
              | _ -> 
		if (not inside_evar) && (isVar c || isRel c || Termops.occur_evar ev' c) then
		  begin
		    (if not (Util.Intmap.mem ev !rmap) then
			rmap := Util.Intmap.add ev [j] !rmap
		     else
                        let ls = Util.Intmap.find ev !rmap in
			rmap := Util.Intmap.add ev (j :: ls) !rmap)
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
  (try invert' false t 0 with NotUnique -> None) >>= fun c' ->
  return (!rmap, c')

let collect_vars =
  let rec aux vars c = match kind_of_term c with
  | Var id -> Names.Idset.add id vars
  | _ -> fold_constr aux vars c in
  aux Names.Idset.empty

let free_vars_intersect tm vars = 
  Names.Idset.exists (fun v -> List.mem v vars) (collect_vars tm)

let some_or_prop o =
  match o with
      None -> mkProp
    | Some tm -> tm

(** removes the positions in the list, and all dependent elements *)
let remove l pos =
  let length = List.length l in
  let l = List.rev l in
  let rec remove' i l vs =
    match l with
      | [] -> []
      | ((x, o, t as p) :: s) -> 
        if List.mem i pos 
	  || free_vars_intersect t vs 
	  || free_vars_intersect (some_or_prop o) vs then
          remove' (i-1) s (x :: vs)
        else
          (p :: remove' (i-1) s vs)
  in List.rev (remove' (length-1) l [])

let free_vars_in tm vars = 
  Names.Idset.for_all (fun v -> List.mem v vars) (collect_vars tm)

exception CannotPrune
(** ev is the evar and plist the indices to prune.  from ?ev : T[env]
    it creates a new evar ?ev' with a shorter context env' such that
    ?ev := ?ev'[id_env']. If the prunning is unsuccessful, it throws
    the exception CannotPrune. *)
let rec prune evd (ev, plist) =
  (* HACK: assume that if ev is defined, then it was already prunned *)
  if Evd.is_defined evd ev then evd
  else
  let evi = Evd.find_undefined evd ev in
  let env = Evd.evar_context evi in
  let env' = remove env plist in
  let env_val' = (List.fold_right Environ.push_named_context_val env' 
                    Environ.empty_named_context_val) in
  (* the type of the evar may contain an evar depending on the some of
     the vars that we want to prune, so we need to prune that
     aswell *)
  let concl = Reductionops.nf_evar evd (Evd.evar_concl evi) in
  let id_env' = Array.to_list (id_substitution env') in
  match invert Util.Intmap.empty evd env' concl id_env' [] ev with
      None -> raise CannotPrune
    | Some (m, concl) ->
      let evd = prune_all m evd in
      let concl = Reductionops.nf_evar evd (Evd.evar_concl evi) in
      let evd', ev' = Evarutil.new_evar_instance env_val' evd 
	concl id_env' in
      Evd.define ev ev' evd'

and prune_all map evd =
  List.fold_left prune evd (Util.Intmap.bindings map)

(* pre: |s1| = |s2| 
   pos: None if s1 or s2 are not equal and not var to var subs
        Some l with l list of indexes where s1 and s2 do not agree *)
let intersect env sigma s1 s2 =
  let n = Array.length s1 in
  let rec intsct i =
    if i < n then
      intsct (i+1) >>= fun l ->
      if eq_constr s1.(i) s2.(i) then
        Some l
      else
        if (isVar s1.(i) || isRel s1.(i)) &&  (isVar s2.(i) || isRel s2.(i)) then
          Some (i :: l) (* both position holds variables: they are indeed different *)
        else if is_aggressive () then Some (i :: l)
	else None
    else Some []
  in 
  assert (Array.length s2 = n) ;
  intsct 0

(* pre: ev is a not-defined evar *)
let unify_same env sigma ev subs1 subs2 =
  match intersect env sigma subs1 subs2 with
  | Some [] -> success sigma
  | Some l -> begin
              try 
		success (prune sigma (ev, l))
              with CannotPrune -> err sigma
              end
  | _ -> err sigma



(* given a list of arguments [args] = [x1 .. xn], a [body] with free
   indices [1 .. n], and a substitution [subst] with context [nc] it
   returns [fun x1 : A1{subst}^-1 => .. => fun xn : An{subst}^-1 =>
   body], where each [A_i] is the type of [x_i].
*)
let fill_lambdas_invert_types map env sigma nc body subst args ev =
  let rmap = ref map in
  List.fold_right (fun arg r-> r >>= fun (ars, bdy) ->
    let ty = Retyping.get_type_of env sigma arg in
    let ars = Util.list_drop_last ars in
    invert map sigma nc ty subst ars ev >>= fun (m, ty) ->
    rmap := m;
    return (ars, mkLambda (Names.Anonymous, ty, bdy))) args (return (args, body)) 
  >>= fun (_, bdy) -> return (!rmap, bdy)

exception ProjectionNotFound
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
    raise ProjectionNotFound

let run_function = ref (fun _ _ _ -> None)
let set_run f = run_function := f

let lift_constr = ref (lazy mkProp)
let set_lift_constr c = lift_constr := c

let is_lift c = 
  try eq_constr c (Lazy.force !lift_constr)
  with _ -> false

let run_cs = ref (lazy (mkProp,mkProp))
let set_run_cs c = run_cs := c

let is_run_proj c = 
  try eq_constr c (fst (Lazy.force !run_cs))
  with _ -> false

let is_run_cst c = 
  try eq_constr c (snd (Lazy.force !run_cs))
  with _ -> false

let rec pad l = if l <= 0 then () else (Printf.printf "_"; pad (l-1))

let print_bar l = if l > 0 then Printf.printf "%s" "|" else ()
    
let debug_str s l =
  if !debug then 
    begin
      print_bar l;
      pad l;
      Printf.printf "%s\n" s
    end
  else
    ()

let debug_eq sigma env c1 c2 l = 
  print_bar l;
  pad l;
  Pp.msg (Termops.print_constr_env env (Evarutil.nf_evar sigma (applist c1)));
  Printf.printf "%s" " =?= ";
  Pp.msg (Termops.print_constr_env env (Evarutil.nf_evar sigma (applist c2)));
  Printf.printf "\n" 
  
type stucked = NotStucked | StuckedLeft | StuckedRight
type direction = Original | Swap

let evar_apprec ts env sigma (c, stack) =
  let rec aux s =
    let (t,stack) = Reductionops.whd_betaiota_deltazeta_for_iota_state ts env sigma s in
    match kind_of_term t with
      | Evar (evk,_ as ev) when Evd.is_defined sigma evk ->
	  aux (Evd.existential_value sigma ev, stack)
      | _ -> (t, Reductionops.list_of_stack stack)
  in aux (c, Reductionops.append_stack_list stack Reductionops.empty_stack)

let array_mem_to_i e i a =
  let j = ref 0 in
  let b = ref false in
  while !j < i && not !b do 
    if a.(!j) = e then
      b := true
    else
      j := !j+1
  done;
  !b

let remove_non_var env sigma (ev, subs as evsubs) args =
  let length = Array.length subs in
  let (_, ps) = Array.fold_right (fun a (i, s) -> 
    if isVarOrRel a && not (array_mem_to_i a i subs || List.mem a args) then (i-1,s)
    else (i-1, i::s)) subs (length-1, [])  in
  if ps = [] then raise CannotPrune
  else
    let sigma' = prune sigma (ev, ps) in
    (sigma', Reductionops.nf_evar sigma' (mkEvar evsubs), args)


exception InternalException

let tbl = Hashtbl.create 1000

let tblfind t x = try Hashtbl.find t x with Not_found -> false

(* pre: c and c' are in whdnf with our definition of whd *)
let rec unify' ?(conv_t=Reduction.CONV) dbg ts env sigma0 (c, l) (c', l') =
  let (c, l1) = decompose_app (Evarutil.whd_head_evar sigma0 c) in
  let (c', l2) = decompose_app (Evarutil.whd_head_evar sigma0 c') in
  let l, l' = l1 @ l, l2 @ l' in
  let t, t' = (c, l), (c', l') in
  if !debug then debug_eq sigma0 env t t' dbg else ();
  let res =
    if Evarutil.is_ground_term sigma0 (applist t) && Evarutil.is_ground_term sigma0 (applist t') 
      && Reductionops.is_trans_fconv conv_t ts env sigma0 (applist t) (applist t') 
    then begin debug_str "Reduce-Same" dbg; success sigma0 end
    else if use_hash () && tblfind tbl (sigma0, env, (c,l),(c',l')) then begin
      debug_str "Hash-Hit" dbg;
      err sigma0 end else begin
  match (kind_of_term c, kind_of_term c') with
  | Evar _, _ 
  | _, Evar _ ->
    one_is_meta dbg ts conv_t env sigma0 t t'

  | _, _  ->
    (
      if (isConst c || isConst c') && not (eq_constr c c') then
	begin
          if is_lift c && List.length l = 3 then
            run_and_unify dbg ts env sigma0 l t'
          else if is_lift c' && List.length l' = 3 then
            run_and_unify dbg ts env sigma0 l' t
          else
            err sigma0
	end
      else
        err sigma0
    ) ||= fun _ ->
    (
      if (isConst c || isConst c') && not (eq_constr c c') then
	try conv_record dbg ts env sigma0 t t'
	with ProjectionNotFound ->
	  try conv_record dbg ts env sigma0 t' t
	  with ProjectionNotFound -> err sigma0
      else
	err sigma0
    ) ||= fun _ ->
    (
      let n = List.length l in
      let m = List.length l' in
      if n = m then 
	begin 
	  debug_str "App-FO" dbg;
	  compare_heads conv_t (dbg+1) ts env sigma0 c c' &&= fun sigma1 ->
          ise_list2 sigma1 (unify_constr (dbg+1) ts env) l l'
	end
      else
	err sigma0
    ) ||= fun _ ->
    (
      try_step dbg conv_t ts env sigma0 t t'
    ) 
    end
  in
  if is_success res then 
    debug_str "ok" dbg
  else begin
    if use_hash () then Hashtbl.add tbl (sigma0, env, (c, l), (c',l')) true else ();
    debug_str "err" dbg
  end;
  res

and unify_constr ?(conv_t=Reduction.CONV) dbg ts env sigma0 t t' =
  unify' ~conv_t dbg ts env sigma0 (decompose_app t) (decompose_app t')

and run_and_unify dbg ts env sigma0 args ty =
  let a, f, v = List.nth args 0, List.nth args 1, List.nth args 2 in
  unify' ~conv_t:Reduction.CUMUL (dbg+1) ts env sigma0 (decompose_app a) ty &&= fun sigma1 ->
  print_bar dbg;
  pad dbg;
  Printf.printf "Running: ";
  Pp.msg (Termops.print_constr_env env (Evarutil.nf_evar sigma1 f));
  Printf.printf "\n";
  match !run_function env sigma1 f with
  | Some (sigma2, v') -> 
    print_bar dbg;
    pad dbg;
    Printf.printf "Resulted in: ";
    Pp.msg (Termops.print_constr_env env (Evarutil.nf_evar sigma2 v));
    Printf.printf "\n";    
    unify' (dbg+1) ts env sigma2 (decompose_app v) (decompose_app v')
  | _ -> debug_str "Failed" dbg; err sigma0

and try_solve_simple_eqn dbg ts env sigma evsubs args t =
  if get_solving_eqn () then
    try
      let t = Evarutil.solve_pattern_eqn env args (applist t) in
      match Evarutil.solve_simple_eqn (unify_evar_conv ts) env sigma (None, evsubs, t) with
	| (_, false) -> err sigma
	| (sigma', true) -> Printf.printf "%s" "solve_simple_eqn solved it: ";
	  stat_solve_simple_eqn := Big_int.succ_big_int !stat_solve_simple_eqn;
	  debug_eq sigma env (mkEvar evsubs, []) (decompose_app t) dbg;
	  success sigma'
    with _ -> 
      Printf.printf "%s" "solve_simple_eqn failed!";
      err sigma
  else
    err sigma

and one_is_meta dbg ts conv_t env sigma0 (c, l as t) (c', l' as t') =
  (* first we instantiate all defined metas *)
  let nf_map = List.map (fun a->Reductionops.nf_evar sigma0 a) in
  let (c, l) = (Reductionops.nf_evar sigma0 c, nf_map l) in 
  let (c', l') = (Reductionops.nf_evar sigma0 c', nf_map l') in
  if isEvar c && isEvar c' then
    let (k1, s1 as e1), (k2, s2 as e2) = destEvar c, destEvar c' in
    if k1 = k2 then
      (* Meta-Same *)
      begin
	debug_str "Meta-Same-Same or Meta-Same" dbg;
	unify_same env sigma0 k1 s1 s2 &&= fun sigma1 ->
	ise_list2 sigma1 (unify_constr (dbg+1) ts env) l l'
      end
    else
      begin
      (* Meta-Meta *)
	debug_str "Meta-Meta" dbg;
        (
	if k1 > k2 then
	  instantiate dbg ts conv_t env sigma0 e1 l t' ||= fun _ ->
	  instantiate ~dir:Swap dbg ts conv_t env sigma0 e2 l' t ||= fun _ ->
          try_solve_simple_eqn dbg ts env sigma0 e1 l t'
	else
	  instantiate ~dir:Swap dbg ts conv_t env sigma0 e2 l' t ||= fun _ ->
	  instantiate dbg ts conv_t env sigma0 e1 l t' ||= fun _ ->
          try_solve_simple_eqn dbg ts env sigma0 e2 l' t
        ) (* ||= fun _ ->
          try_solve_simple_eqn dbg ts env sigma0 e1 l t' ||= fun _ ->
          try_solve_simple_eqn dbg ts env sigma0 e2 l' t *)
      end
  else
    if isEvar c then
      if is_lift c' && List.length l' = 3 then
        run_and_unify dbg ts env sigma0 l' t
      else
	begin
	  let e1 = destEvar c in
	  instantiate dbg ts conv_t env sigma0 e1 l t' ||= fun _ ->
          try_solve_simple_eqn dbg ts env sigma0 e1 l t'
	end
    else
      if is_lift c && List.length l = 3 then
        run_and_unify dbg ts env sigma0 l t'
      else
	begin
          let e2 = destEvar c' in
	  instantiate ~dir:Swap dbg ts conv_t env sigma0 e2 l' t ||= fun _ ->
          try_solve_simple_eqn dbg ts env sigma0 e2 l' t
	end

and compare_heads conv_t dbg ts env sigma0 c c' =
  match (kind_of_term c, kind_of_term c') with
  (* Prop-Same, Set-Same, Type-Same, Type-Same-LE *)
  | Sort s1, Sort s2 -> debug_str "Type-Same" dbg;
    begin
    try
	let sigma1 = match conv_t with
      | Reduction.CONV -> Evd.set_eq_sort sigma0 s1 s2 
      | _ -> Evd.set_leq_sort sigma0 s1 s2
      in (true, sigma1)
    with _ -> err sigma0 
    end

  (* Lam-Same *)
  | Lambda (name, t1, c1), Lambda (_, t2, c2) ->
    debug_str "Lam-Same" dbg;
    let env' = Environ.push_rel (name, None, t1) env in
    unify_constr (dbg+1) ts env sigma0 t1 t2 &&= fun sigma1 ->
    unify_constr ~conv_t (dbg+1) ts env' sigma1 c1 c2 &&= fun sigma2 ->
    success sigma2

  (* Prod-Same *)
  | Prod (name, t1, c1), Prod (_, t2, c2) ->
    debug_str "Prod-Same" dbg;
    unify_constr (dbg+1) ts env sigma0 t1 t2 &&= fun sigma1 ->
    unify_constr ~conv_t (dbg+1) ts (Environ.push_rel (name,None,t1) env) sigma1 c1 c2

  | LetIn (name, trm1, ty1, body1), LetIn (_, trm2, ty2, body2) ->
    (
      (* Let-Same *)
      debug_str "Let-Same" dbg;
      let env' = Environ.push_rel (name, Some trm1, ty1) env in
      unify_constr (dbg+1) ts env sigma0 ty1 ty2 &&= fun sigma1 ->
      unify_constr (dbg+1) ts env sigma0 trm1 trm2 &&= fun sigma2 ->
      unify_constr ~conv_t (dbg+1) ts env' sigma2 body1 body2
    ) ||= (fun _ ->
      (* Let-Zeta *)
      debug_str "Let-Zeta" dbg;
      let body1 = subst1 trm1 body1 in
      let body2 = subst1 trm2 body2 in
      unify_constr ~conv_t (dbg+1) ts env sigma0 body1 body2
    )

  (* Rigid-Same *)
  | Rel n1, Rel n2 when n1 = n2 ->
    debug_str "Rigid-Same" dbg;
    success sigma0
  | Var id1, Var id2 when id1 = id2 -> 
    debug_str "Rigid-Same" dbg;
    success sigma0
  | Const c1, Const c2 when Names.eq_constant c1 c2 ->
    debug_str "Rigid-Same" dbg;
    success sigma0
  | Ind c1, Ind c2 when Names.eq_ind c1 c2 ->
    debug_str "Rigid-Same" dbg;
    success sigma0
  | Construct c1, Construct c2 
    when Names.eq_constructor c1 c2  ->
    debug_str "Rigid-Same" dbg;
    success sigma0

  | CoFix (i1,(_,tys1,bds1 as recdef1)), CoFix (i2,(_,tys2,bds2))
    when i1 = i2 ->
    debug_str "CoFix-Same" dbg;
    ise_array2 sigma0 (unify_constr (dbg+1) ts env) tys1 tys2 &&= fun sigma1 ->
    ise_array2 sigma1 (unify_constr (dbg+1) ts (Environ.push_rec_types recdef1 env)) bds1 bds2
	
  | Case (_, p1, c1, cl1), Case (_, p2, c2, cl2) ->
    (
      debug_str "Case-Same" dbg;
      unify_constr (dbg+1) ts env sigma0 p1 p2 &&= fun sigma1 ->
      unify_constr (dbg+1) ts env sigma1 c1 c2 &&= fun sigma2 ->
      ise_array2 sigma2 (unify_constr (dbg+1) ts env) cl1 cl2
    ) 

  | Fix (li1, (_, tys1, bds1 as recdef1)), Fix (li2, (_, tys2, bds2)) 
    when li1 = li2 ->
    debug_str "Fix-Same" dbg;
    ise_array2 sigma0 (unify_constr (dbg+1) ts env) tys1 tys2 &&= fun sigma1 ->
    ise_array2 sigma1 (unify_constr (dbg+1) ts (Environ.push_rec_types recdef1 env)) bds1 bds2

  | _, _ -> err sigma0

and is_reducible ts env (c, l) =
  (isLambda c && l <> []) ||
  (isLetIn c) ||
  ((isRel c || isVar c) && has_definition ts env c)

and try_step ?(stuck=NotStucked) dbg conv_t ts env sigma0 (c, l as t) (c', l' as t') =
  match (kind_of_term c, kind_of_term c') with

  (* Lam-BetaR *)
  | _, Lambda (_, _, trm) when l' <> [] ->
    debug_str "Lam-BetaR" dbg;
    let t2 = (subst1 (List.hd l') trm, List.tl l') in
    unify' ~conv_t (dbg+1) ts env sigma0 t t2 
  (* Let-ZetaR *)
  | _, LetIn (_, trm, _, body) when not (isLetIn c) ->
    debug_str "Let-ZetaR" dbg;
    let t2 = (subst1 trm body, l') in
    unify' ~conv_t (dbg+1) ts env sigma0 t t2

  | _, Case _ | _, Fix _ when stuck <> StuckedRight ->
    let t2 = evar_apprec ts env sigma0 t' in
    if t' <> t2 then
      begin
	debug_str "IotaR" dbg;
	unify' ~conv_t (dbg+1) ts env sigma0 t t2
      end
    else if stuck = NotStucked then
      try_step ~stuck:StuckedRight dbg conv_t ts env sigma0 t t'
    else err sigma0

  (* Lam-BetaL *)
  | Lambda (_, _, trm), _ when l <> [] ->
    debug_str "Lam-BetaL" dbg;
    let t1 = (subst1 (List.hd l) trm, List.tl l) in
    unify' ~conv_t (dbg+1) ts env sigma0 t1 t'
  (* Let-ZetaL *)
  | LetIn (_, trm, _, body), _ when not (isLetIn c') ->
    debug_str "Let-ZetaL" dbg;
    let t1 = (subst1 trm body, l) in
    unify' ~conv_t (dbg+1) ts env sigma0 t1 t'

  | Case _, _ | Fix _, _ when stuck <> StuckedLeft ->
    let t2 = evar_apprec ts env sigma0 t in
    if t <> t2 then
      begin
	debug_str "IotaL" dbg;
	unify' ~conv_t (dbg+1) ts env sigma0 t2 t'
      end
    else if stuck = NotStucked then
      try_step ~stuck:StuckedLeft dbg conv_t ts env sigma0 t t'
    else err sigma0
(*
  (* Var-DeltaR *)
  | _, Rel _ 
  | _, Var _ when has_definition ts env c' ->
    debug_str "Delta-VarR" dbg;
    unify' ~conv_t (dbg+1) ts env sigma0 t (get_def_app_stack env t')

  (* Var-DeltaL *)
  | Rel _, _ 
  | Var _, _ when has_definition ts env c ->
    debug_str "Delta-VarL" dbg;
    unify' ~conv_t (dbg+1) ts env sigma0 (get_def_app_stack env t) t'
*)
(*
  | _, _ when is_reducible ts env t' ->
    debug_str "FlexibleR" dbg;
    unify' ~conv_t (dbg+1) ts env sigma0 t (evar_apprec ts env sigma0 t')

  | _, _ when is_reducible ts env t ->
    debug_str "FlexibleR" dbg;
    unify' ~conv_t (dbg+1) ts env sigma0 (evar_apprec ts env sigma0 t) t'
*)    

  (* Constants get unfolded after everything else *)
  | _, Const _
  | _, Rel _
  | _, Var _ when has_definition ts env c' && stuck = NotStucked ->
      if is_stuck ts env sigma0 t' then
	try_step ~stuck:StuckedRight dbg conv_t ts env sigma0 t t'
      else 
	begin
	  debug_str "Cons-DeltaNotStuckR" dbg;
	  unify' ~conv_t (dbg+1) ts env sigma0 t (evar_apprec ts env sigma0 (get_def_app_stack env t'))
	end
  | Const _, _ 
  | Rel _, _ 
  | Var _, _  when has_definition ts env c && stuck = StuckedRight ->
    debug_str "Cons-DeltaStuckL" dbg;
    unify' ~conv_t (dbg+1) ts env sigma0 (evar_apprec ts env sigma0 (get_def_app_stack env t)) t'

  | _, Const _ 
  | _, Rel _
  | _, Var _ when has_definition ts env c' ->
    debug_str "Cons-DeltaR" dbg;
    unify' ~conv_t (dbg+1) ts env sigma0 t (evar_apprec ts env sigma0 (get_def_app_stack env t'))
  | Const _, _
  | Rel _, _ 
  | Var _, _  when has_definition ts env c ->
    debug_str "Cons-DeltaL" dbg;
    unify' ~conv_t (dbg+1) ts env sigma0 (evar_apprec ts env sigma0 (get_def_app_stack env t)) t'

  (* Lam-EtaR *)
  | _, Lambda (name, t1, c1) when l' = [] && not (isLambda c) ->
    debug_str "Lam-EtaR" dbg;
    eta_match dbg ts env sigma0 (name, t1, c1) t
  (* Lam-EtaL *)
  | Lambda (name, t1, c1), _ when l = [] && not (isLambda c') ->
    debug_str "Lam-EtaL" dbg;
    eta_match dbg ts env sigma0 (name, t1, c1) t'

  | _, _ -> err sigma0

and is_stuck ts env sigma (hd, args) =
  let (hd, args) = evar_apprec ts env sigma (try_unfolding ts env hd, args) in
  let rec is_unnamed (hd, args) = match kind_of_term hd with
    | (Var _|Construct _|Ind _|Const _|Prod _|Sort _) -> false
    | (Case _|Fix _|CoFix _|Meta _|Rel _)-> true
    | Evar _ -> false (* immediate solution without Canon Struct *)
    | Lambda _ -> assert(args = []); true
    | LetIn (_, b, _, c) -> is_unnamed (evar_apprec ts env sigma (subst1 b c, args))
    | App _| Cast _ -> assert false
  in is_unnamed (hd, args)
    
and remove_equal_tail (h, args) (h', args') =
  let rargs = List.rev args in
  let rargs' = List.rev args' in
  let noccur i xs ys = not (Termops.occur_term i h')
      && not (List.exists (Termops.occur_term i) ys) in
  let rec remove rargs rargs' =
    match rargs, rargs' with
      | (x :: xs), (y :: ys) when eq_constr x y && noccur x xs ys -> remove xs ys
      | _, _ -> rargs, rargs'
  in 
  let (xs, ys) = remove rargs rargs' in
  (List.rev xs, List.rev ys)

(* pre: args and args' are lists of vars and/or rels. subs is an array of rels and vars. *) 
and instantiate' dbg ts conv_t env sigma0 (ev, subs as uv) args (h, args') =
  let args, args' = remove_equal_tail (mkEvar uv, args) (h, args') in
  (* beta-reduce to remove dependencies *)
  let t = Reductionops.whd_beta sigma0 (applist (h, args')) in 
    let evi = Evd.find_undefined sigma0 ev in
    let nc = Evd.evar_filtered_context evi in
    let res = 
      let subsl = Array.to_list subs in
      invert Util.Intmap.empty sigma0 nc t subsl args ev >>= fun (map, t') ->
      fill_lambdas_invert_types map env sigma0 nc t' subsl args ev >>= fun (map, t') ->
      let sigma1 = prune_all map sigma0 in
      let t'' = Evd.instantiate_evar nc t' subsl in
      let t'' = Termops.refresh_universes t'' in
      let ty' = Retyping.get_type_of env sigma1 t'' in
      let ty = Evd.existential_type sigma1 uv in
      let p = unify_constr ~conv_t:Reduction.CUMUL (dbg+1) ts env sigma1 ty' ty &&= fun sigma2 ->
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
      | None -> err sigma0
  
(* by invariant, we know that ev is uninstantiated *)
and instantiate ?(dir=Original) dbg ts conv_t env sigma 
    (ev, subs as evsubs) args (h, args' as t) =
  (
    if is_variable_subs subs && is_variable_args args then
      begin
        (* Meta-InstL *)
        debug_str "Meta-Inst" dbg;
        try instantiate' dbg ts conv_t env sigma evsubs args t
        with CannotPrune -> err sigma
      end
    else err sigma
  ) ||= (fun _ ->
    if is_aggressive () then
      begin
        (* Meta-Prune *)
        debug_str "Meta-Prune" dbg;
        try 
	  let (sigma', evsubs', args'') = remove_non_var env sigma evsubs args in
	  unify' ~conv_t:conv_t dbg ts env sigma' (evsubs', args'') t
        with CannotPrune -> err sigma
      end
    else err sigma
  ) ||= (fun _ ->
    if should_try_fo args t then
      begin
        (* Meta-FO *)
        debug_str "Meta-FO" dbg;
        meta_fo dir dbg ts env sigma (evsubs, args) t
      end
    else
      err sigma
  ) ||= (fun _ ->
    (* Meta-Reduce: before giving up we see if we can reduce on the right *)
    if has_definition ts env h then
      begin
        debug_str "Meta-Reduce" dbg;
        let t' = evar_apprec ts env sigma (get_def_app_stack env t) in
        unify' ~conv_t:conv_t (dbg+1) ts env sigma (mkEvar evsubs, args) t'
      end
    else
      begin
        let t' = evar_apprec ts env sigma t in
	if t <> t' then
          begin
            debug_str "Meta-Reduce" dbg;
            unify' ~conv_t:conv_t (dbg+1) ts env sigma (mkEvar evsubs, args) t'
          end
	else err sigma
      end
  ) ||= (fun _ -> 
    (* if the equation is [?f =?= \x.?f x] the occurs check will fail, but there is a solution: eta expansion *)
    if isLambda h && List.length args' = 0 then
      begin
        debug_str "Lam-EtaR" dbg;
        eta_match dbg ts env sigma (destLambda h) (mkEvar evsubs, args)
      end
    else
      err sigma
)
 
and should_try_fo args (h, args') =
  List.length args > 0 && List.length args' >= List.length args

(* ?e a1 a2 = h b1 b2 b3 ---> ?e = h b1 /\ a1 = b2 /\ a2 = b3 *)
and meta_fo dir dbg ts env sigma (evsubs, args) (h, args') =
  let (args'1,args'2) =
              Util.list_chop (List.length args'-List.length args) args' in
  if dir = Original then 
    unify' (dbg+1) ts env sigma (mkEvar evsubs, []) (h, args'1) &&= fun sigma' ->
    ise_list2 sigma' (unify_constr (dbg+1) ts env) args args'2
  else
    unify' (dbg+1) ts env sigma (h, args'1) (mkEvar evsubs, []) &&= fun sigma' ->
    ise_list2 sigma' (unify_constr (dbg+1) ts env) args'2 args

(* unifies ty with a product type from {name : a} to some Type *)
and check_product dbg ts env sigma ty (name, a) =
  let nc = Environ.named_context env in
  let naid = Namegen.next_name_away name (Termops.ids_of_named_context nc) in
  let nc' = (naid, None, a) :: nc in
  let v = Evarutil.new_untyped_evar () in
  let sigma', univ = Evd.new_univ_variable sigma in
  let evi = Evd.make_evar (Environ.val_of_named_context nc') (mkType univ) in 
  let sigma'' = Evd.add sigma' v evi in
  let idsubst = Array.append [| mkRel 1 |] (id_substitution nc) in
  unify_constr (dbg+1) ts env sigma'' ty (mkProd (Names.Name naid, a, mkEvar(v, idsubst)))

and eta_match dbg ts env sigma0 (name, a, t1) (th, tl as t) =
  let env' = Environ.push_rel (name, None, a) env in
  let t' = applist (lift 1 th, List.map (lift 1) tl @ [mkRel 1]) in
  let ty = Retyping.get_type_of env sigma0 (applist t) in
  check_product dbg ts env sigma0 ty (name, a) &&= fun sigma1 ->
  unify_constr (dbg+1) ts env' sigma1 t1 t'

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
  debug_str "CS" dbg;
  ise_list2 evd' (fun i x1 x -> unify_constr (dbg+1) trs env i x1 (substl ks x))
    params1 params &&= fun i ->
  ise_list2 i (fun i u1 u -> unify_constr (dbg+1) trs env i u1 (substl ks u))
    us2 us &&= (fun i -> 
  if is_run_cst c then
    begin
      let f = mkApp(List.nth params1 2,[|t2|]) in
      print_bar dbg;
      pad dbg;
      Printf.printf "Running: ";
      Pp.msg (Termops.print_constr_env env (Evarutil.nf_evar i f));
      Printf.printf "\n";
      match !run_function env i f with
	| Some (i, v) -> 
	  print_bar dbg;
	  pad dbg;
	  Printf.printf "Resulted in: ";
	  Pp.msg (Termops.print_constr_env env (Evarutil.nf_evar i v));
	  Printf.printf "\n";
	  unify_constr (dbg+1) trs env i v (List.nth ks 0)
	| _ -> debug_str "Failed" dbg; err i
    end
  else
    success i) &&= fun i ->
  unify' (dbg+1) trs env i (decompose_app c1) (c,(List.rev ks)) &&= fun i ->
  ise_list2 i (unify_constr (dbg+1) trs env) ts ts1

and unify ?(conv_t=Reduction.CONV) = unify_constr ~conv_t:conv_t 0

and swap (a, b) = (b, a) 

and unify_evar_conv ts env sigma0 conv_t t t' =
  stat_unif_problems := Big_int.succ_big_int !stat_unif_problems;
  Hashtbl.clear tbl;
  swap (unify ~conv_t:conv_t ts env sigma0 t t')
