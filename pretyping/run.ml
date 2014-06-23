open List
open String

open Pp
open Term
open Termops
open Reductionops
open Environ
open Evarutil
open Evd
open Names
open Closure
open Util
open Evarconv
open Libnames

open Munify
open Stdlib_constr

let init = Stdlib_constr.reduce_value := Tacred.compute

module Exceptions = struct

  let mkInternalException = fun e -> mkApp (
    MtacNames.mkConstr "InternalException", [|MtacNames.mkConstr e|])

  let mkNullPointer = lazy (mkInternalException  "NullPointer")
  let mkTermNotGround = lazy (mkInternalException  "TermNotGround")
  let mkOutOfBounds = lazy (mkInternalException  "ArrayOutOfBounds")

  (* HACK: we put Prop as the type of the raise. We can put an evar, but
     what's the point anyway? *)
  let mkRaise e = mkApp(MtacNames.mkConstr "raise", [|mkProp; Lazy.force e|]) 

  let error_stuck = "Cannot reduce term, perhaps an opaque definition?"
  let error_param = "Parameter appears in returned value"
  let error_no_match = "No pattern matches"
  let error_abs = "Cannot abstract non variable"
  let error_abs_env = "Cannot abstract variable in a context depending on it"
  let error_abs_type = "Variable is appearing in the returning type"
  let error_abs_ref = "Variable is appearing in type of reference"
  let error_array_zero = "Array must have non-zero length"
  let unknown_reduction_strategy = "Unknown reduction strategy"

  let raise = error
end

module ReductionStrategy = struct

  let mkRed = fun s -> lazy (MtacNames.mkConstr s)
  let redNone = mkRed "RedNone"
  let redSimpl = mkRed "RedSimpl"
  let redWhd = mkRed "RedWhd"
  let redOneStep = mkRed "RedOneStep"

  let test = fun r c -> eq_constr (Lazy.force r) c
  let isRedNone = test redNone
  let isRedSimpl = test redSimpl
  let isRedWhd = test redWhd
  let isRedOneStep = test redOneStep

  let one_step env sigma c =
    let h, args = decompose_app c in
    let h = whd_evar sigma h in
    let r = 
      match kind_of_term h with
      | Lambda (_, _, trm) when args <> [] -> 
        (subst1 (List.hd args) trm, List.tl args)
      | LetIn (_, trm, _, body) -> (subst1 trm body, args)
      | Var _ | Rel _ | Const _ -> (Munify.try_unfolding Closure.all_transparent env h, args)
      | _ -> h, args
    in applist r
        

  let reduce sigma env strategy c =
    if isRedNone strategy then
      c
    else if isRedSimpl strategy then
      Tacred.simpl env sigma c
    else if isRedWhd strategy then
      whd_betadeltaiota env sigma c
    else if isRedOneStep strategy then
      one_step env sigma c
    else
      Exceptions.raise Exceptions.unknown_reduction_strategy 

end

module UnificationStrategy = struct

  let mkUni = fun s -> lazy (MtacNames.mkConstr s)
  let uniRed = mkUni "UniRed"
  let uniSimpl = mkUni "UniSimpl"
  let uniMuni = mkUni "UniMuni"

  let test = fun r c -> eq_constr (Lazy.force r) c
  let isUniRed = test uniRed
  let isUniSimpl = test uniSimpl
  let isUniMuni = test uniMuni

  let find_pbs sigma evars =
    let (_, pbs) = extract_all_conv_pbs sigma in
    List.filter (fun (_,_,c1,c2) -> 
      List.exists (fun e -> 
	Termops.occur_term e c1 || Termops.occur_term e c2) evars) pbs

  let unify rsigma env evars strategy t1 t2 =
    if isUniRed strategy then
      try
        let sigma = the_conv_x ~eta:false env t2 t1 !rsigma in
	rsigma := consider_remaining_unif_problems env sigma;
        List.length (find_pbs !rsigma evars) = 0
      with _ -> false
    else if isUniSimpl strategy then
      let b, sigma = Simpleunify.unify env !rsigma t2 t1 in
      rsigma := sigma;
      b && List.length (find_pbs sigma evars) = 0
    else if isUniMuni strategy then
      let b, sigma = Munify.unify Names.full_transparent_state env !rsigma t2 t1 in
      rsigma := sigma;
      b
    else
      Exceptions.raise Exceptions.unknown_reduction_strategy 

end

let mkT () = Lazy.force MtacNames.mkT_lazy



type data = Val of (evar_map * constr) | Err of constr

let (>>=) v g =
  match v with
    | Val v' -> g v'
    | _ -> v

let return s t = Val (s, t)

let fail t = Err t
(*
let uflags =
  { Unification.default_unify_flags with
    Unification.modulo_eta = false }
*)
let rec open_pattern (env, sigma) p evars =
  let (patt, args) = whd_betadeltaiota_stack env sigma p in
  let length = List.length args in
  let nth = List.nth args in
  if MtacNames.isBase patt && length = 6 then
    let p = nth 3 in
    let b = nth 4 in
    let strategy = nth 5 in
    Some (sigma, evars, p, b, strategy)
  else if MtacNames.isTele patt && length = 5 then
    let c = nth 2 in
    let f = nth 4 in
    let (sigma', evar) = Evarutil.new_evar sigma env (* empty_env *) c in
(*    let evar = Evarutil.new_meta () in
    let sigma' = Evd.meta_declare evar c sigma in *)
    open_pattern (env, sigma') (mkApp (f, [|evar|])) (evar :: evars)
  else
    None



let rec runmatch' (env, sigma as ctxt) t ty patts' i =
  let (patts, args) =  whd_betadeltaiota_stack env sigma patts' in
  if CoqList.isNil patts && List.length args = 1 then
    Exceptions.raise Exceptions.error_no_match
  else if CoqList.isCons patts && List.length args = 3 then
    match open_pattern ctxt (List.nth args 1) [] with
        Some (sigma', evars, p, body, strategy) ->
          let rsigma' = ref sigma' in
	  let devars = destEvars evars in
          begin
            if unify env rsigma' evars strategy p t && all_defined rsigma' devars then
              let body = nf_evar !rsigma' body in
              let () = remove_all rsigma' devars in
	      let body' = mkApp(body, [|CoqEq.mkAppEqRefl ty t|]) in
              (!rsigma', body')
            else
              runmatch' ctxt t ty (List.nth args 2) (i+1)
          end
      | None -> Exceptions.raise Exceptions.error_stuck
  else
    Exceptions.raise Exceptions.error_stuck

and destEvars =
  (* fun l -> l *)
  List.map (fun e-> let ev, _ = destEvar e in ev)

and all_defined rsigma =
  (* List.fold_left (fun b e -> b && Evd.meta_defined !rsigma e) true *)
  (*
  List.fold_left (fun b e -> b && Evd.is_defined !rsigma e) true
  *)
  (fun _->true)

and remove_all rsigma =
  fun l -> ()
  (* List.iter (fun e -> rsigma := Evd.remove !rsigma e) *)

and unify env rsigma evars strategy t1 t2 =
  UnificationStrategy.unify rsigma env evars strategy t1 t2


let runmatch (env, sigma as ctxt) t ty patts = 
  runmatch' ctxt t ty patts 0
   
    
let print env sigma s = Printf.printf "[DEBUG] %s\n" (CoqString.from_coq env sigma s)
let print_term t = Printf.printf "[DEBUG] "; msg (Termops.print_constr t); Printf.printf "\n"

exception AbstractingArrayType

let mysubstn t n c =
  let rec substrec in_arr depth c = match kind_of_term c with
    | App (c, l) when Refs.isArrRef c ->
      mkApp (c, [|substrec true depth l.(0); l.(1)|])
    | Rel k    ->
        if k<=depth then c
        else if k = depth+n then
          if in_arr then raise AbstractingArrayType
          else lift depth t
        else mkRel (k+1)
    | _ -> map_constr_with_binders succ (substrec in_arr) depth c in
  substrec false 0 c

(* solves typeclasses instances appearing in t *)
(* NOT WORKING!
let solve_instances_for env evd t =
  let revd = ref evd in
  let rec f depth c = 
    let c = whd_evar !revd c in
    match kind_of_term c with
    | Evar e     ->
      let ty = Evd.existential_type !revd e in
      let (evd', _) = Typeclasses.resolve_one_typeclass env !revd ty in
      revd := evd'
    | _ -> iter_constr_with_binders succ f depth c in
  f 0 t;
  !revd
*)

(* checks that no variable in env to the right of i (that is, smaller
   to i) depends on i. *)
let noccurn_env env i =
  let rec noc n =
    if n = 1 then true
    else
      let (_, t, a) = Environ.lookup_rel (i-n+1) env in
      noccurn (n-1) a 
      && (if t = None then true else noccurn (n-1) (let Some t' = t in t'))
      && noc (n-1)
  in noc i

let rec run' (env, sigma, undo as ctxt) t =
  let t = whd_betadeltaiota env sigma t in
  let (h, args) = decompose_app t in
  let nth = List.nth args in
  let assert_args n = 
    if List.length args = n then
      ()
    else
      Exceptions.raise "The number of arguments for the constructor is wrong"
  in
  let constr c = 
    if isConstruct h then
      let (m, ix) = destConstruct h in
      if eq_ind m (destInd (mkT ())) then
	ix
      else
	Exceptions.raise Exceptions.error_stuck
    else
      Exceptions.raise Exceptions.error_stuck
  in
  match constr h with
    | 1 -> assert_args 3; (* ret *)        
	return sigma (ReductionStrategy.reduce sigma env (nth 1) (nth 2))

      | 2 -> assert_args 4; (* bind *)
	run' ctxt (nth 2) >>= fun (sigma', v) ->
	let t' = mkApp(nth 3, [|v|]) in
	run' (env, sigma', undo) t'

      | 3 -> assert_args 3; (* try *)
	begin
	match run' ctxt (nth 1) with
	  | Val (sigma', v) -> return sigma' v
	  | Err i -> 
            let t' = mkApp(nth 2, [|i|]) in
            run' ctxt t'
	end

      | 4 -> assert_args 2; (* raise *)
	fail (List.nth args 1)

      | 5 -> assert_args 6; (* fix1 *)
	let a, b, s, i, f, x = nth 0, nth 1, nth 2, nth 3, nth 4, nth 5 in
	run_fix ctxt h [|a|] b s i f [|x|]

      | 6 -> assert_args 8; (* fix 2 *)
	let a1, a2, b, s, i, f, x1, x2 = nth 0, nth 1, nth 2, nth 3, nth 4, nth 5, nth 6, nth 7 in
	run_fix ctxt h [|a1; a2|] b s i f [|x1; x2|]

      | 7 -> assert_args 10; (* fix 3 *)
	let a1, a2, a3, b, s, i, f, x1, x2, x3 = 
	  nth 0, nth 1, nth 2, nth 3, nth 4, nth 5, nth 6, nth 7, nth 8, nth 9 in
	run_fix ctxt h [|a1; a2; a3|] b s i f [|x1; x2; x3|]

      | 8 -> assert_args 12; (* fix 4 *)
	let a1, a2, a3, a4, b, s, i, f, x1, x2, x3, x4 = 
	  nth 0, nth 1, nth 2, nth 3, nth 4, nth 5, nth 6, nth 7, nth 8, nth 9, nth 10, nth 11 in
	run_fix ctxt h [|a1; a2; a3; a4|] b s i f [|x1; x2; x3; x4|]

      | 9 -> assert_args 14; (* fix 5 *)
	let a1, a2, a3, a4, a5, b, s, i, f, x1, x2, x3, x4, x5 = 
	  nth 0, nth 1, nth 2, nth 3, nth 4, nth 5, nth 6, nth 7, nth 8, nth 9, nth 10, nth 11, nth 12, nth 13 in
	run_fix ctxt h [|a1; a2; a3; a4; a5|] b s i f [|x1; x2; x3; x4; x5|]

      | 10 -> assert_args 4; (* match *)
	let (sigma', body) = runmatch (env, sigma) (nth 2) (nth 0) (nth 3) in
	run' (env, sigma', undo) body

      | 11 -> assert_args 1; (* print *)
	let s = nth 0 in
	print env sigma s;
	return sigma (Lazy.force CoqUnit.mkTT)

      | 12 -> assert_args 3; (* nu *)
	let a, f = nth 0, nth 2 in
	let fx = mkApp(lift 1 f, [|mkRel 1|]) in
        let ur = ref [] in
        begin
	match run' (push_rel (Anonymous, None, a) env, sigma, (ur :: undo)) fx with
          | Val (sigma', e) ->
            clean !ur;
	    if Intset.mem 1 (free_rels e) then
              Exceptions.raise Exceptions.error_param
	    else
	      return sigma' (pop e)
          | Err e -> 
            clean !ur;
	    if Intset.mem 1 (free_rels e) then
              Exceptions.raise Exceptions.error_param
	    else
	      fail (pop e)
        end

      | 13 -> assert_args 2; (* is_param *)
	let e = whd_betadeltaiota env sigma (nth 1) in
	if isRel e then
	  return sigma (Lazy.force CoqBool.mkTrue)
	else
	  return sigma (Lazy.force CoqBool.mkFalse)

      | 14 -> assert_args 4; (* abs *)
        let a, p, x, y = nth 0, nth 1, nth 2, nth 3 in
        abs env sigma a p x y false

      | 15 -> assert_args 4; (* abs_eq *)
        let a, p, x, y = nth 0, nth 1, nth 2, nth 3 in
        abs env sigma a p x y true

      | 16 -> assert_args 1; (* evar *)
	let t = nth 0 in
	let (sigma', ev) = Evarutil.new_evar sigma env t in
	return sigma' ev

      | 17 -> assert_args 2; (* is_evar *)
	let e = whd_betadeltaiota env sigma (nth 1) in
	if isEvar e then
	  return sigma (Lazy.force CoqBool.mkTrue)
	else
	  return sigma (Lazy.force CoqBool.mkFalse)

      | 18 -> assert_args 3; (* hash *)
        return sigma (hash ctxt (nth 1) (nth 2))

      | 19 -> assert_args 4; (* nu_let *)
	let a, t, f = nth 0, nth 2, nth 3 in
	let fx = mkApp(lift 1 f, [|mkRel 1;CoqEq.mkAppEqRefl a (mkRel 1)|]) in
        let ur = ref [] in
        begin
	match run' (push_rel (Anonymous, Some t, a) env, sigma, (ur :: undo)) fx with
          | Val (sigma', e) ->
            clean !ur;
	    return sigma' (mkLetIn (Anonymous, t, a, e))
          | Err e -> 
            clean !ur;
	    if Intset.mem 1 (free_rels e) then
              Exceptions.raise Exceptions.error_param
	    else
	      fail (pop e)
        end

      | 20 -> assert_args 0; (* solve_typeclasses *)
	let evd' = Typeclasses.resolve_typeclasses env sigma in
	return evd' (Lazy.force CoqUnit.mkTT)

      | 21 -> assert_args 3; (* new_array *)
	let ty, n, c = nth 0, nth 1, nth 2 in
	return sigma (Refs.new_array env sigma undo ty n c)

      | 22 -> assert_args 3; (* get *)
	let ty, a, i = nth 0, nth 1, nth 2 in
	begin
	try
	  return sigma (Refs.get env sigma undo a i)
	with Refs.NullPointerException ->
	  fail (Lazy.force Exceptions.mkNullPointer)
	  | Refs.OutOfBoundsException ->
	  fail (Lazy.force Exceptions.mkOutOfBounds)
	end

      | 23 -> assert_args 4; (* set *)
	let ty, a, i, c = nth 0, nth 1, nth 2, nth 3 in
	begin
	try 
	  Refs.set env sigma undo a i c;
 	  return sigma (Lazy.force CoqUnit.mkTT)
	with Refs.OutOfBoundsException ->
	  fail (Lazy.force Exceptions.mkOutOfBounds)
	end

      | 24 -> assert_args 2; (* length *)
	let i = nth 1 in
	return sigma (Refs.length env sigma i)

      | 25 -> assert_args 2; (* print term *)
    let t = nth 1 in
    print_term t;
	return sigma (Lazy.force CoqUnit.mkTT)

      | _ ->
	Exceptions.raise "I have no idea what is this construct of T that you have here"

and abs env sigma a p x y eq_proof =
  let x = whd_betadeltaiota env sigma x in
    (* check if the type p does not depend of x, and that no variable
       created after x depends on it.  otherwise, we will have to
       substitute the context, which is impossible *)
  if isRel x then
    let rel = destRel x in
    if noccurn rel p then
      if noccurn_env env rel then
        try
          let y' = mysubstn (mkRel 1) rel y in
          let t = mkLambda (Anonymous, a, y') in
          if eq_proof then
            let ex_a = mkProd (Anonymous, a, mkApp(lift 1 p, [|mkRel 1|])) in
            let px_type = mkApp(p, [|x|]) in
            let px_type_lifted = mkApp(p, [|lift 1 x|]) in
            let ex_p = mkLambda (Anonymous, ex_a, CoqEq.mkAppEq px_type_lifted (mkApp(mkRel 1, [|lift 1 x|])) (lift 1 y)) in
            let ex_x = t in
            let ex_px = CoqEq.mkAppEqRefl px_type y in
            return sigma (CoqSigT.mkAppExistT ex_a ex_p ex_x ex_px)
          else
            return sigma t
        with AbstractingArrayType ->
          Exceptions.raise Exceptions.error_abs_ref          
      else
        Exceptions.raise Exceptions.error_abs_env
    else
      Exceptions.raise Exceptions.error_abs_type
  else
    Exceptions.raise Exceptions.error_abs

and clean =
  List.iter (fun i -> Refs.invalidate i)
    
and run_fix (env, sigma, _ as ctxt) h a b s i f x =
  let fixf = mkApp(h, Array.append a [|b;s;i;f|]) in
  let c = mkApp (f, Array.append [| fixf|] x) in
  run' ctxt c

and hash (env, sigma, undo) c size =
  let size = CoqN.from_coq env sigma size in
  let nus = List.length undo in
  let rec upd depth t =
    match kind_of_term t with
      | Rel k ->
        if depth < k then
          begin
            if k > depth + nus then
              mkRel (k - nus)
            else
              mkRel (k + nus - (2 * (k -1)))
          end
        else
          t
      | _ -> map_constr_with_binders succ upd depth t
  in
  let h = Term.hash_constr (upd 0 c) in
  CoqN.to_coq (Pervasives.abs (h mod size))

let assert_free_of_refs c =
  if not (Refs.used ()) then
    ()
  else if List.exists (fun i->i<0) (collect_metas c) then
    error "Returning a reference. This is not allowed since you might be naughty and use it in the next execution."
  else ()

let run (env, sigma) t  = 
  let _ = Refs.clean () in
  match run' (env, sigma, []) (nf_evar sigma t) with
    | Err i -> 
      assert_free_of_refs i;
      Err i
    | Val (sigma', v) -> 
      assert_free_of_refs v;
      Val (sigma', nf_evar sigma' v)


let pretypeT pretype tycon env evdref lvar c =
  let t = 
    match tycon with
      | Some (_, ty) -> ty
      | _ ->
        let sigma, univ = new_univ_variable !evdref in
        evdref := sigma;
        e_new_evar evdref env (mkType univ)
  in
  let tt = mkApp(mkT (), [|t|]) in
  t, pretype (mk_tycon tt) env evdref lvar c

let pretype_run pretype coerce_to_tycon tycon env evdref lvar loc c =
  let t, r = pretypeT pretype tycon env evdref lvar c in
  let d = run (env, !evdref) r.uj_val in
  match d with
    | Val (evmap, e) ->
      evdref := evmap ;
      let r = { uj_val = e; uj_type = t } in
      coerce_to_tycon loc env evdref r tycon
    | Err e -> 
      Pretype_errors.error_user_exception loc env !evdref e

let munify_run env evd f = 
  match run (env, evd) f with
    | Val v -> Some v
    | _ -> None

let _ = Munify.set_run munify_run
let _ = Munify.set_lift_constr (MtacNames.mkLazyConstr "lift")
