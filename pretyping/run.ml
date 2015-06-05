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

let reduce_value = Tacred.compute

module Constr = struct
  exception Constr_not_found of string

  let mkConstr name = lazy (
     try constr_of_global (Nametab.global_of_path (path_of_string name))
     with Not_found -> raise (Constr_not_found name)
  )

  let isConstr = fun r c -> eq_constr (Lazy.force r) c
end

module ConstrBuilder = struct

  type t = DaConstr of string

  let build_app t args = 
    let DaConstr s = t in
    mkApp (Lazy.force (Constr.mkConstr s), args)

  let equal t = 
    let DaConstr s = t in Constr.isConstr (Constr.mkConstr s)

  exception WrongConstr of t * constr

  let from_coq t (env, sigma as ctx) cterm =
    let (head, args) = whd_betadeltaiota_stack env sigma cterm in
    let args = Array.of_list args in
    if equal t head then
      args
    else
      raise (WrongConstr (t, head))
end

module CoqOption = struct
  let noneBuilder = ConstrBuilder.DaConstr "Coq.Init.Datatypes.None"

  let mkNone ty = ConstrBuilder.build_app noneBuilder [|ty|]

  let someBuilder = ConstrBuilder.DaConstr "Coq.Init.Datatypes.Some"

  let mkSome ty t = ConstrBuilder.build_app someBuilder [|ty; t|]

  let from_coq (env, sigma as ctx) cterm fsome = 
    try 
      let _ = ConstrBuilder.from_coq noneBuilder ctx cterm in
      None
    with ConstrBuilder.WrongConstr _ -> 
      let arr = ConstrBuilder.from_coq someBuilder ctx cterm in
      Some (fsome arr.(0))

end

module MtacNames = struct
  let mtacore_name = "Mtac.mtacore"
  let mtac_module_name = mtacore_name ^ ".Mtac"
  let mkLazyConstr = fun e-> Constr.mkConstr (mtac_module_name ^ "." ^ e)
  let mkConstr = fun e-> Lazy.force (Constr.mkConstr (mtac_module_name ^ "." ^ e))
  let mkBuilder = fun e-> ConstrBuilder.DaConstr (mtac_module_name ^ "." ^ e)
  let mkT_lazy = lazy (mkConstr "Mtac")

  let mkBase = mkLazyConstr "base"
  let mkTele = mkLazyConstr "tele"

  let isBase = Constr.isConstr mkBase
  let isTele = Constr.isConstr mkTele

end

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

module CoqList = struct
  let mkNil  = Constr.mkConstr "Coq.Init.Datatypes.nil"
  let mkCons = Constr.mkConstr "Coq.Init.Datatypes.cons"

  let makeNil ty = Term.mkApp (Lazy.force mkNil, [| ty |])
  let makeCons t x xs = Term.mkApp (Lazy.force mkCons, [| t ; x ; xs |])

  let mkListType ty = 
    mkApp (Lazy.force (Constr.mkConstr "Coq.Init.Datatypes.cons"),
    [|ty|])

  let isNil  = Constr.isConstr mkNil
  let isCons = Constr.isConstr mkCons

  let rec from_coq_conv (env, sigma as ctx) (fconv : Term.constr -> 'a) cterm =
    let (constr, args) = whd_betadeltaiota_stack env sigma cterm in
    if isNil constr then [] else
    if not (isCons constr) then invalid_arg "not a list" else
    let elt = List.nth args 1 in
    let ctail = List.nth args 2 in
    fconv elt :: from_coq_conv ctx fconv ctail

  let from_coq (env, sigma as ctx) =
    from_coq_conv ctx (fun x->x)

end

module CoqEq = struct
  let mkEq = Constr.mkConstr "Coq.Init.Logic.eq"
  let mkEqRefl = Constr.mkConstr "Coq.Init.Logic.eq_refl"

  let mkAppEq a x y = mkApp(Lazy.force mkEq, [|a;x;y|])
  let mkAppEqRefl a x = mkApp(Lazy.force mkEqRefl, [|a;x|])
end

module CoqSigT = struct
  let mkExistT  = Constr.mkConstr "Coq.Init.Specif.existT"

  let mkAppExistT a p x px =
    mkApp (Lazy.force mkExistT, [|a; p; x; px|])
end

module CoqNat = struct
  let mkZero = Constr.mkConstr "Coq.Init.Datatypes.O"
  let mkSucc = Constr.mkConstr "Coq.Init.Datatypes.S"

  let isZero = Constr.isConstr mkZero
  let isSucc = Constr.isConstr mkSucc

  let rec to_coq = function
    | 0 -> Lazy.force mkZero
    | n -> Term.mkApp (Lazy.force mkSucc, [| to_coq (pred n) |])

  let from_coq env evd c =
    let rec fc c = 
      if isZero c then
        0
      else 
        let (s, n) = destApp c in
        begin
          if isSucc s then
            1 + (fc (n.(0)))
          else
	    Exceptions.raise "Not a nat"
        end
    in
    let c' = reduce_value env evd c in
    fc c'
     
end

module CoqPositive = struct
  let xI = Constr.mkConstr "Coq.Numbers.BinNums.xI"
  let xO = Constr.mkConstr "Coq.Numbers.BinNums.xO"
  let xH = Constr.mkConstr "Coq.Numbers.BinNums.xH"

  let isH = Constr.isConstr xH
  let isI = Constr.isConstr xI
  let isO = Constr.isConstr xO
  
  let from_coq env evd c =
    let rec fc i c =
      if isH c then
        1
      else 
        let (s, n) = destApp c in
        begin
          if isI s then
            (fc (i+1) (n.(0)))*2 + 1
          else if isO s then
            (fc (i+1) (n.(0)))*2
          else
	    Exceptions.raise"Not a positive"
        end
    in
    let c' = reduce_value env evd c in
    fc 0 c'

  let rec to_coq n =
    if n = 1 then
      Lazy.force xH
    else if n mod 2 = 0 then
      mkApp(Lazy.force xO, [|to_coq (n / 2)|])
    else
      mkApp(Lazy.force xI, [|to_coq ((n-1)/2)|])

end

module CoqN = struct
  let tN = Constr.mkConstr "Coq.Numbers.BinNums.N"
  let h0 = Constr.mkConstr "Coq.Numbers.BinNums.N0"
  let hP = Constr.mkConstr "Coq.Numbers.BinNums.Npos"

  let is0 = Constr.isConstr h0
  let isP = Constr.isConstr hP

  let from_coq env evd c =
    let rec fc c = 
      if is0 c then
        0
      else 
        let (s, n) = destApp c in
        begin
          if isP s then
            CoqPositive.from_coq env evd (n.(0))
          else
	    Exceptions.raise "Not a positive"
        end
    in
    let c' = reduce_value env evd c in
    fc c'

  let to_coq n =
    if n = 0 then
      Lazy.force h0
    else
      mkApp(Lazy.force hP, [|CoqPositive.to_coq n|])
end

module CoqBool = struct

  let mkTrue = Constr.mkConstr "Coq.Init.Datatypes.true"
  let mkFalse = Constr.mkConstr "Coq.Init.Datatypes.false"

  let isTrue = Constr.isConstr mkTrue

end 

module CoqAscii = struct

  let from_coq env sigma c =
    let (h, args) = whd_betadeltaiota_stack env sigma c in
    let rec from_bits n bits =
      match bits with
        | [] -> 0
        | (b :: bs) -> (if CoqBool.isTrue b then 1 else 0) lsl n + from_bits (n+1) bs
    in 
    let n = from_bits 0 args in
    Char.escaped (Char.chr n)

end 

module CoqString = struct

  let mkEmpty = Constr.mkConstr "Coq.Strings.String.EmptyString"
  let mkString = Constr.mkConstr "Coq.Strings.String.String"

  let isEmpty = Constr.isConstr mkEmpty
  let isString = Constr.isConstr mkString

  let rec from_coq env sigma s =
    let (h, args) = whd_betadeltaiota_stack env sigma s in
    if isEmpty h then
      ""
    else if isString h then
      let c, s' = List.nth args 0, List.nth args 1 in
      CoqAscii.from_coq env sigma c ^ from_coq env sigma s'
    else
      Exceptions.raise "Not a string"

end

module CoqUnit = struct
  let mkTT = Constr.mkConstr "Coq.Init.Datatypes.tt"
end

(** An array that grows 1.5 times when it gets out of space *) 
module GrowingArray = struct
  type 'a t = 'a array ref * 'a * int ref
  
  let make i t = (ref (Array.make i t), t, ref 0)
  let length g = let (_, _, i) = g in !i

  exception OutOfBounds
                                  
  let get g i = 
    let (a, _, l) = g in 
    if i < !l then
      Array.get !a i
    else
      raise OutOfBounds

  let set g i = 
    let (a, _, l) = g in 
    if i < !l then
      Array.set !a i
    else
      raise OutOfBounds

  let add g t =
    let (a, e, i) = g in
    begin
    if Array.length !a <= !i then
      a := Array.append !a (Array.make (Array.length !a / 2) e)
    else
      ()
    end;
    Array.set !a !i t;
    i := !i+1
 
end

(*
  OUTDATED EXPLANATION: instead of storing one cell references we store arrays

   The context of the references is never changed, except when a new
   parameter is inserted using (nu x, t). Then, when exiting the context
   of nu x, we need to make sure that no reference refers to x. For this 
   reason, we keep a list of references to lists enumerating the references 
   pointing to x. To make it clear, the argument 'undo' used by many of the 
   functions has the following shape:

   [ r1 ; r2 ; ... ; rn ]

   where r1 corresponds to the innermost nu executed, and rn to the outermost.
   Each ri is a reference to a list [x1 ; ...; xim] of im references pointing
   to values that refer to the binder noted by i.

   When leaving the scope of x, the execution makes sure every reference listed 
   in the list referred on the top of the undo list is invalidated, that is,
   pointing to "null". 
*)
module ArrayRefFactory = 
struct
  let mkArrRef= Constr.mkConstr (MtacNames.mtac_module_name ^ ".carray")

  let isArrRef =  Constr.isConstr mkArrRef

  let to_coq a i n = 
    Term.mkApp (Lazy.force mkArrRef, [|a ; CoqN.to_coq i; n|])

  let from_coq env evd c =
    let c = whd_betadeltaiota env evd c in
    if isApp c && isArrRef (fst (destApp c)) then
      CoqN.from_coq env evd (snd (destApp c)).(1)
    else
      Exceptions.raise "Not a reference"

end

module ArrayRefs = struct

  let init () = GrowingArray.make 4 ((None, 0), [||])

  let bag = ref (init ())

  let clean () = 
    bag := init ()

  let get_parameters params t = Intset.filter (fun i -> i <= params) (free_rels t)

  let check_context undo index i arr =
    match arr.(i) with 
      | Some (c', _) ->     
        let level = List.length undo in
	(* check if the db index points to the nu context *)
        let params = get_parameters level c' in
        Intset.iter (fun k ->
          let rl = List.nth undo (k -1) in
          rl := ((index, i) :: !rl) (* mark this location as 'dirty' *)
        ) params
      | _ -> ()


  (* A, x : A |- 
       a <- make_array (Rel 2) 5 (Rel 1); // 5 copies of x
       // a is equal to [| (0, Rel 2), (0, Rel 1), ..., (0, Rel 1) |]
       // where 0 is the level
       nu y : A,
         // now the context is A, x : A, y : A
         // therefore the level is now 1
         let _ := array_get A a 0;
         // A is Rel 3 now, so in order to compare the type with the type of the array
         // we need to lift by 1 (level - l), where l is the level of the type
        array_set A a 0 y
  *)
  let new_array evd sigma undo ty n c =
    let level = List.length undo in
    let size = CoqN.from_coq evd sigma n in
    let arr = Array.make size (Some (c, level)) in
    let index = GrowingArray.length !bag in
    let params = get_parameters level ty in
    Intset.iter (fun k ->
      let rl = List.nth undo (k -1) in
      rl := ((index, -1) :: !rl) (* mark this location as 'dirty' *)
    ) params;
    GrowingArray.add !bag ((Some ty, level), arr);
    Array.iteri (fun i t -> check_context undo index i arr) arr;
    ArrayRefFactory.to_coq ty index n

  exception NullPointerException
  exception OutOfBoundsException
  exception WrongTypeException
  exception WrongIndexException

  let get env evd undo i ty k = 
    let level = List.length undo in
    let index = ArrayRefFactory.from_coq env evd i in
    let arri = CoqN.from_coq env evd k in
    try
      let ((aty, al), v) = GrowingArray.get !bag index in
      match aty, v.(arri) with
	| None,  _ -> raise WrongIndexException
        | _, None -> raise NullPointerException
        | Some aty, Some (c, l) -> 
	  try
	    let aty = lift (level - al) aty in
	    let evd = the_conv_x env aty ty evd in
	    (evd, lift (level - l) c)
          with _ -> raise WrongTypeException
    with Invalid_argument _ -> raise OutOfBoundsException
      | GrowingArray.OutOfBounds -> raise WrongIndexException

  (* HACK SLOW *)
  let remove_all undo index k =
    List.iter (fun rl ->
      rl := List.filter (fun i -> i <> (index, k)) !rl) undo

  let set env evd undo i k ty c = 
    let level = List.length undo in
    let index = ArrayRefFactory.from_coq env evd i in
    let arri = CoqN.from_coq env evd k in
    remove_all undo index arri;
    try
      let ((aty, al), v) = GrowingArray.get !bag index in
      match aty with
        | Some aty -> 
          let aty = lift (level - al) aty in
          let evd = the_conv_x env aty ty evd in
          v.(arri) <- Some (c, level);
          check_context undo index arri v;
          evd
        | None -> raise WrongTypeException
    with Invalid_argument _ -> raise OutOfBoundsException
      | GrowingArray.OutOfBounds -> raise WrongIndexException
      | _ -> raise WrongTypeException

  let invalidate (index, k) =
    let ((ty, i), v) = GrowingArray.get !bag index in
    if k < 0 then
      GrowingArray.set !bag index ((None, i), v)
    else
      v.(k) <- None
    
end


type data = Val of (evar_map * Evd.ExistentialSet.t * constr) 
	    | Err of (evar_map * Evd.ExistentialSet.t * constr)

let (>>=) v g =
  match v with
    | Val v' -> g v'
    | _ -> v

let return s es t = Val (s, es, t)

let fail s es t = Err (s, es, t)
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
    | Rel k    ->
        if k<=depth then c
        else if k = depth+n then
          lift depth t
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


let dest_Case (env, sigma) t_type t =
  let nil = Constr.mkConstr "Coq.Init.Datatypes.nil" in
  let cons = Constr.mkConstr "Coq.Init.Datatypes.cons" in
  let mkCase = MtacNames.mkConstr "mkCase" in
  let dyn = MtacNames.mkConstr "dyn" in
  let mkDyn = MtacNames.mkConstr "Dyn" in
  try
    let t = whd_betadeltaiota env sigma t in
    let (info, return_type, discriminant, branches) = Term.destCase t in
    let branch_dyns = Array.fold_left (
      fun l t -> 
        let dyn_type = Retyping.get_type_of env sigma t in
        Term.applist (Lazy.force cons, [dyn; Term.applist (mkDyn, [dyn_type; t]); l])
      ) (Lazy.force nil) branches in
    let ind_type = Retyping.get_type_of env sigma discriminant in
    let return_type_type = Retyping.get_type_of env sigma return_type in
    (* (sigma, (Term.applist(mkCase, [t_type; t; ind_type; discriminant; branch_dyns]))) *)
    (sigma, (Term.applist(mkCase, 
      [ind_type; discriminant; t_type;
       Term.applist(mkDyn, [return_type_type; return_type]); 
       branch_dyns
      ])
      )
      )
  with
   | Not_found -> 
        Exceptions.raise "Something specific went wrong. TODO: find out what!"
   | _ -> 
        Exceptions.raise "Something not so specific went wrong."

let make_Case (env, sigma) case =
  let map = Constr.mkConstr "List.map" in
  let elem = MtacNames.mkConstr "elem" in
  let mkDyn = MtacNames.mkConstr "Dyn" in
  let case_ind = MtacNames.mkConstr "case_ind" in
  let case_val = MtacNames.mkConstr "case_val" in
  let case_type = MtacNames.mkConstr "case_type" in
  let case_return = MtacNames.mkConstr "case_return" in
  let case_branches = MtacNames.mkConstr "case_branches" in
  let repr_ind = Term.applist(case_ind, [case]) in
  let repr_val = Term.applist(case_val, [case]) in
  let repr_val_red = whd_betadeltaiota env sigma repr_val in
  let repr_type = Term.applist(case_type, [case]) in
  let repr_return = Term.applist(case_return, [case]) in
  let repr_return_unpack = Term.applist(elem, [repr_return]) in
  let repr_return_red = whd_betadeltaiota env sigma repr_return_unpack in
  let repr_branches = Term.applist(case_branches, [case]) in
  let repr_branches_list = CoqList.from_coq (env, sigma) repr_branches in
  let repr_branches_dyns = 
      List.map (fun t -> Term.applist(elem, [t])) repr_branches_list in
  let repr_branches_red =       
    List.map (fun t -> whd_betadeltaiota env sigma t) repr_branches_dyns in
  let t_type, l = Term.decompose_app (whd_betadeltaiota env sigma repr_ind) in
  if Term.isInd t_type then
    match Term.kind_of_term t_type with
    | Term.Ind (mind, ind_i) -> 
      let mbody = Environ.lookup_mind mind env in
      let ind = Array.get mbody.mind_packets ind_i in
      let case_info = Inductiveops.make_case_info env (mind, ind_i)
      Term.LetPatternStyle in
      let match_term = Term.mkCase (case_info, repr_return_red, repr_val_red,
      Array.of_list (List.rev repr_branches_red)) in
      let match_type = Retyping.get_type_of env sigma match_term in
      (sigma, Term.applist(mkDyn, [match_type;  match_term]))
    | _ -> assert false
  else
    Exceptions.raise "case_type is not an inductive type"


let get_Constrs (env, sigma) t =
  let t_type, args = Term.decompose_app (whd_betadeltaiota env sigma t) in
  if Term.isInd t_type then
    match Term.kind_of_term t_type with
    | Term.Ind (mind, ind_i) -> 
      let mbody = Environ.lookup_mind mind env in
      let ind = Array.get (mbody.mind_packets) ind_i in
      let dyn = MtacNames.mkConstr "dyn" in
      let mkDyn = MtacNames.mkConstr "Dyn" in
      let l = Array.fold_left 
          (fun l i ->
              let constr = Names.ith_constructor_of_inductive (mind, ind_i) i in
              let coq_constr = Term.applist (mkDyn, [CoqList.makeNil dyn]) in (* what is the sense of this line? it's being shadowed in the next one *)
              let coq_constr = Term.applist (Term.mkConstruct constr, args) in
	      let ty = Retyping.get_type_of env sigma coq_constr in 
              let dyn_constr = Term.applist (mkDyn, [ty; coq_constr]) in
              CoqList.makeCons dyn dyn_constr l 
          )
              (CoqList.makeNil dyn )  
          (* this is just a dirty hack to get the indices of constructors *)
          (Array.mapi (fun i t -> i+1) ind.mind_consnames)
      in  
      (sigma, l)
    | _ -> assert false
  else
    Exceptions.raise "The argument of Mconstrs is not an inductive type"

module Hypotheses = struct

  let ahyp_constr = MtacNames.mkBuilder "ahyp"

  let mkAHyp ty n t = 
    let t = match t with
      | None -> CoqOption.mkNone ty
      | Some t -> CoqOption.mkSome ty t
    in ConstrBuilder.build_app ahyp_constr [|ty; n; t|]

  let mkHypType = MtacNames.mkLazyConstr "Hyp"


  let cons_hyp ty n t renv =
    let hyptype = Lazy.force mkHypType in
    CoqList.makeCons hyptype (mkAHyp ty n t) renv

  let from_coq (env, sigma as ctx) c =
    let fvar = fun c ->
	if Term.isVar c || isRel c then c
	else Exceptions.raise "Not a variable in hypothesis"
    in
    let fdecl = fun d -> CoqOption.from_coq ctx d (fun c->c) in 
    let args = ConstrBuilder.from_coq ahyp_constr ctx c in
    (fvar args.(1), fdecl args.(2), args.(0))

  let from_coq_list (env, sigma as ctx) =
    CoqList.from_coq_conv ctx (from_coq ctx)
      
end

(* It replaces each ii by ci in l = [(i1,c1) ... (in, cn)] in c.
   It throws Not_found if there is a variable not in l *)
let multi_subst l c =
  let rec substrec depth c = match kind_of_term c with
    | Rel k    ->
        if k<=depth then c
        else 
	  List.assoc (k - depth) l
    | _ -> map_constr_with_binders succ substrec depth c in
  substrec 0 c

let rec run' (env, renv, sigma, undo, metas as ctxt) t =
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
	return sigma metas (ReductionStrategy.reduce sigma env (nth 1) (nth 2))

      | 2 -> assert_args 4; (* bind *)
	run' ctxt (nth 2) >>= fun (sigma', metas, v) ->
	let t' = mkApp(nth 3, [|v|]) in
	run' (env, renv, sigma', undo, metas) t'

      | 3 -> assert_args 3; (* try *)
	begin
	match run' ctxt (nth 1) with
	  | Val (sigma', metas, v) -> return sigma' metas v
	  | Err (sigma', metas, i) -> 
            let t' = mkApp(nth 2, [|i|]) in
            run' (env, renv, sigma', undo, metas) t'
	end

      | 4 -> assert_args 2; (* raise *)
	fail sigma metas (List.nth args 1)

      | 5 -> assert_args 6; (* fix1 *)
	let a, b, s, i, f, x = nth 0, nth 1, nth 2, nth 3, nth 4, nth 5 in
	run_fix ctxt h [|a|] b s i f [|x|]

      | 6 -> assert_args 8; (* fix 2 *)
	let a1, a2, b, s, i, f, x1, x2 = 
	  nth 0, nth 1, nth 2, nth 3, nth 4, nth 5, nth 6, nth 7 in
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
	run' (env, renv, sigma', undo, metas) body

      | 11 -> assert_args 1; (* print *)
	let s = nth 0 in
	print env sigma s;
	return sigma metas (Lazy.force CoqUnit.mkTT)

      | 12 -> assert_args 3; (* nu *)
	let a, f = nth 0, nth 2 in
	let fx = mkApp(lift 1 f, [|mkRel 1|]) in
	let renv = lift 1 renv in
        let ur = ref [] in
        begin
	  let env = push_rel (Anonymous, None, a) env in
	  let renv = Hypotheses.cons_hyp a (mkRel 1) None renv in
	match run' (env, renv, sigma, (ur :: undo), metas) fx with
          | Val (sigma', metas, e) ->
            clean !ur;
	    if Intset.mem 1 (free_rels e) then
              Exceptions.raise Exceptions.error_param
	    else
	      return sigma' metas (pop e)
          | Err (sigma', metas, e) -> 
            clean !ur;
	    if Intset.mem 1 (free_rels e) then
              Exceptions.raise Exceptions.error_param
	    else
	      fail sigma' metas (pop e)
        end

      | 13 -> assert_args 2; (* is_param *)
	let e = whd_betadeltaiota env sigma (nth 1) in
	if isRel e then
	  return sigma metas (Lazy.force CoqBool.mkTrue)
	else
	  return sigma metas (Lazy.force CoqBool.mkFalse)

      | 14 -> assert_args 4; (* abs *)
        let a, p, x, y = nth 0, nth 1, nth 2, nth 3 in
        abs env sigma metas a p x y false

      | 15 -> assert_args 4; (* abs_eq *)
        let a, p, x, y = nth 0, nth 1, nth 2, nth 3 in
        abs env sigma metas a p x y true

      | 16 -> assert_args 1; (* evar *)
	let t = nth 0 in
	let (sigma', ev) = Evarutil.new_evar sigma env t in
	return sigma' (ExistentialSet.add (fst (destEvar ev)) metas) ev

      | 17 -> assert_args 2; (* is_evar *)
	let e = whd_betadeltaiota env sigma (nth 1) in
	if isEvar e then
	  return sigma metas (Lazy.force CoqBool.mkTrue)
	else
	  return sigma metas (Lazy.force CoqBool.mkFalse)

      | 18 -> assert_args 3; (* hash *)
        return sigma metas (hash ctxt (nth 1) (nth 2))

      | 19 -> assert_args 4; (* nu_let *)
	let a, t, f = nth 0, nth 2, nth 3 in
	let fx = mkApp(lift 1 f, [|mkRel 1;CoqEq.mkAppEqRefl a (mkRel 1)|]) in
	let renv = lift 1 renv in
        let ur = ref [] in
        begin
	  let env = push_rel (Anonymous, Some t, a) env in
	  let renv = Hypotheses.cons_hyp a (mkRel 1) (Some t) renv in
	match run' (env, renv, sigma, (ur :: undo), metas) fx with
          | Val (sigma', metas, e) ->
            clean !ur;
	    return sigma' metas (mkLetIn (Anonymous, t, a, e))
          | Err (sigma', metas, e) -> 
            clean !ur;
	    if Intset.mem 1 (free_rels e) then
              Exceptions.raise Exceptions.error_param
	    else
	      fail sigma' metas (pop e)
        end

      | 20 -> assert_args 0; (* solve_typeclasses *)
	let evd' = Typeclasses.resolve_typeclasses ~fail:false env sigma in
	return evd' metas (Lazy.force CoqUnit.mkTT)
	
      | 21 -> assert_args 3; (* new_array *)
	let ty, n, c = nth 0, nth 1, nth 2 in
	let a = ArrayRefs.new_array env sigma undo ty n c in
	return sigma metas a

      | 22 -> assert_args 3; (* get *)
	let ty, a, i = nth 0, nth 1, nth 2 in
	begin
	try
	  let (sigma, e) = ArrayRefs.get env sigma undo a ty i in
	  return sigma metas e
	with ArrayRefs.NullPointerException ->
	  fail sigma metas (Lazy.force Exceptions.mkNullPointer)
	  | ArrayRefs.OutOfBoundsException ->
	  fail sigma metas (Lazy.force Exceptions.mkOutOfBounds)
	  | ArrayRefs.WrongTypeException ->
	    Exceptions.raise "Wrong type!"
	  | ArrayRefs.WrongIndexException ->
	    Exceptions.raise "Wrong array!"
	end

      | 23 -> assert_args 4; (* set *)
	let ty, a, i, c = nth 0, nth 1, nth 2, nth 3 in
	begin
	try 
	  let sigma = ArrayRefs.set env sigma undo a i ty c in
 	  return sigma metas (Lazy.force CoqUnit.mkTT)
	with ArrayRefs.OutOfBoundsException ->
	  fail sigma metas (Lazy.force Exceptions.mkOutOfBounds)
	  | ArrayRefs.WrongTypeException ->
	    Exceptions.raise "Wrong type!"
	  | ArrayRefs.WrongIndexException ->
	    Exceptions.raise "Wrong array!"
	end

      | 24 -> assert_args 2; (* print term *)
        let t = nth 1 in
        print_term t;
	return sigma metas (Lazy.force CoqUnit.mkTT)

      | 25 -> (* hypotheses *)
	return sigma metas renv

  | 26 -> (* dest case *) 
    let t_type = nth 0 in
    let t = nth 1 in
    let (sigma', case) = dest_Case (env, sigma) t_type t in
    return sigma' metas case

  | 27 -> (* get constrs *) 
    let t = nth 1 in
    let (sigma', constrs) = get_Constrs (env, sigma) t in
    return sigma' metas constrs

  | 28 -> (* make case *) 
    let case = nth 0 in
    let (sigma', case) = make_Case (env, sigma) case in
    return sigma' metas case

  | 29 -> (* Cevar *)
    let ty, hyp = nth 0, nth 1 in
    cvar (env, sigma, metas) ty hyp

      | _ ->
	Exceptions.raise "I have no idea what is this construct of T that you have here"

and cvar (env, sigma, metas) ty hyp =
  let hyp = Hypotheses.from_coq_list (env, sigma) hyp in
  let check_vars e t vars = Idset.subset (Termops.collect_vars t) vars &&
    if Option.has_some e then 
      Idset.subset (Termops.collect_vars (Option.get e)) vars
    else true
  in
  let _, _, subs, env' = List.fold_right (fun (i, e, t) (avoid, avoids, subs, env') -> 
    if isRel i then
      let n = destRel i in
      let na, _, _ = List.nth (rel_context env) (n-1) in
      let id = Namegen.next_name_away na avoid in
      let e = try Option.map (multi_subst subs) e with Not_found -> Exceptions.raise "Not well-formed hypotheses" in
      let t = try multi_subst subs t with Not_found -> Exceptions.raise "Not well-formed hypotheses" in
      let b = check_vars e t avoids in
      let d = (id, e, t) in
      if b then 
	(id::avoid, Idset.add id avoids, (n, mkVar id) :: subs, push_named d env')
      else
	Exceptions.raise "Not well-formed hypotheses"
    else
      let id = destVar i in
      if check_vars e t avoids then
	(id::avoid, Idset.add id avoids, subs, push_named (id, e, t) env')
      else
	Exceptions.raise "Not well-formed hypotheses"
  ) hyp ([], Idset.empty, [], empty_env)
  in
  let vars = List.map (fun (v, _, _)->v) hyp in
  try 
    if Util.list_distinct vars then
      let evi = Evd.make_evar (Environ.named_context_val env') (multi_subst subs ty) in
      let e = new_untyped_evar () in
      let sigma = Evd.add sigma e evi in
      return sigma metas (mkEvar (e, Array.of_list vars))
    else
      Exceptions.raise "Duplicated variable in hypotheses"
  with Not_found -> 
    Exceptions.raise "Hypothesis not found"


and abs env sigma metas a p x y eq_proof =
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
            return sigma metas (CoqSigT.mkAppExistT ex_a ex_p ex_x ex_px)
          else
            return sigma metas t
        with AbstractingArrayType ->
          Exceptions.raise Exceptions.error_abs_ref          
      else
        Exceptions.raise Exceptions.error_abs_env
    else
      Exceptions.raise Exceptions.error_abs_type
  else
    Exceptions.raise Exceptions.error_abs

and clean =
  List.iter (fun i -> ArrayRefs.invalidate i)
    
and run_fix (env, renv, sigma, _, _ as ctxt) h a b s i f x =
  let fixf = mkApp(h, Array.append a [|b;s;i;f|]) in
  let c = mkApp (f, Array.append [| fixf|] x) in
  run' ctxt c

and hash (env, renv, sigma, undo, metas) c size =
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

let clean_unused_metas sigma metas term =
  let rec rem (term : constr) (metas : Evd.ExistentialSet.t) =
    let fms = Evd.collect_evars term in
    let metas = Evd.ExistentialSet.diff metas fms in
    Evd.ExistentialSet.fold (fun ev metas ->
      let ev_info = Evd.find sigma ev  in
      let metas = rem (Evd.evar_concl ev_info) metas in
      let metas = List.fold_right (fun (_, body, ty) metas ->
	let metas = rem ty metas in
	match body with
	  | None -> metas
	  | Some v -> rem v metas) (Evd.evar_context ev_info) metas in
      match Evd.evar_body ev_info with
	| Evar_empty -> metas
	| Evar_defined b -> rem b metas
    ) fms metas
  in 
  let metas = rem term metas in
  (* remove all the reminding metas *)
  Evd.ExistentialSet.fold (fun ev sigma -> Evd.remove sigma ev) metas sigma

let build_hypotheses env =
  let renv = List.mapi (fun n (_, t, ty) -> (mkRel (n+1), t, ty)) (rel_context env)
    @ List.rev (List.map (fun (n, t, ty) -> (mkVar n, t, ty)) (named_context env))
  in (* [H : x > 0, x : nat] *)
  let rec build env =
    match env with
      | [] -> CoqList.makeNil (Lazy.force Hypotheses.mkHypType)
      | (n, t, ty) :: env -> Hypotheses.cons_hyp ty n t (build env)
  in 
  build renv

let run (env, sigma) t  = 
  let _ = ArrayRefs.clean () in
  let renv = build_hypotheses env in
  match run' (env, renv, sigma, [], Evd.ExistentialSet.empty) (nf_evar sigma t) with
    | Err i -> 
      Err i
    | Val (sigma', metas, v) -> 
      let sigma' = clean_unused_metas sigma' metas v in
      Val (sigma', Evd.ExistentialSet.empty, nf_evar sigma' v)


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
    | Val (evmap, _, e) ->
      evdref := evmap ;
      let r = { uj_val = e; uj_type = t } in
      coerce_to_tycon loc env evdref r tycon
    | Err (evmap, _, e) -> 
      evdref := evmap ;
      Pretype_errors.error_user_exception loc env !evdref e

let munify_run env evd f = 
  match run (env, evd) f with
    | Val (sigma, _, v) -> Some (sigma, v)
    | _ -> None

let _ = Munify.set_run munify_run
let _ = Munify.set_lift_constr (MtacNames.mkLazyConstr "lift")
let _ = Munify.set_run_cs (lazy (MtacNames.mkConstr "value", 
			         MtacNames.mkConstr "exec_def"))
