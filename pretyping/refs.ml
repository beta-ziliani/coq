open Stdlib_constr

(** An array that grows 1.5 times when it gets out of space *) 
module GrowingArray = struct
  type 'a t = 'a array ref * 'a * int ref
  
  let make i t = (ref (Array.make i t), t, ref 0)
  let length g = let (_, _, i) = g in !i
  let get g = let (a, _, _) = g in Array.get !a
  let set g = let (a, _, _) = g in Array.set !a

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

type loc = int

let isArrRef = Term.isMeta

let to_coq n = 
  Term.mkMeta (-n -1)

exception NotALocation

let from_coq env evd c =
  let c = Reductionops.whd_betadeltaiota env evd c in
  if Term.isMeta c && Term.destMeta c < 0 then
    -(Term.destMeta c) -1
  else
    raise NotALocation


let bag = ref (GrowingArray.make 4 (Term.mkProp, [||]))

let clean () = 
  bag := GrowingArray.make 4 (Term.mkProp, [||])

let used () =
  GrowingArray.length !bag > 0

let check_context undo index i arr =
  let size = List.length undo in
  let rec check depth t =
    match Term.kind_of_term t with
      | Term.Rel k ->
        if depth < k && k <= depth + size then (* check if the db index points to the nu context *)
          let rl = List.nth undo (k - depth -1) in
          rl := ((index, i) :: !rl) (* mark this location as 'dirty' *)
        else
          ()
      | _ -> Term.iter_constr_with_binders succ check depth t
  in
  match arr.(i) with 
    | Some (c', _) -> check 0 c' 
    | _ -> ()
      

let new_array evd sigma undo a n c =
  let level = List.length undo in
  let size = CoqN.from_coq evd sigma n in
  let arr = Array.make size (Some (c, level)) in
  GrowingArray.add !bag (a, arr);
  let index = pred (GrowingArray.length !bag) in
  Array.iteri (fun i t -> check_context undo index i arr) arr;
  to_coq index
    
exception NullPointerException
  
exception OutOfBoundsException
  
let get env evd undo i k = 
  let level = List.length undo in
  let index = from_coq env evd i in
  let arri = CoqN.from_coq env evd k in
  let (_, v) = GrowingArray.get !bag index in
  try
    match v.(arri) with
	None -> raise NullPointerException
      | Some (c, l) -> (Term.lift (level - l) c)
  with Invalid_argument _ -> raise OutOfBoundsException
    
  (* HACK SLOW *)
let remove_all undo index k =
  List.iter (fun rl ->
    rl := List.filter (fun i -> i <> (index, k)) !rl) undo
    
let set env evd undo i k c = 
  let level = List.length undo in
  let index = from_coq env evd i in
  let arri = CoqN.from_coq env evd k in
  remove_all undo index arri;
  let (_, v) = GrowingArray.get !bag index in
  try
    v.(arri) <- Some (c, level);
    check_context undo index arri v
  with Invalid_argument _ -> raise OutOfBoundsException

let length env evd i =
  let index = from_coq env evd i in
  let (_, v) = GrowingArray.get !bag index in
  CoqN.to_coq (Array.length v)
    
let invalidate (index, k) =
  let (_, v) = GrowingArray.get !bag index in
  v.(k) <- None
   
let get_array_type = Constr.mkConstr (MtacNames.mtacore_name ^ "." ^ "MyArrayImp.array")

let type_of env evd l =
  let index = from_coq env evd l in
  let (a, _) = GrowingArray.get !bag index in
  Term.mkApp (Lazy.force get_array_type, [|a|])
  
  
