(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2012     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(***********************************************************************)
(*                                                                     *)
(*      This module defines proof facilities relevant to the           *)
(*      toplevel. In particular it defines the global proof            *)
(*      environment.                                                   *)
(*                                                                     *)
(***********************************************************************)

open Util
open Pp
open Names
open Util

(*** Proof Modes ***)

(* Type of proof modes :
    - A function [set] to set it *from standard mode*
    - A function [reset] to reset the *standard mode* from it *)
type proof_mode = {
  name : string ;
  set : unit -> unit ;
  reset : unit -> unit
}

let proof_modes = Hashtbl.create 6
let find_proof_mode n =
  try Hashtbl.find proof_modes n
  with Not_found ->
    Errors.error (Format.sprintf "No proof mode named \"%s\"." n)

let register_proof_mode ({name = n} as m) =
  Hashtbl.add proof_modes n (Ephemeron.create m)

(* initial mode: standard mode *)
let standard = { name = "No" ; set = (fun ()->()) ; reset = (fun () -> ()) }
let _ = register_proof_mode standard

(* Default proof mode, to be set at the beginning of proofs. *)
let default_proof_mode = ref (find_proof_mode "No")

let _ =
  Goptions.declare_string_option {Goptions.
    optsync = true ;
    optdepr = false;
    optname = "default proof mode" ;
    optkey = ["Default";"Proof";"Mode"] ;
    optread = begin fun () ->
      (Ephemeron.default !default_proof_mode standard).name
    end;
    optwrite = begin fun n ->
      default_proof_mode := find_proof_mode n
    end
  }

(*** Proof Global Environment ***)

(* Extra info on proofs. *)
type lemma_possible_guards = int list list

type proof_object = {
  id : Names.Id.t;
  entries : Entries.definition_entry list;
  persistence : Decl_kinds.goal_kind;
}

type proof_ending =
  | Admitted
  | Proved of Vernacexpr.opacity_flag *
             (Vernacexpr.lident * Decl_kinds.theorem_kind option) option *
              proof_object
type proof_terminator = proof_ending -> unit
type closed_proof = proof_object * proof_terminator

type pstate = {
  pid : Id.t;
  terminator : proof_terminator Ephemeron.key;
  endline_tactic : Tacexpr.raw_tactic_expr option;
  section_vars : Context.section_context option;
  proof : Proof.proof;
  strength : Decl_kinds.goal_kind;
  mode : proof_mode Ephemeron.key;
}

(* The head of [!pstates] is the actual current proof, the other ones are
   to be resumed when the current proof is closed or aborted. *)
let pstates = ref ([] : pstate list)

(* Current proof_mode, for bookkeeping *)
let current_proof_mode = ref !default_proof_mode

(* combinators for proof modes *)
let update_proof_mode () =
  match !pstates with
  | { mode = m } :: _ ->
      Ephemeron.iter_opt !current_proof_mode (fun x -> x.reset ());
      current_proof_mode := m;
      Ephemeron.iter_opt !current_proof_mode (fun x -> x.set ())
  | _ ->
      Ephemeron.iter_opt !current_proof_mode (fun x -> x.reset ());
      current_proof_mode := find_proof_mode "No"

(* combinators for the current_proof lists *)
let push a l = l := a::!l;
  update_proof_mode ()

exception NoSuchProof
let _ = Errors.register_handler begin function
  | NoSuchProof -> Errors.error "No such proof."
  | _ -> raise Errors.Unhandled
end
let extract id l =
  let rec aux = function
    | ({pid = id' } as np)::l when Id.equal id id' -> (np,l)
    | np::l -> let (np', l) = aux l in (np' , np::l)
    | [] -> raise NoSuchProof
  in
  let (np,l') = aux !l in
  l := l';
  update_proof_mode ();
  np

exception NoCurrentProof
let _ = Errors.register_handler begin function
  | NoCurrentProof -> Errors.error "No focused proof (No proof-editing in progress)."
  | _ -> raise Errors.Unhandled
end
let extract_top l =
  match !l with
  | np::l' -> l := l' ; update_proof_mode (); np
  | [] -> raise NoCurrentProof

(* combinators for the proof_info map *)
let add id info m =
  m := Id.Map.add id info !m
let remove id m =
  m := Id.Map.remove id !m

(*** Proof Global manipulation ***)

let get_all_proof_names () =
  List.map (function { pid = id } -> id) !pstates

let cur_pstate () =
  match !pstates with
  | np::_ -> np
  | [] -> raise NoCurrentProof

let give_me_the_proof () = (cur_pstate ()).proof
let get_current_proof_name () = (cur_pstate ()).pid

let interp_tac = ref (fun _ -> assert false)
let set_interp_tac f = interp_tac := f

let with_current_proof f =
  match !pstates with
  | [] -> raise NoCurrentProof
  | p :: rest ->
      let et =
        match p.endline_tactic with
        | None -> Proofview.tclUNIT ()
        | Some tac -> !interp_tac tac in
      let (newpr,status) = f et p.proof in
      let p = { p with proof = newpr } in
      pstates := p :: rest;
      status
let simple_with_current_proof f =
  ignore (with_current_proof (fun t p -> f t p , true))

(* Sets the tactic to be used when a tactic line is closed with [...] *)
let set_endline_tactic tac =
  match !pstates with
  | [] -> raise NoCurrentProof
  | p :: rest -> pstates := { p with endline_tactic = Some tac } :: rest

(* spiwack: it might be considered to move error messages away.
    Or else to remove special exceptions from Proof_global.
    Arguments for the former: there is no reason Proof_global is only
    accessed directly through vernacular commands. Error message should be
   pushed to external layers, and so we should be able to have a finer
   control on error message on complex actions. *)
let msg_proofs () =
  match get_all_proof_names () with
    | [] -> (spc () ++ str"(No proof-editing in progress).")
    | l ->  (str"." ++ fnl () ++ str"Proofs currently edited:" ++ spc () ++
               (pr_sequence Nameops.pr_id l) ++ str".")

let there_is_a_proof () = not (List.is_empty !pstates)
let there_are_pending_proofs () = there_is_a_proof ()
let check_no_pending_proof () =
  if not (there_are_pending_proofs ()) then
    ()
  else begin
    Errors.error (Pp.string_of_ppcmds
      (str"Proof editing in progress" ++ msg_proofs () ++ fnl() ++
       str"Use \"Abort All\" first or complete proof(s)."))
  end

let discard_gen id =
  pstates := List.filter (fun { pid = id' } -> not (Id.equal id id')) !pstates

let discard (loc,id) =
  let n = List.length !pstates in
  discard_gen id;
  if Int.equal (List.length !pstates) n then
    Errors.user_err_loc
      (loc,"Pfedit.delete_proof",str"No such proof" ++ msg_proofs ())

let discard_current () =
  if List.is_empty !pstates then raise NoCurrentProof else pstates := List.tl !pstates

let discard_all () = pstates := []

(* [set_proof_mode] sets the proof mode to be used after it's called. It is
    typically called by the Proof Mode command. *)
let set_proof_mode m id =
  pstates :=
    List.map (function { pid = id' } as p ->
      if Id.equal id' id then { p with mode = m } else p) !pstates;
  update_proof_mode ()

let set_proof_mode mn =
  set_proof_mode (find_proof_mode mn) (get_current_proof_name ())

let activate_proof_mode mode =
  Ephemeron.iter_opt (find_proof_mode mode) (fun x -> x.set ())
let disactivate_proof_mode mode =
  Ephemeron.iter_opt (find_proof_mode mode) (fun x -> x.reset ())

exception AlreadyExists
let _ = Errors.register_handler begin function
  | AlreadyExists -> Errors.error "Already editing something of that name."
  | _ -> raise Errors.Unhandled
end

(** [start_proof id str goals terminator] starts a proof of name [id]
    with goals [goals] (a list of pairs of environment and
    conclusion); [str] describes what kind of theorem/definition this
    is (spiwack: for potential printing, I believe is used only by
    closing commands and the xml plugin); [terminator] is used at the
    end of the proof to close the proof. *)
let start_proof id str goals terminator =
  let initial_state = {
    pid = id;
    terminator = Ephemeron.create terminator;
    proof = Proof.start Evd.empty goals;
    endline_tactic = None;
    section_vars = None;
    strength = str;
    mode = find_proof_mode "No" } in
  push initial_state pstates

let start_dependent_proof id str goals terminator =
  let initial_state = {
    pid = id;
    terminator = Ephemeron.create terminator;
    proof = Proof.dependent_start Evd.empty goals;
    endline_tactic = None;
    section_vars = None;
    strength = str;
    mode = find_proof_mode "No" } in
  push initial_state pstates

let get_used_variables () = (cur_pstate ()).section_vars

let set_used_variables l =
  let env = Global.env () in
  let ids = List.fold_right Id.Set.add l Id.Set.empty in
  let ctx = Environ.keep_hyps env ids in
  match !pstates with
  | [] -> raise NoCurrentProof
  | p :: rest ->
      if not (Option.is_empty p.section_vars) then
        Errors.error "Used section variables can be declared only once";
      pstates := { p with section_vars = Some ctx} :: rest

let get_open_goals () =
  let gl, gll, shelf , _ , _ = Proof.proof (cur_pstate ()).proof in
  List.length gl +
    List.fold_left (+) 0
    (List.map (fun (l1,l2) -> List.length l1 + List.length l2) gll) +
    List.length shelf

let close_proof ?feedback_id ~now fpl =
  let { pid; section_vars; strength; proof; terminator } = cur_pstate () in
  let initial_goals = Proof.initial_goals proof in
  let entries =
    Future.map2 (fun p (c, t) -> { Entries.
      const_entry_body = p;
      const_entry_secctx = section_vars;
      const_entry_feedback = feedback_id;
      const_entry_type  = Some t;
      const_entry_inline_code = false;
      const_entry_opaque = true })
    fpl initial_goals in
  if now then
    List.iter (fun x ->ignore(Future.force x.Entries.const_entry_body)) entries;
  { id = pid; entries = entries; persistence = strength },
  Ephemeron.get terminator

let return_proof () =
  let { proof } = cur_pstate () in
  let initial_goals = Proof.initial_goals proof in
  let evd =
    let error s = raise (Errors.UserError("last tactic before Qed",s)) in
    try Proof.return proof with
    | Proof.UnfinishedProof ->
        error(str"Attempt to save an incomplete proof")
    | Proof.HasShelvedGoals ->
        error(str"Attempt to save a proof with shelved goals")
    | Proof.HasGivenUpGoals ->
        error(str"Attempt to save a proof with given up goals")
    | Proof.HasUnresolvedEvar->
        error(str"Attempt to save a proof with existential " ++
              str"variables still non-instantiated") in
  let eff = Evd.eval_side_effects evd in
  (** ppedrot: FIXME, this is surely wrong. There is no reason to duplicate
      side-effects... This may explain why one need to uniquize side-effects
      thereafter... *)
  List.map (fun (c, _) -> (Evarutil.nf_evar evd c, eff)) initial_goals

let close_future_proof ~feedback_id proof =
  close_proof ~feedback_id ~now:false proof
let close_proof fix_exn =
  close_proof ~now:true (Future.from_val ~fix_exn (return_proof ()))

(** Gets the current terminator without checking that the proof has
    been completed. Useful for the likes of [Admitted]. *)
let get_terminator () = Ephemeron.get ( cur_pstate() ).terminator
let set_terminator hook =
  match !pstates with
  | [] -> raise NoCurrentProof
  | p :: ps -> pstates := { p with terminator = Ephemeron.create hook } :: ps

(**********************************************************)
(*                                                        *)
(*                                 Bullets                *)
(*                                                        *)
(**********************************************************)

module Bullet = struct

  type t = Vernacexpr.bullet

  let bullet_eq b1 b2 = match b1, b2 with
  | Vernacexpr.Dash, Vernacexpr.Dash -> true
  | Vernacexpr.Star, Vernacexpr.Star -> true
  | Vernacexpr.Plus, Vernacexpr.Plus -> true
  | _ -> false

  type behavior = {
    name : string;
    put : Proof.proof -> t -> Proof.proof
  }

  let behaviors = Hashtbl.create 4
  let register_behavior b = Hashtbl.add behaviors b.name b

  (*** initial modes ***)
  let none = {
    name = "None";
    put = fun x _ -> x
  }
  let _ = register_behavior none

  module Strict = struct
    (* spiwack: we need only one focus kind as we keep a stack of (distinct!) bullets *)
    let bullet_kind = (Proof.new_focus_kind () : t list Proof.focus_kind)
    let bullet_cond = Proof.done_cond ~loose_end:true bullet_kind

    (* spiwack: as it is bullets are reset (locally) by *any* non-bullet focusing command
       experience will tell if this is the right discipline of if we want to be finer and
       reset them only for a choice of bullets. *)
    let get_bullets pr =
      if Proof.is_last_focus bullet_kind pr then
	Proof.get_at_focus bullet_kind pr
      else
	[]

    let has_bullet bul pr =
      let rec has_bullet = function
	| b'::_ when bullet_eq bul b' -> true
	| _::l -> has_bullet l
	| [] -> false
      in
      has_bullet (get_bullets pr)

    (* precondition: the stack is not empty *)
    let pop pr =
      match get_bullets pr with
      | b::_ ->
         let pr = Proof.unfocus bullet_kind pr () in
         pr, b
      | _ -> assert false

    let push b pr =
      Proof.focus bullet_cond (b::get_bullets pr) 1 pr

    let put p bul =
      if has_bullet bul p then
        let rec aux p =
          let p, b = pop p in
          if not (bullet_eq bul b) then aux p else p in
        push bul (aux p)
      else
	push bul p

    let strict = {
      name = "Strict Subproofs";
      put = put
    }
    let _ = register_behavior strict
  end

  (* Current bullet behavior, controled by the option *)
  let current_behavior = ref Strict.strict

  let _ =
    Goptions.declare_string_option {Goptions.
      optsync = true;
      optdepr = false;
      optname = "bullet behavior";
      optkey = ["Bullet";"Behavior"];
      optread = begin fun () ->
	(!current_behavior).name
      end;
      optwrite = begin fun n ->
	current_behavior := Hashtbl.find behaviors n
      end
    }

  let put p b =
    (!current_behavior).put p b
end


(**********************************************************)
(*                                                        *)
(*                     Default goal selector              *)
(*                                                        *)
(**********************************************************)


(* Default goal selector: selector chosen when a tactic is applied
   without an explicit selector. *)
let default_goal_selector = ref (Vernacexpr.SelectNth 1)
let get_default_goal_selector () = !default_goal_selector

let print_goal_selector = function
  | Vernacexpr.SelectAll -> "all"
  | Vernacexpr.SelectNth i -> string_of_int i

let parse_goal_selector = function
  | "all" -> Vernacexpr.SelectAll
  | i ->
      let err_msg = "A selector must be \"all\" or a natural number." in
      begin try
              let i = int_of_string i in
              if i < 0 then Errors.error err_msg;
              Vernacexpr.SelectNth i
        with Failure _ -> Errors.error err_msg
      end

let _ =
  Goptions.declare_string_option {Goptions.
                                  optsync = true ;
                                  optdepr = false;
                                  optname = "default goal selector" ;
                                  optkey = ["Default";"Goal";"Selector"] ;
                                  optread = begin fun () -> print_goal_selector !default_goal_selector end;
                                  optwrite = begin fun n ->
                                    default_goal_selector := parse_goal_selector n
                                  end
                                 }


module V82 = struct
  let get_current_initial_conclusions () =
    let { pid; strength; proof } = cur_pstate () in
    pid, (List.map snd (Proof.initial_goals proof), strength)
end

type state = pstate list
        
let freeze ~marshallable =
  match marshallable with
  | `Yes ->
      Errors.anomaly (Pp.str"full marshalling of proof state not supported")
  | `Shallow -> !pstates
  | `No -> !pstates
let unfreeze s = pstates := s; update_proof_mode ()

