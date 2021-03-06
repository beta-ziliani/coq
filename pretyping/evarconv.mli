(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2012     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

open Names
open Term
open Context
open Environ
open Termops
open Reductionops
open Evd
open Locus

(** {4 Unification for type inference. } *)

exception UnableToUnify of evar_map * Pretype_errors.unification_error

(** {6 Main unification algorithm for type inference. } *)

(** returns exception NotUnifiable with best known evar_map if not unifiable *)
val the_conv_x     : ?ts:transparent_state -> env -> constr -> constr -> evar_map -> evar_map
val the_conv_x_leq : ?ts:transparent_state -> env -> constr -> constr -> evar_map -> evar_map

(** The same function resolving evars by side-effect and
   catching the exception *)
val e_conv  : ?ts:transparent_state -> env -> evar_map ref -> constr -> constr -> bool
val e_cumul : ?ts:transparent_state -> env -> evar_map ref -> constr -> constr -> bool

(** {6 Unification heuristics. } *)

(** Try heuristics to solve pending unification problems and to solve
    evars with candidates *)

val consider_remaining_unif_problems : ?ts:transparent_state -> env -> evar_map -> evar_map

(** Check all pending unification problems are solved and raise an
    error otherwise *)

val check_problems_are_solved : evar_map -> unit

(** Check if a canonical structure is applicable *)

val check_conv_record : constr * types Stack.t -> constr * types Stack.t ->
  constr * constr list * (constr Stack.t * constr Stack.t) *
    (constr Stack.t * types Stack.t) *
    (constr Stack.t * types Stack.t) * constr *
    (int * constr)

(** Try to solve problems of the form ?x[args] = c by second-order
    matching, using typing to select occurrences *)

val second_order_matching : transparent_state -> env -> evar_map ->
  existential -> occurrences option list -> constr -> evar_map * bool

(** Declare function to enforce evars resolution by using typing constraints *)

val set_solve_evars : (env -> evar_map ref -> constr -> constr) -> unit

(**/**)
(* For debugging *)
val evar_conv_x : transparent_state ->
  env -> evar_map -> conv_pb -> constr -> constr -> Evarsolve.unification_result
val evar_eqappr_x : ?rhs_is_already_stuck:bool -> transparent_state ->
  env -> evar_map ->
    conv_pb -> state * Cst_stack.t -> state * Cst_stack.t ->
      Evarsolve.unification_result
(**/**)
