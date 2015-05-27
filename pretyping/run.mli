open Term
open Evd
open Environ

type data = Val of (evar_map * Evd.ExistentialSet.t * constr) 
	    | Err of (evar_map * Evd.ExistentialSet.t * constr)

val mkT : unit -> Term.constr

val run : (env * evar_map) -> constr -> data

val pretype_run : 
  (Evarutil.type_constraint -> Environ.env -> Evd.evar_map ref -> 'a -> 'b -> Environ.unsafe_judgment) ->
  (Util.loc -> Environ.env -> Evd.evar_map ref -> Environ.unsafe_judgment -> ('c * Term.types) option -> 'd) ->
  ('c * Term.types) option ->
  Environ.env -> Evd.evar_map ref -> 'a -> Util.loc -> 'b -> 'd


(* debug *)
val run' : (env * constr * evar_map * (int * int) list ref list * Evd.ExistentialSet.t) -> constr -> data
val runmatch' : Environ.env * Evd.evar_map -> 
  Term.constr -> Term.types -> Term.constr -> int -> Evd.evar_map * Term.constr
val clean_unused_metas : Evd.evar_map -> Evd.ExistentialSet.t -> Term.constr -> Evd.evar_map
