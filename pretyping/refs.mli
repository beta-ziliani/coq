
type loc = int

val isArrRef : Term.constr -> bool

exception NotALocation

val to_coq : loc -> Term.constr

val from_coq : Environ.env -> Evd.evar_map -> Term.constr -> loc

val clean : unit -> unit

val used : unit -> bool

val new_array : Environ.env -> Evd.evar_map -> (int * int) list ref list 
  -> Term.types -> Term.constr -> Term.constr -> Term.constr

exception NullPointerException

exception OutOfBoundsException

val get : Environ.env -> Evd.evar_map -> (int * int) list ref list -> 
  Term.constr -> Term.constr -> Term.constr

val set  : Environ.env -> Evd.evar_map -> (int * int) list ref list -> 
  Term.constr -> Term.constr -> Term.constr -> unit

val length : Environ.env -> Evd.evar_map -> Term.constr -> Term.constr
  
val invalidate : (int * int) -> unit

val type_of : Environ.env -> Evd.evar_map -> Term.constr -> Term.types
