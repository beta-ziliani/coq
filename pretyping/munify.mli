open Term
open Context
open Environ

val unify : ?conv_t:Evd.conv_pb ->
  Names.transparent_state ->
  Environ.env ->
  Evd.evar_map -> Term.types -> Term.types -> bool * Evd.evar_map

val unify_evar_conv : 
  Names.transparent_state ->
  Environ.env ->
  Evd.evar_map -> 
  Evd.conv_pb -> 
  Term.types -> 
  Term.types -> Evarsolve.unification_result


val unfold_value : Names.transparent_state ->
  Environ.env -> Evd.evar_map -> 
  Term.constr -> Term.constr

(* DEBUG *)
val id_substitution : named_context -> Term.constr array

val find_unique : ('a -> bool) -> ('a -> 'b) -> 'b -> 'a list -> int option
  
val intersect : Term.constr array -> Term.constr array -> int list option


val invert :
  int list Evar.Map.t ref ->
  (Names.Id.t * 'a * 'b) list ->
  Term.constr ->
  Term.constr list -> Term.constr list -> Term.constr option

val fill_lambdas_invert_types :
  int list Evar.Map.t ref ->
  Environ.env ->
  Evd.evar_map ->
  (Names.Id.t * 'a * 'b) list ->
  Term.constr ->
  Term.constr list -> Term.constr list -> Term.constr option

val try_step :  Evd.conv_pb ->
  Names.transparent_state ->
  Environ.env ->
  Evd.evar_map ->
  Term.constr * Term.constr list ->
  Term.constr * Term.constr list -> bool * Evd.evar_map

val instantiate' :
  Names.transparent_state ->
  Evd.conv_pb ->
  Environ.env ->
  Evd.evar_map ->
  Evd.evar * Term.types array ->
  Term.types list ->
  Term.constr * Term.types list -> bool * Evd.evar_map

val meta_fo :
  Names.transparent_state ->
  Environ.env ->
  Evd.evar_map ->
  Term.existential * Term.types list ->
  Term.constr * Term.types list -> bool * Evd.evar_map

val conv_record : Names.transparent_state ->
  Environ.env ->
  Evd.evar_map ->
  Term.constr * Term.types list ->
  Term.constr * Term.types list -> bool * Evd.evar_map


val check_conv_record : Term.constr * 'a list ->
  Term.constr * Term.types list ->
  Term.constr * Term.constr list * (Term.constr list * 'a list) *
    (Term.constr list * Term.types list) *
    ('a list * Term.types list) * 'a * (int * Term.constr)

val ise_list2 : Evd.evar_map  ->
  (Evd.evar_map -> Term.constr -> Term.constr -> bool * Evd.evar_map) -> 
  Term.constr list -> Term.constr list -> bool * Evd.evar_map

val debug : Term.constr list -> unit
