open Term

(* DEBUG *)
val id_substitution : Sign.named_context -> Term.constr array

val find_unique : ('a -> bool) -> ('a -> 'b) -> 'b -> 'a list -> int option
	
val intersect : Term.constr array -> Term.constr array -> int list option

val invert :  (Names.identifier * 'a * 'b) list ->
           Term.constr ->
           Term.types list -> Term.types list -> Term.constr option

val fill_lambdas : Environ.env ->
           Evd.evar_map -> Term.constr list -> Term.constr -> Term.constr

val unify : ?conv_t:Evd.conv_pb ->
           Names.transparent_state ->
           Environ.env ->
           Evd.evar_map -> Term.types -> Term.types -> bool * Evd.evar_map

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
