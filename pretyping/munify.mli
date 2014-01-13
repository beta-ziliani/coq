open Term

val unify : ?conv_t:Evd.conv_pb ->
           Names.transparent_state ->
           Environ.env ->
           Evd.evar_map -> Term.types -> Term.types -> bool * Evd.evar_map

val unify_evar_conv : ?conv_t:Evd.conv_pb ->
           Names.transparent_state ->
           Environ.env ->
           Evd.evar_map -> Term.types -> Term.types -> Evd.evar_map * bool


(* DEBUG *)
val id_substitution : Sign.named_context -> Term.constr array

val find_unique : ('a -> bool) -> ('a -> 'b) -> 'b -> 'a list -> int option
	
val intersect : Term.constr array -> Term.constr array -> int list option

val invert :  (Names.identifier * 'a * 'b) list ->
           Term.constr ->
           Term.types list -> Term.types list -> Term.constr option

val fill_lambdas : Environ.env ->
           Evd.evar_map -> Term.constr list -> Term.constr -> Term.constr

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

val ise_list2 :   'a ->
           ('a -> 'b -> 'c -> bool * 'a) -> 'b list -> 'c list -> bool * 'a
