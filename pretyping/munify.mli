open Term

val unify : ?conv_t:Evd.conv_pb ->
  Names.transparent_state ->
  Environ.env ->
  Evd.evar_map -> Term.types -> Term.types -> bool * Evd.evar_map

val unify_evar_conv : ?conv_t:Evd.conv_pb ->
  Names.transparent_state ->
  Environ.env ->
  Evd.evar_map -> Term.types -> Term.types -> Evd.evar_map * bool


val unfold_value : Names.transparent_state ->
  Environ.env -> Evd.evar_map -> 
  Term.constr -> Term.constr

val set_run : (Environ.env -> Evd.evar_map -> Term.constr -> 
  (Evd.evar_map * Term.constr) option) -> unit

val set_lift_constr : constr Lazy.t -> unit


(* DEBUG *)
val id_substitution : Sign.named_context -> Term.constr array

val find_unique : ('a -> bool) -> ('a -> 'b) -> 'b -> 'a list -> int option
  
val intersect : Term.constr array -> Term.constr array -> int list option

val invert :
  int list Util.Intmap.t ref ->
  (Names.identifier * 'a * 'b) list ->
  Term.constr ->
  Term.types list -> Term.types list -> Term.constr option

val fill_lambdas_invert_types :
  int list Util.Intmap.t ref ->
  Environ.env ->
  Evd.evar_map ->
  (Names.identifier * 'a * 'b) list ->
  Term.constr ->
  Term.types list -> Term.types list -> Term.constr option

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

val one_is_meta : Names.transparent_state ->
  Evd.conv_pb -> Environ.env ->
  Evd.evar_map -> Term.constr * Term.types list ->
  Term.constr * Term.types list -> bool * Evd.evar_map

val is_variable_subs : Term.types array -> bool

val is_variable_args : Term.types list -> bool
