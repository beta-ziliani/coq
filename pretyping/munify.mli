open Term

val unify : ?conv_t:Evd.conv_pb ->
  Names.transparent_state ->
  Environ.env ->
  Evd.evar_map -> Term.types -> Term.types -> bool * Evd.evar_map

val unify_evar_conv :
  Names.transparent_state ->
  Evarutil.conv_fun

val set_run : (Environ.env -> Evd.evar_map -> Term.constr -> 
  (Evd.evar_map * Term.constr) option) -> unit

val set_lift_constr : constr Lazy.t -> unit


val use_munify : unit -> bool

val set_use_munify : bool -> unit


val get_debug : unit -> bool

val set_debug : bool -> unit

val get_evarconv_for_cs : unit -> bool

(* Doesn't belong here! *)
val try_unfolding : Names.transparent_state -> Environ.env -> Term.constr -> Term.constr


(* DEBUG *)
val id_substitution : Sign.named_context -> Term.constr array

val find_unique : ('a -> bool) -> ('a -> 'b) -> 'b -> 'a list -> int option
  
val intersect : 
  Environ.env ->
  Evd.evar_map ->
  Term.constr array -> Term.constr array -> int list option

val invert :
  int list Util.Intmap.t ref ->
  Evd.evar_map ->
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

type stucked = NotStucked | StuckedLeft | StuckedRight

val try_step :
           ?stuck:stucked ->
           int ->
           Evd.conv_pb ->
           Names.transparent_state ->
           Environ.env ->
           Evd.evar_map ->
           Term.constr * Term.constr list ->
           Term.constr * Term.constr list -> bool * Evd.evar_map

val instantiate' : int ->
  Names.transparent_state ->
  Evd.conv_pb ->
  Environ.env ->
  Evd.evar_map ->
  Evd.evar * Term.types array ->
  Term.types list ->
  Term.constr * Term.types list -> bool * Evd.evar_map

val instantiate : int ->
  Names.transparent_state ->
  Evd.conv_pb ->
  Environ.env ->
  Evd.evar_map ->
  Evd.evar * Term.types array ->
  Term.types list ->
  Term.constr * Term.types list -> bool * Evd.evar_map

val meta_fo : int ->
  Names.transparent_state ->
  Environ.env ->
  Evd.evar_map ->
  Term.existential * Term.types list ->
  Term.constr * Term.types list -> bool * Evd.evar_map

val conv_record : int -> Names.transparent_state ->
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

val one_is_meta : int -> Names.transparent_state ->
  Evd.conv_pb -> Environ.env ->
  Evd.evar_map -> Term.constr * Term.types list ->
  Term.constr * Term.types list -> bool * Evd.evar_map

val is_variable_subs : Term.types array -> bool

val is_variable_args : Term.types list -> bool

val unify' : ?conv_t:Evd.conv_pb -> int ->
  Names.transparent_state ->
  Environ.env ->
  Evd.evar_map -> (Term.constr * Term.constr list) -> (Term.constr * Term.constr list) -> bool * Evd.evar_map

val should_try_fo : Term.constr list -> (Term.constr * Term.constr list) -> bool

val debug_eq : Evd.evar_map -> Environ.env -> Term.constr * Term.constr list -> Term.constr * Term.constr list  -> int -> unit

val debug_str : string -> int -> unit

val is_stuck : Names.transparent_state -> Environ.env -> Evd.evar_map ->
  Term.constr * Term.constr list -> bool
