open Term
open Environ
open Evd
open Reduction

val unify : ?conv_pb:conv_pb -> env -> evar_map -> constr -> constr -> (bool * evar_map)