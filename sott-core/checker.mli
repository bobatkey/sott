(** The type checker *)

(** Internal representation of checked terms *)
type value

module Context : sig
  type t

  val empty : t

  val extend_with_defn : string -> ty:value -> tm:value -> t -> t
end

module Evaluation : sig
  val eval0 : Context.t -> Syntax.term -> value
end

type error_message =
  | Type_mismatch of { loc : Location.t; ctxt : Context.t; computed_ty : Syntax.term; expected_ty : Syntax.term }
  | Types_not_equal of { loc : Location.t; ctxt : Context.t; ty1 : Syntax.term; ty2 : Syntax.term }
  | Term_is_not_a_type of Location.t
  | Term_mismatch of Location.t * Context.t * Syntax.term * Syntax.term * Syntax.term
  | VarNotFound of Location.t * string
  | BadApplication of { loc : Location.t; arg_loc : Location.t; ctxt : Context.t; ty : Syntax.term }
  | MsgLoc of Location.t * string

val is_type : Context.t -> Syntax.term -> (unit, error_message) result

val has_type : Context.t -> value -> Syntax.term -> (unit, error_message) result
