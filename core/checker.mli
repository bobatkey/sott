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
  | Term_is_not_a_type of Location.t
  | Type_mismatch of
      { loc         : Location.t
      ; ctxt        : Context.t
      ; computed_ty : Syntax.term
      ; expected_ty : Syntax.term }
  | Term_is_not_a_function of Location.t
  | Term_is_not_a_pair of Location.t
  | Term_is_not_a_small_type of Location.t
  | Term_is_not_a_natural of Location.t
  | Term_is_not_an_equiv_class of Location.t
  | Term_is_not_a_valid_tag of Location.t * Syntax.tag_set
  | Term_is_not_a_type_equality of Location.t
  | Term_is_not_a_term_equality of Location.t
  | Types_not_equal of
      { loc  : Location.t
      ; ctxt : Context.t
      ; ty1  : Syntax.term
      ; ty2  : Syntax.term }
  | Terms_not_equal of
      { loc  : Location.t
      ; ctxt : Context.t
      ; tm1  : Syntax.term
      ; tm2  : Syntax.term
      ; ty   : Syntax.term
      }
  | BadSubst of
      { loc  : Location.t
      ; ctxt : Context.t
      ; desired_eq : Syntax.term * Syntax.term
      ; proved_eq  : Syntax.term * Syntax.term
      }
  | BadFunext of
      { loc  : Location.t
      ; ctxt : Context.t
      ; ty   : Syntax.term
      }
  | BadCoherence of
      { loc  : Location.t
      ; ctxt : Context.t
      ; ty   : Syntax.term
      }
  | BadSameClass of
      { loc  : Location.t
      ; ctxt : Context.t
      ; ty   : Syntax.term
      }
  | VarNotFound of Location.t * string
  | BadApplication of
      { loc     : Location.t
      ; arg_loc : Location.t
      ; ctxt    : Context.t
      ; ty      : Syntax.term }
  | BadProject of
      { loc    : Location.t
      ; hd_loc : Location.t
      ; ctxt   : Context.t
      ; ty     : Syntax.term }
  | BadNatElim of
      { loc    : Location.t
      ; hd_loc : Location.t
      ; ctxt   : Context.t
      ; ty     : Syntax.term
      }
  | BadQuotElim of
      { loc    : Location.t
      ; hd_loc : Location.t
      ; ctxt   : Context.t
      ; ty     : Syntax.term
      }
  | BadTagElim of
      { loc    : Location.t
      ; hd_loc : Location.t
      ; ctxt   : Context.t
      ; ty     : Syntax.term
      }
  | IncorrectTags of
      { loc         : Location.t
      ; hd_loc      : Location.t
      ; unmatched   : Syntax.tag_set
      ; unmatchable : Syntax.tag_set
      }

val is_type : Context.t -> Syntax.term -> (unit, error_message) result

val has_type : Context.t -> value -> Syntax.term -> (unit, error_message) result
