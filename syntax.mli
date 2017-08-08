type 'a binder =
  | B  of string * 'a

type term =
  { term_loc  : Location.t
  ; term_data : term_data
  }

and term_data =
  | Neutral of head * elims

  | Set

  | Pi of term * term binder
  | Lam of term binder

  | Sigma of term * term binder
  | Pair of term * term

  | Bool
  | True
  | False

  | Nat
  | Zero
  | Succ of term

  | TyEq of term * term
  | TmEq of { tm1 : term; ty1 : term; tm2 : term; ty2 : term }

  (* proof constructors *)
  | Subst of { ty_s : term
             ; ty_t : term binder
             ; tm_x : term
             ; tm_y : term
             ; tm_e : term
             }
  | Refl
  | Coh
  | Funext of term binder binder binder

  (* placeholder for an erased proof term; only generated during
     reification. *)
  | Irrel

and head =
  { head_loc  : Location.t
  ; head_data : head_data
  }

and head_data =
  | Bound  of int
  | Free_local of string
  | Free_global of string
  | Coerce of { coercee  : term
              ; src_type : term
              ; tgt_type : term
              ; eq_proof : term
              }

and elims =
  { elims_loc  : Location.t
  ; elims_data : elims_data
  }

and elims_data =
  | Nil
  | App     of elims * term
  | If      of elims * term binder * term * term
  | Project of elims * [`fst | `snd]
  | ElimNat of elims * term binder * term * term binder binder



module Scoping : sig
  val bind : string -> term -> term binder

  val bind2 : string -> string -> term -> term binder binder

  val bind3 : string -> string -> string -> term -> term binder binder binder

  val bind_anon : term -> term binder
end

(** Internal representation of checked terms *)
type value

module Context : sig
  type t

  val empty : t
  val extend_with_defn : string -> ty:value -> tm:value -> t -> t
  val lookup_exn : string -> t -> value * value option
end

module Evaluation : sig
  val eval0 : Context.t -> term -> value
end

type error_message =
  [ `Type_mismatch of Location.t * term * term
  | `VarNotFound of Location.t * string
  | `MsgLoc of Location.t * string
  ]

val is_type : Context.t -> term -> (unit, [> error_message]) result

val has_type : Context.t -> value -> term -> (unit, [> error_message]) result
