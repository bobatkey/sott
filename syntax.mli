type 'a binder =
  | B  of string * 'a

type term =
  | Neutral of head * elims

  | Lam of term binder
  | Set
  | Pi  of term * term binder
  | Sigma of term * term binder
  | Pair of term * term
  | Bool
  | True
  | False

  | TyEq of term * term
  | TmEq of { tm1 : term; ty1 : term; tm2 : term; ty2 : term }

  (* equality proof constructors *)
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
  | Bound  of int
  | Free   of string
  | Coerce of { coercee  : term
              ; src_type : term
              ; tgt_type : term
              ; eq_proof : term
              }

and elims =
  | Nil
  | App of elims * term
  | If  of elims * term binder * term * term
  | Project of elims * [`fst | `snd]

val bind : string -> term -> term binder
val bind3 : string -> string -> string -> term -> term binder binder binder
val bind_anon : term -> term binder

(** Internal representation of checked terms *)
type value

val reify_type : value -> int -> term

val reify : value -> value -> int -> term

module Context : sig
  type t

  val empty : t
  val extend_with_defn : string -> ty:value -> tm:value -> t -> t
  val lookup_exn : string -> t -> value * value option
end

type error_message =
  [ `Msg of string
  | `Type_mismatch of term * term
  | `VarNotFound of string
  ]

val eval0 : Context.t -> term -> value

val is_type : Context.t -> term -> (unit, [> error_message]) result

val has_type : Context.t -> value -> term -> (unit, [> error_message]) result
