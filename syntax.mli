type term =
  | Neutral of head * elims

  | Lam of term
  | Set
  | Pi  of term * term
  | Bool
  | True
  | False

  | TyEq of term * term
  | TmEq of term * term * term * term

  (* equality proof constructors *)
  | Subst of { ty_s : term
             ; ty_t : term
             ; tm_x : term
             ; tm_y : term
             ; tm_e : term
             }
  | Refl
  | Coh
  | Funext of term

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
  | If  of elims * term * term * term

val bind : string -> ?offset:int -> term -> term

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

val eval_closed : Context.t -> term -> value

val is_type : Context.t -> term -> (unit, [>`Msg of string | `Type_mismatch of term * term]) result

val has_type : Context.t -> value -> term -> (unit, [> `Msg of string | `Type_mismatch of term * term]) result
