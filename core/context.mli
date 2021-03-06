module type S = sig

  type t

  type ty

  type tm

  val empty : t

  val extend : string -> ty -> t -> string * t

  val extend_global : string -> ty:ty -> tm:tm -> t -> t

  val lookup_local : string -> t -> (ty, [>`VarNotFound of string]) result

  val lookup_global : string -> t -> (ty, [>`VarNotFound of string]) result

  val lookup_exn : string -> t -> ty * tm option

  val local_bindings : t -> (string * ty) list

end

module type TY_TM = sig

  type ty

  type tm

end

module Make (T : TY_TM)
  : S with type ty = T.ty and type tm = T.tm
