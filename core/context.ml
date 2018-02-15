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

module Make (T : TY_TM) = struct

  module VarMap = Map.Make(String)

  type ty = T.ty

  type tm = T.tm

  type entry =
    { entry_type : ty
    ; entry_defn : tm option
    }

  type t =
    { global_entries    : entry VarMap.t
    ; local_entries     : entry VarMap.t
    ; local_entry_order : string list
    }

  let empty =
    { global_entries = VarMap.empty
    ; local_entries  = VarMap.empty
    ; local_entry_order = []
    }

  let taken_of_ctxt ctxt nm =
    VarMap.mem nm ctxt.global_entries
    || VarMap.mem nm ctxt.local_entries

  (* FIXME: what if we extend with a name that is already free in the
     term? Need to distinguish free local and free global. *)
  let extend nm entry_type ctxt =
    let nm = Name_supply.freshen_for (taken_of_ctxt ctxt) nm in
    let entry = { entry_type; entry_defn = None } in
    nm,
    { ctxt with
        local_entries     = VarMap.add nm entry ctxt.local_entries
      ; local_entry_order = nm :: ctxt.local_entry_order
    }

  let lookup_local nm ctxt =
    match VarMap.find nm ctxt.local_entries with
      | exception Not_found ->
         Error (`VarNotFound nm)
      | {entry_type} ->
         Ok entry_type

  let lookup_global nm ctxt =
    match VarMap.find nm ctxt.global_entries with
      | exception Not_found ->
         Error (`VarNotFound nm)
      | {entry_type} ->
         Ok entry_type

  let lookup_exn nm ctxt =
    match VarMap.find nm ctxt.local_entries with
      | {entry_type;entry_defn} ->
         (entry_type, entry_defn)
      | exception Not_found ->
         let {entry_type; entry_defn} = VarMap.find nm ctxt.global_entries in
         (entry_type, entry_defn)

  let extend_global nm ~ty ~tm ctxt =
    let entry = { entry_type = ty; entry_defn = Some tm } in
    { ctxt with global_entries = VarMap.add nm entry ctxt.global_entries }

  let local_bindings ctxt =
    List.fold_left
      (fun bindings nm ->
         let {entry_type} = VarMap.find nm ctxt.local_entries in
         (nm, entry_type) :: bindings)
      []
      ctxt.local_entry_order

end
