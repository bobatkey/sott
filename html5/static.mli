(** Generation of HTML in string form. *)

(** Supports the generic HTML generation interface. *)
include Sig.S

(** [raw_text str] produces a document consisting of [str] without
    escaping any of the HTML-sensitive characters. FIXME: better
    description. *)
val raw_text : string -> _ t

(** Rendering of HTML documents to various kinds of outputs. *)
module Render : sig
  val to_buffer : ?doctype:bool -> Buffer.t -> _ t -> unit

  val to_string : ?doctype:bool -> _ t -> string

  val to_channel : ?doctype:bool -> out_channel -> _ t -> unit

  val print : ?doctype:bool -> _ t -> unit

  val to_custom : ?doctype:bool -> (string -> unit) -> _ t -> unit
end
