(** HTML5 generation module signature. *)

(** {1 HTML5 Generation Interface}

    This module defines a single signature {!S} that describes an
    interface for generating HTML5 node forests (a forest is a
    sequence of nodes, where nodes may contain other nodes). *)

(** Module signature for implementations that support construction of
    HTML5 node forests. *)
module type S = sig

  (** Representations of forests of HTML5 elements. The actual
      representation is specific to the implementation of this
      signature. The type parameter represents the type of annotations
      that the represented HTML has been decorated with. *)
  type +'a html

  type +'a t = 'a html

  (** Representations of HTML5 attributes. The actual representation
      is specific to the implementation of this signature. The type
      parameter represents the type of annotations that that the
      represented attribute has been decorated with. *)
  type _ attribute

  (** {2 Monoid Operations} *)

  (** The empty forest of HTML5 nodes. *)
  val empty : _ html

  (** Concatenation of HTML5 node forests. *)
  val (^^) : 'action html -> 'action html -> 'action html

  (** [concat_list l] concatenates all the elements of [l] using
      {!^^}, or is {!empty} if [l] is empty. *)
  val concat_list  : 'action html list -> 'action html

  (** [concat_map f l] is equivalent to doing [concat_list (List.map f
      l)], but is more efficient because it won't allocate the
      intermediate list. *)
  val concat_map : ('a -> 'action html) -> 'a list -> 'action html

  (** {2 Functor} *)
  
  val map : ('a -> 'b) -> 'a html -> 'b html

  (** {2 Node Generation} *)

  (** {3 Text Nodes} *)

  (** [text str] constructs a text node containing the string
      [str]. 

      FIXME: encodings? *)
  val text : string -> _ html

  (** {3 Element Nodes} *)
  
  (** {4 Element generator types} *)

  type 'a void_element =
    ?attrs:'a attribute list -> unit -> 'a html

  type 'a void_element' =
    attrs:'a attribute list -> 'a html

  type 'a escapable_text_element =
    ?attrs:'a attribute list -> string -> 'a html

  type 'a raw_text_element =
    ?attrs:'a attribute list -> string -> 'a html

  type 'a normal_element =
    ?attrs:'a attribute list -> 'a html -> 'a html

  (** {4 The root element (HTML5, Sec. 4.1)} *)
  
  val html : _ normal_element

  (** {4 Document metadata (HTML5, Sec 4.2)} *)

  val head : _ normal_element
  val title : _ escapable_text_element
  val base : _ void_element'
  val link : _ void_element'
  val meta : _ void_element'
  val style : _ raw_text_element

  (** {4 Sections (HTML5, Sec 4.3)} *)

  val body : _ normal_element
  val article : _ normal_element
  val section : _ normal_element
  val nav : _ normal_element
  val aside : _ normal_element
  val h1 : _ normal_element
  val h2 : _ normal_element
  val h3 : _ normal_element
  val h4 : _ normal_element
  val h5 : _ normal_element
  val h6 : _ normal_element
  val header : _ normal_element
  val footer : _ normal_element
  val address : _ normal_element

  (** {4 Grouping content (HTML5, Sec 4.4)} *)
  
  val p : _ normal_element
  val hr : _ void_element
  val pre : _ normal_element
  val blockquote : _ normal_element
  val ol : _ normal_element
  val ul : _ normal_element
  val li : _ normal_element
  val dl : _ normal_element
  val dt : _ normal_element
  val dd : _ normal_element
  val figure : _ normal_element
  val figcaption : _ normal_element
  val div : _ normal_element
  val main : _ normal_element

  (** {4 Text level semantics (HTML5, Sec 4.5)} *)

  val a : _ normal_element
  val em : _ normal_element
  val strong : _ normal_element
  val small : _ normal_element
  val s : _ normal_element
  val cite : _ normal_element
  val q : _ normal_element
  val dfn : _ normal_element
  val abbr : _ normal_element
  val data : _ normal_element
  val time : _ normal_element
  val code : _ normal_element
  val var : _ normal_element
  val samp : _ normal_element
  val kbd : _ normal_element
  val sub : _ normal_element
  val sup : _ normal_element
  val i : _ normal_element
  val b : _ normal_element
  val u : _ normal_element
  val mark : _ normal_element
  val ruby : _ normal_element
  val rb : _ normal_element
  val rt : _ normal_element
  val rtc : _ normal_element
  val rp : _ normal_element
  val bdi : _ normal_element
  val bdo : _ normal_element
  val span : _ normal_element
  val br : _ void_element
  val wbr : _ void_element

  (** {4 Edits (HTML5, Sec 4.6)} *)

  val ins : _ normal_element
  val del : _ normal_element

  (** {4 Embedded content (HTML5, Sec 4.7)} *)

  val img : _ void_element'
  val iframe : _ normal_element (* not really a normal element *)
  val embed : _ void_element'
  val object_ : _ normal_element
  val param : _ void_element'
  val video : _ normal_element
  val audio : _ normal_element
  val source : _ void_element'
  val track : _ void_element'
  val map_ : _ normal_element
  val area : _ void_element'

  (** {4 Tabular data (HTML5, Sec 4.9)} *)
  
  val table : _ normal_element
  val caption : _ normal_element
  val colgroup : _ normal_element
  val col : _ void_element'
  val tbody : _ normal_element
  val thead : _ normal_element
  val tfoot : _ normal_element
  val tr : _ normal_element
  val td : _ normal_element
  val th : _ normal_element

  (** {4 Forms (HTML5, Sec 4.10)} *)
  
  val form : _ normal_element
  val label : _ normal_element
  val input : _ void_element'
  val button : _ normal_element
  val select : _ normal_element
  val datalist : _ normal_element
  val optgroup : _ normal_element
  val option : _ normal_element
  val textarea : _ escapable_text_element
  val keygen : _ void_element'
  val output : _ normal_element
  val progress : _ normal_element
  val meter : _ normal_element
  val fieldset : _ normal_element
  val legend : _ normal_element

  (** {4 Scripting (HTML5, Sec 4.11)} *)

  val script : _ raw_text_element
  val noscript : _ normal_element
  val template : _ normal_element
  val canvas : _ normal_element

  (** {2 Attribute Generation} *)

  (** Attribute generation interface *)
  module A : sig

    (** {3 Global attributes (HTML5, Sec 3.2.5)} *)

    val accesskey : string -> _ attribute
    val class_ : string -> _ attribute
    val contenteditable : bool -> _ attribute
    val dir : [`ltr | `rtl | `auto] -> _ attribute
    val hidden : bool -> _ attribute
    val id : string -> _ attribute
    val lang : string -> _ attribute
    val spellcheck : bool -> _ attribute
    val style : string -> _ attribute
    val tabindex : int -> _ attribute
    val title : string -> _ attribute
    val translate : bool -> _ attribute

    (** {3 'html' element attributes (HTML, Sec 4.1.1)} *)
    
    val manifest : string (* uri *) -> _ attribute

    (* 'meta' attributes *)
    val http_equiv : string -> _ attribute
    val content : string -> _ attribute
    val charset : string -> _ attribute

    (* 'style' attributes *)
    (* FIXME *)

    (* 'blockquote' attributes *)
    (*val cite : string -> _ attribute*)

    (* 'ol' attributes *)
    (* FIXME *)

    (* 'li' attributes *)
    (* FIXME: 'value' *)

    (* 'a' attributes *)
    val href : string -> _ attribute
    val download : string -> _ attribute
    val rel : string -> _ attribute
    val hreflang : string -> _ attribute
    val type_ : string -> _ attribute

    (* 'img' attributes *)
    val src : string -> _ attribute
    val alt : string -> _ attribute

    (* 'form' attributes *)
    val accept_charset : string -> _ attribute
    val action : string -> _ attribute
    val autocomplete : string -> _ attribute
    val enctype : string -> _ attribute
    val http_method : string -> _ attribute
    val name : string -> _ attribute
    val novalidate : string -> _ attribute
    val target : string -> _ attribute

    (* 'label' attributes *)
    val form : string -> _ attribute
    val for_control : string -> _ attribute

    (* 'input' attributes *)
    val enabled : bool -> _ attribute
    val checked : bool -> _ attribute
    val value   : string -> _ attribute
    val placeholder : string -> _ attribute

    val label : string -> _ attribute

    (* 'option' attributes *)
    val selected : bool -> _ attribute
    val disabled : bool -> _ attribute
  end
end
