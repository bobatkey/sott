module AttributeMap = Map.Make (String)

type attributes = string AttributeMap.t

type element_name = string

type node =
  | Void_element             of element_name * attributes
  | Normal_element           of element_name * attributes * node
  | RawText_element          of element_name * attributes * string
  | EscapableRawText_element of element_name * attributes * string
  | Text                     of string
  | RawText                  of string
  | Concat                   of node * node
  | Empty
  | List                     of node list

type 'a t = node

type 'a html = node

(**********************************************************************)
(* Rendering *)
module RenderCommon (Output : sig
    val string    : string -> unit
    val substring : string -> int -> int -> unit
  end) =
struct
  let attributes attrs =
    if not (AttributeMap.is_empty attrs) then begin
      attrs |> AttributeMap.iter begin fun name value ->
        Output.string " ";
        Output.string name;
        if value <> "" then begin
          Output.string "=\"";
          Output.string value; (* FIXME: escaping *)
          Output.string "\""
        end
      end
    end

  let start_tag name attrs =
    Output.string "<";
    Output.string name;
    attributes attrs;
    Output.string ">"

  let end_tag name =
    Output.string "</";
    Output.string name;
    Output.string ">"

  let escaped_text text =
    let rec loop i j =
      if j = String.length text then
        Output.substring text i (j - i)
      else if text.[j] = '<' then
        (Output.substring text i (j - i);
         Output.string "&lt;";
         loop (j+1) (j+1))
      else if text.[j] = '&' then
        (Output.substring text i (j - i);
         Output.string "&amp;";
         loop (j+1) (j+1))
      else
        loop i (j+1)
    in
    loop 0 0

  let rec node = function
    | Normal_element (name, attrs, children) ->
       start_tag name attrs;
       node children;
       end_tag name
    | Void_element (name, attrs) ->
       start_tag name attrs
    | RawText_element (name, attrs, text) ->
       start_tag name attrs;
       (* FIXME: need to make sure that 'text' doesn't contain </name> *)
       Output.string text;
       end_tag name
    | EscapableRawText_element (name, attrs, text) ->
       start_tag name attrs;
       Output.string text;
       end_tag name
    | Text string ->
       escaped_text string
    | RawText string ->
       Output.string string
    | Concat (node1, node2) ->
       node node1;
       node node2
    | Empty ->
       ()
    | List nodes ->
       List.iter node nodes

  let document ?(doctype=true) document =
    if doctype then
      Output.string "<!DOCTYPE html>";
    node document
end

module Render = struct

  let to_custom ?doctype render document =
    let module R =
      RenderCommon
        (struct
          let string = render
          let substring s i len =
            render (String.sub s i len)
        end)
    in
    R.document ?doctype document

  let to_buffer ?doctype buffer document =
    let module R =
      RenderCommon
        (struct
          let string = Buffer.add_string buffer
          let substring = Buffer.add_substring buffer
        end)
    in
    R.document ?doctype document

  let to_string ?doctype document =
    let b = Buffer.create 32768 in
    to_buffer ?doctype b document;
    Buffer.contents b

  let to_channel ?doctype ch document =
    let module Renderer =
      RenderCommon
        (struct
          let string = output_string ch
          let substring = output_substring ch
        end)
    in
    Renderer.document ?doctype document

  let print ?doctype document =
    let module Renderer =
      RenderCommon
        (struct
          let string = print_string
          let substring = output_substring stdout
        end)
    in
    Renderer.document ?doctype document
end

(**********************************************************************)
type _ attribute =
  | Attr of string * string
  | NoAttr

type 'a void_element = ?attrs:'a attribute list -> unit -> 'a t

type 'a void_element' = attrs:'a attribute list -> 'a t

type 'a escapable_text_element = ?attrs:'a attribute list -> string -> 'a t

type 'a raw_text_element = ?attrs:'a attribute list -> string -> 'a t

type 'a normal_element = ?attrs:'a attribute list -> 'a t -> 'a t

(**********************************************************************)
let empty = Empty

let (^^) node1 node2 = Concat (node1, node2)

let concat_list nodes = List nodes

let concat_map f l =
  List.fold_left (fun d x -> d ^^ f x) empty l

let map f t = t

let attributes list =
  List.fold_left
    (fun attributes -> function
       | Attr (name, value) ->
          AttributeMap.add name value attributes
       | NoAttr ->
          attributes)
    AttributeMap.empty
    list

(**********************************************************************)
let normal_element name ?(attrs=[]) children =
  let attributes = attributes attrs in
  Normal_element (name, attributes, children)

let escapable_raw_text_element name ?(attrs=[]) text =
  let attributes = attributes attrs in
  EscapableRawText_element (name, attributes, text)

let raw_text_element name ?(attrs=[]) text =
  let attributes = attributes attrs in
  RawText_element (name, attributes, text)

let void_element name ?(attrs=[]) () =
  let attributes = attributes attrs in
  Void_element (name, attributes)

let text text =
  Text text

let raw_text text =
  RawText text

(**********************************************************************)
(* 4.1 The root element *)
let html ?attrs = normal_element "html" ?attrs

(* 4.2 Document metadata *)
let head ?attrs = normal_element "head" ?attrs
let title ?attrs = escapable_raw_text_element "title" ?attrs
let base ~attrs = void_element "base" ~attrs ()
let link ~attrs = void_element "link" ~attrs ()
let meta ~attrs = void_element "meta" ~attrs ()
let style ?attrs = raw_text_element "style" ?attrs

(* 4.3 Sections *)
let body ?attrs = normal_element "body" ?attrs
let article ?attrs = normal_element "article" ?attrs
let section ?attrs = normal_element "section" ?attrs
let nav ?attrs = normal_element "nav" ?attrs
let aside ?attrs = normal_element "aside" ?attrs
let h1 ?attrs = normal_element "h1" ?attrs
let h2 ?attrs = normal_element "h2" ?attrs
let h3 ?attrs = normal_element "h3" ?attrs
let h4 ?attrs = normal_element "h4" ?attrs
let h5 ?attrs = normal_element "h5" ?attrs
let h6 ?attrs = normal_element "h6" ?attrs
let header ?attrs = normal_element "header" ?attrs
let footer ?attrs = normal_element "footer" ?attrs
let address ?attrs = normal_element "address" ?attrs

(* 4.4 Grouping content *)
let p ?attrs = normal_element "p" ?attrs
let hr ?attrs = void_element "hr" ?attrs
let pre ?attrs = normal_element "pre" ?attrs
let blockquote ?attrs = normal_element "blockquote" ?attrs
let ol ?attrs = normal_element "ol" ?attrs
let ul ?attrs = normal_element "ul" ?attrs
let li ?attrs = normal_element "li" ?attrs
let dl ?attrs = normal_element "dl" ?attrs
let dt ?attrs = normal_element "dt" ?attrs
let dd ?attrs = normal_element "dd" ?attrs
let figure ?attrs = normal_element "figure" ?attrs
let figcaption ?attrs = normal_element "figcaption" ?attrs
let div ?attrs = normal_element "div" ?attrs
let main ?attrs = normal_element "main" ?attrs

(* 4.5 Text level semantics *)
let a ?attrs = normal_element "a" ?attrs
let em ?attrs = normal_element "em" ?attrs
let strong ?attrs = normal_element "strong" ?attrs
let small ?attrs = normal_element "small" ?attrs
let s ?attrs = normal_element "s" ?attrs
let cite ?attrs = normal_element "cite" ?attrs
let q ?attrs = normal_element "q" ?attrs
let dfn ?attrs = normal_element "dfn" ?attrs
let abbr ?attrs = normal_element "abbr" ?attrs
let data ?attrs = normal_element "data" ?attrs
let time ?attrs = normal_element "time" ?attrs
let code ?attrs = normal_element "code" ?attrs
let var ?attrs = normal_element "var" ?attrs
let samp ?attrs = normal_element "samp" ?attrs
let kbd ?attrs = normal_element "kbd" ?attrs
let sub ?attrs = normal_element "sub" ?attrs
let sup ?attrs = normal_element "sup" ?attrs
let i ?attrs = normal_element "i" ?attrs
let b ?attrs = normal_element "b" ?attrs
let u ?attrs = normal_element "u" ?attrs
let mark ?attrs = normal_element "mark" ?attrs
let ruby ?attrs = normal_element "ruby" ?attrs
let rb ?attrs = normal_element "rb" ?attrs
let rt ?attrs = normal_element "rt" ?attrs
let rtc ?attrs = normal_element "rtc" ?attrs
let rp ?attrs = normal_element "rp" ?attrs
let bdi ?attrs = normal_element "bdi" ?attrs
let bdo ?attrs = normal_element "bdo" ?attrs
let span ?attrs = normal_element "span" ?attrs
let br ?attrs = void_element "br" ?attrs
let wbr ?attrs = void_element "wbr" ?attrs

(* 4.6 Edits *)
let ins ?attrs = normal_element "ins" ?attrs
let del ?attrs = normal_element "del" ?attrs

(* 4.7 Embedded content *)
let img ~attrs = void_element "img" ~attrs ()
(* FIXME: iframe isn't really a 'normal_element', but it seems
   easiest to treat it as one. *)
let iframe ?attrs = normal_element "iframe" ?attrs
let embed ~attrs = void_element "embed" ~attrs ()
let object_ ?attrs = normal_element "object" ?attrs
let param ~attrs = void_element "param" ~attrs ()
let video ?attrs = normal_element "video" ?attrs
let audio ?attrs = normal_element "audio" ?attrs
let source ~attrs = void_element "source" ~attrs ()
let track ~attrs = void_element "track" ~attrs ()
let map_ ?attrs = normal_element "map" ?attrs
let area ~attrs = void_element "area" ~attrs ()

(* 4.8 Links *)
(* FIXME: could have an enumeration of link types *)

(* 4.9 Tabular data *)
let table ?attrs = normal_element "table" ?attrs
let caption ?attrs = normal_element "caption" ?attrs
let colgroup ?attrs = normal_element "colgroup" ?attrs
let col ~attrs = void_element "col" ~attrs ()
let tbody ?attrs = normal_element "tbody" ?attrs
let thead ?attrs = normal_element "thead" ?attrs
let tfoot ?attrs = normal_element "tfoot" ?attrs
let tr ?attrs = normal_element "tr" ?attrs
let td ?attrs = normal_element "td" ?attrs
let th ?attrs = normal_element "th" ?attrs

(* 4.10 Forms *)
let form ?attrs = normal_element "form" ?attrs
let label ?attrs = normal_element "label" ?attrs
let input ~attrs = void_element "input" ~attrs ()
let button ?attrs = normal_element "button" ?attrs
let select ?attrs = normal_element "select" ?attrs
let datalist ?attrs = normal_element "datalist" ?attrs
let optgroup ?attrs = normal_element "optgroup" ?attrs
let option ?attrs = normal_element "option" ?attrs
let textarea ?attrs = escapable_raw_text_element "textarea" ?attrs
let keygen ~attrs = void_element "keygen" ~attrs ()
let output ?attrs = normal_element "output" ?attrs
let progress ?attrs = normal_element "progress" ?attrs
let meter ?attrs = normal_element "meter" ?attrs
let fieldset ?attrs = normal_element "fieldset" ?attrs
let legend ?attrs = normal_element "legend" ?attrs

(* 4.11 Scripting *)
let script ?attrs = raw_text_element "script" ?attrs
let noscript ?attrs = normal_element "noscript" ?attrs
let template ?attrs = normal_element "template" ?attrs
let canvas ?attrs = normal_element "canvas" ?attrs

(* Attributes *)
module A = struct
  (* Global attributes (3.2.5) *)
  let accesskey value =
    Attr ("accesskey", value)
  let class_ value =
    Attr ("class", value)
  let contenteditable value =
    Attr ("contenteditable", if value then "true" else "false")
  let dir value =
    Attr ("dir", match value with `ltr -> "ltr" | `rtl -> "rtl" | `auto -> "auto")
  let hidden value =
    Attr ("hidden", if value then "true" else "false")
  let id value =
    Attr ("id", value)
  let lang value =
    Attr ("lang", value)
  let spellcheck value =
    Attr ("spellcheck", if value then "true" else "false")
  let style value =
    Attr ("style", value)
  let tabindex value =
    Attr ("tabindex", string_of_int value)
  let title value =
    Attr ("title", value)
  let translate value =
    Attr ("translate", if value then "yes" else "no")

  (* 'html' element attributes (4.1.1) *)
  let manifest value =
    Attr ("manifest", value)

  (* 'meta' attributes *)
  let http_equiv value =
    Attr ("http-equiv", value)
  let content value =
    Attr ("content", value)
  let charset value =
    Attr ("charset", value)

  (* 'a' element attributes (4.5.1) *)
  let href value =
    Attr ("href", value)
  let target value =
    Attr ("target", value)
  let download value =
    Attr ("download", value)
  let rel value =
    Attr ("rel", value)
  let hreflang value =
    Attr ("hreflang", value)
  let type_ value =
    Attr ("type", value)

  (* For 'img' elements *)
  let src value =
    Attr ("src", value)

  (* For 'form' elements *)
  let accept_charset value =
    Attr ("accept-charset", value)
  let action value =
    Attr ("action", value)
  let autocomplete value =
    Attr ("autocomplete", value)
  let enctype value =
    Attr ("enctype", value)
  let http_method value =
    Attr ("method", value)
  let name value =
    Attr ("name", value)
  let novalidate value = (*FIXME: boolean?*)
    Attr ("novalidate", value)
  let target value =
    Attr ("target", value)

  (* For 'label' elements *)
  let form value =
    Attr ("form", value)
  let for_control value =
    Attr ("for", value)

  (* For 'input' elements *)
  let accept value =
    Attr ("accept", value)
  let alt value =
    Attr ("alt", value)
  let enabled value =
    Attr ("enabled", if value then "yes" else "no")
  let checked value =
    Attr ("checked", if value then "yes" else "no")
  let value value =
    Attr ("value", value)
  let placeholder value =
    Attr ("placeholder", value)

  let label value =
    Attr ("label", value)
  
  (* 'option' attributes *)
  let selected value =
    Attr ("selected", if value then "yes" else "no")
  let disabled value =
    if value then Attr ("disabled", "yes") else NoAttr

  (* FIXME... *)
end
