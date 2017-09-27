open Html5.Static

open Parser

let class_of_token = function
  | SET | BOOL | TRUE | FALSE | NAT | ZERO | SUCC
  | REFL | COH | SUBST | FUNEXT | SAME_CLASS
  | SLASH | INTRODUCE | EMPTY | TAG _ ->
     "constructor"
  | HASH_FST | HASH_SND | COERCE | FOR | USE ->
     "eliminator"
  | DEFINE | AS ->
     "definitions"
  | LPAREN | RPAREN | LBRACE | RBRACE | LSQBRACK | RSQBRACK
  | EQUALS | COLON | SEMICOLON | DOT | COMMA | LBRACEPIPE | PIPERBRACE
  | ARROW | ASTERISK | BACKSLASH | UNDERSCORE | NATURAL _ ->
     "punctuation"
  | IDENT _ ->
     "identifier"
  | EOF ->
     assert false


let of_file filename =
  let ch = open_in filename in
  let lb = Lexing.from_channel ch in
  let rec build doc =
    let token_desc = Lexer.token lb in
    let token_text = Lexing.lexeme lb in
    match token_desc with
      | `Token EOF ->
         doc
      | _ ->
         let klass =
           match token_desc with
             | `Token tok  -> class_of_token tok
             | `Comment    -> "comment"
             | `Whitespace -> "whitespace"
             | `Newline    -> "whitespace"
         in
         let doc = doc ^^ span ~attrs:[A.class_ klass] (text token_text) in
         build doc
  in
  html begin
    head begin
      title filename
      ^^
      style
        {|
body pre { font-family: ubuntu mono }
.comment { color: green }
.definitions { font-weight: bold }
.identifier { font-style: italic }
.constructor { color: #cc2222 }
.eliminator { color: #229922 }
.punctuation { color: #555555 }
|}
    end
    ^^
    body begin
      pre begin
        build empty
      end
    end
  end
  |>
  Render.print ~doctype:true;
  Ok ()
