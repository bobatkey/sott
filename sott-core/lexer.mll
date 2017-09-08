{
open Lexing
open Parser
}

let white   = [' ' '\t']+
let newline = '\r' | '\n' | "\r\n"
let id_cont = ['a'-'z' 'A'-'Z' '0'-'9' '_' '\'']
let id      = ['a'-'z' 'A'-'Z'] id_cont* | ['_'] id_cont+
let natural = ['0'-'9']+

rule token = parse
| white        { `Whitespace }
| newline      { Lexing.new_line lexbuf; `Newline }
| "Set"        { `Token SET }
| '('          { `Token LPAREN }
| ')'          { `Token RPAREN }
| '{'          { `Token LBRACE }
| '}'          { `Token RBRACE }
| '['          { `Token LSQBRACK }
| ']'          { `Token RSQBRACK }
| '='          { `Token EQUALS }
| ':'          { `Token COLON }
| ';'          { `Token SEMICOLON }
| '.'          { `Token DOT }
| "->"         { `Token ARROW }
| ","          { `Token COMMA }
| "*"          { `Token ASTERISK }
| '_'          { `Token UNDERSCORE }
| "\\"         { `Token BACKSLASH }
| "Bool"       { `Token BOOL }
| "True"       { `Token TRUE }
| "False"      { `Token FALSE }
| "Nat"        { `Token NAT }
| "Zero"       { `Token ZERO }
| "Succ"       { `Token SUCC }
| "same-class" { `Token SAME_CLASS }
| "/"          { `Token SLASH }
| "for"        { `Token FOR }
| "refl"       { `Token REFL }
| "coerce"     { `Token COERCE }
| "coherence"  { `Token COH }
| "subst"      { `Token SUBST }
| "funext"     { `Token FUNEXT }
| "define"     { `Token DEFINE }
| "as"         { `Token AS }
| "use"        { `Token USE }
| "introduce"  { `Token INTRODUCE }
| "#fst"       { `Token HASH_FST }
| "#snd"       { `Token HASH_SND }
| natural      { `Token (NATURAL (int_of_string (Lexing.lexeme lexbuf))) }
| id           { `Token (IDENT (Lexing.lexeme lexbuf)) }
| "(*"         { comment lexbuf; `Comment }
| eof          { `Token EOF }

and comment = parse
| [^ '*''\n' ]* "\n" { Lexing.new_line lexbuf; comment lexbuf }
| [^ '*''\n' ]* "*)" { () }
| [^ '*''\n' ]* "(*" { comment lexbuf; comment lexbuf }
| [^ '*''\n' ]* "*"  { comment lexbuf }

{

let rec program_token lexbuf = match token lexbuf with
  | `Token tok ->
     tok
  | `Whitespace | `Comment | `Newline ->
     program_token lexbuf

}