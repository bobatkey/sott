{
open Lexing
open Parser

let next_line lexbuf =
  let pos = lexbuf.lex_curr_p in
  lexbuf.lex_curr_p <-
    { pos with pos_bol  = lexbuf.lex_curr_pos;
               pos_lnum = pos.pos_lnum + 1
    }
}

let white   = [' ' '\t']+
let newline = '\r' | '\n' | "\r\n"
let id      = ['a'-'z' 'A'-'Z' '_'] ['a'-'z' 'A'-'Z' '0'-'9' '_']*

rule token = parse
| white     { token lexbuf }
| newline   { next_line lexbuf; token lexbuf }
| "Set"     { SET }
| '('       { LPAREN }
| ')'       { RPAREN }
| '{'       { LBRACE }
| '}'       { RBRACE }
| '['       { LSQBRACK }
| ']'       { RSQBRACK }
| '='       { EQUALS }
| ':'       { COLON }
| ';'       { SEMICOLON }
| '.'       { DOT }
| "->"      { ARROW }
| ","       { COMMA }
| "\\"      { BACKSLASH }
| "Bool"    { BOOL }
| "True"    { TRUE }
| "False"   { FALSE }
| "case"    { CASE }
| "for"     { FOR }
| "refl"    { REFL }
| "coerce"  { COERCE }
| "coh"     { COH }
| "subst"   { SUBST }
| "funext"  { FUNEXT }
| "define"  { DEFINE }
| "as"      { AS }
| id        { IDENT (Lexing.lexeme lexbuf) }
| "(*"      { comment lexbuf; token lexbuf }
| eof       { EOF }

and comment = parse
| [^ '*' ]* "*)" { () }
| [^ '*' ]* "(*" { comment lexbuf; comment lexbuf }
| [^ '*' ]* "*"  { comment lexbuf }
