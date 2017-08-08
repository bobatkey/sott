{
open Lexing
open Parser
}

let white   = [' ' '\t']+
let newline = '\r' | '\n' | "\r\n"
let id      = ['a'-'z' 'A'-'Z' '_'] ['a'-'z' 'A'-'Z' '0'-'9' '_' '\'']*

rule token = parse
| white     { token lexbuf }
| newline   { Lexing.new_line lexbuf; token lexbuf }
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
| "*"       { ASTERISK }
| "\\"      { BACKSLASH }
| "Bool"    { BOOL }
| "True"    { TRUE }
| "False"   { FALSE }
| "Nat"     { NAT }
| "Zero"    { ZERO }
| "Succ"    { SUCC }
| "#recursion" { HASH_RECURSION }
| "by_cases" { BY_CASES }
| "for"     { FOR }
| "refl"    { REFL }
| "coerce"  { COERCE }
| "coherence" { COH }
| "subst"   { SUBST }
| "funext"  { FUNEXT }
| "define"  { DEFINE }
| "as"      { AS }
| "#fst"    { HASH_FST }
| "#snd"    { HASH_SND }
| id        { IDENT (Lexing.lexeme lexbuf) }
| "(*"      { comment lexbuf; token lexbuf }
| eof       { EOF }

and comment = parse
| [^ '*' ]* "*)" { () }
| [^ '*' ]* "(*" { comment lexbuf; comment lexbuf }
| [^ '*' ]* "*"  { comment lexbuf }
