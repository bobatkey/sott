%{
open Syntax

type elim =
  | Apply of term
  | ElimBool of term * term * term

let build_elim elims = function
  | Apply t                   -> App (elims, t)
  | ElimBool (ty, tm_t, tm_f) -> If (elims, ty, tm_t, tm_f)
%}

%token <string> IDENT
%token LPAREN LBRACE LSQBRACK
%token RPAREN RBRACE RSQBRACK
%token DOT COMMA COLON SEMICOLON EQUALS
%token ARROW
%token TRUE FALSE BOOL CASE FOR REFL COH SUBST FUNEXT
%token SET
%token DEFINE AS
%token COERCE
%token BACKSLASH

%token EOF

%start<Syntax.term> whole_term
%start<[`Def of string * Syntax.term * Syntax.term] list> file

%%

file:
  | definitions=list(definition); EOF
    { definitions }

definition:
  | DEFINE; nm=IDENT; COLON; ty=term; AS; tm=term
    { `Def (nm, ty, tm) }

whole_term:
  | t=term; EOF { t }

term:
  | BACKSLASH; x=IDENT; ARROW; t=term
    { Lam (bind x t) }
  | bs=nonempty_list(pi_binding); ARROW; tT=term
    { List.fold_right (fun (id, tS) tT -> Pi (tS, bind id tT)) bs tT }
  | tS=app_term; ARROW; tT=term
    { Pi (tS, tT) }
  | t=app_term
    { t }

pi_binding:
  | LPAREN; id=IDENT; COLON; tS=term; RPAREN
    { (id, tS) }

(* sigma_term goes here *)

app_term:
  | h=head; ts=nonempty_list(elim)
    { let h, es = h, Nil in Neutral (h, List.fold_left build_elim Nil ts) }
  | t=base_term
    { t }

base_term:
  | REFL
    { Refl }
  | COH
    { Coh }
  | FUNEXT; LPAREN; x1=IDENT; x2=IDENT; xe=IDENT; DOT; e=term; RPAREN
    { Funext (bind x1 ~offset:2 (bind x2 ~offset:1 (bind xe e))) }
  | SUBST; LPAREN; ty_s=term; COMMA; x=IDENT; DOT; ty_t=term; COMMA; tm_x=term; COMMA; tm_y=term; COMMA; tm_e=term; RPAREN
    { Subst { ty_s; ty_t = bind x ty_t; tm_x; tm_y; tm_e } }
  | SET
    { Set }
  | BOOL
    { Bool }
  | TRUE
    { True }
  | FALSE
    { False }
  | LSQBRACK; ty1=term; EQUALS; ty2=term; RSQBRACK
    { TyEq (ty1, ty2) }
  | LSQBRACK; tm1=term; COLON; ty1=term; EQUALS; tm2=term; COLON; ty2=term; RSQBRACK
    { TmEq {tm1; ty1; tm2; ty2} }
  | h=head
    { Neutral (h, Nil) }
  | LPAREN; t=term; RPAREN
    { t }

head:
  | COERCE; LPAREN; coercee=term; COMMA; src_type=term; COMMA; tgt_type=term; COMMA; eq_proof=term; RPAREN
    { Coerce { coercee; src_type; tgt_type; eq_proof } }
  | id=IDENT
    { Free id }

elim:
  | t=base_term
      { Apply t }
  | CASE; FOR; x=IDENT; DOT; ty=term; LBRACE; TRUE; ARROW; tm_t=term; SEMICOLON; FALSE; ARROW; tm_f=term; RBRACE
      { ElimBool (bind x ty, tm_t, tm_f) }
