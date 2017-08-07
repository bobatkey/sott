%{
open Syntax

type elim =
  | Apply    of term * Location.t
  | ElimBool of term binder * term * term * Location.t
  | Project  of [`fst | `snd] * Location.t

let nil =
  { elims_data = Nil; elims_loc = Location.generated }

let build_elim elims = function
  | Apply (t, elims_loc) ->
     { elims_data = App (elims, t); elims_loc }
  | ElimBool (ty, tm_t, tm_f, elims_loc) ->
     { elims_data = If (elims, ty, tm_t, tm_f); elims_loc }
  | Project (dir, elims_loc) ->
     { elims_data = Project (elims, dir); elims_loc }
%}

%token <string> IDENT
%token LPAREN LBRACE LSQBRACK
%token RPAREN RBRACE RSQBRACK
%token DOT COMMA COLON SEMICOLON EQUALS
%token ARROW ASTERISK
%token TRUE FALSE BOOL BY_CASES FOR REFL COH SUBST FUNEXT
%token HASH_FST HASH_SND
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
  | BACKSLASH; xs=nonempty_list(IDENT); ARROW; t=term
    { List.fold_right
         (fun x t -> { term_data = Lam (Scoping.bind x t)
                     ; term_loc  = Location.generated })
         xs t }
  | bs=nonempty_list(pi_binding); ARROW; tT=term
    { List.fold_right
         (fun (id, tS) tT -> { term_data = Pi (tS, Scoping.bind id tT)
                             ; term_loc  = Location.generated })
         bs tT }
  | tS=app_term; ARROW; tT=term
    { { term_data = Pi (tS, Scoping.bind_anon tT)
      ; term_loc  = Location.mk $startpos $endpos } }
  | t=sigma_term
    { t }

pi_binding:
  | LPAREN; id=IDENT; COLON; tS=term; RPAREN
    { (id, tS) }

sigma_term:
  | LPAREN; id=IDENT; COLON; tS=term; RPAREN; ASTERISK; tT=sigma_term
    { { term_data = Sigma (tS, Scoping.bind id tT)
      ; term_loc  = Location.mk $startpos $endpos
      } }
  | tS=app_term; ASTERISK; tT=sigma_term
    { { term_data = Sigma (tS, Scoping.bind_anon tT)
      ; term_loc  = Location.mk $startpos $endpos
      } }
  | t=app_term
    { t }

app_term:
  | h=head; ts=nonempty_list(elim)
    { let h, es = h, Nil in
      { term_data = Neutral (h, List.fold_left build_elim nil ts)
      ; term_loc  = Location.mk $startpos $endpos } }
  | t=base_term
    { t }

base_term:
  | REFL
    { { term_data = Refl
      ; term_loc  = Location.mk $startpos $endpos } }
  | COH
    { { term_data = Coh
      ; term_loc  = Location.mk $startpos $endpos } }
  | FUNEXT; LPAREN; x1=IDENT; x2=IDENT; xe=IDENT; DOT; e=term; RPAREN
    { { term_data = Funext (Scoping.bind3 x1 x2 xe e)
      ; term_loc  = Location.mk $startpos $endpos } }
  | SUBST; LPAREN; ty_s=term;
            COMMA; x=IDENT; DOT; ty_t=term;
            COMMA; tm_x=term;
            COMMA; tm_y=term;
            COMMA; tm_e=term;
           RPAREN
    { { term_data = Subst { ty_s; ty_t = Scoping.bind x ty_t; tm_x; tm_y; tm_e }
      ; term_loc  = Location.mk $startpos $endpos } }
  | SET
    { { term_data = Set
      ; term_loc  = Location.mk $startpos $endpos } }
  | BOOL
    { { term_data = Bool
      ; term_loc  = Location.mk $startpos $endpos } }
  | TRUE
    { { term_data = True
      ; term_loc  = Location.mk $startpos $endpos } }
  | FALSE
    { { term_data = False
      ; term_loc  = Location.mk $startpos $endpos } }
  | LSQBRACK; ty1=term; EQUALS; ty2=term; RSQBRACK
    { { term_data = TyEq (ty1, ty2)
      ; term_loc  = Location.mk $startpos $endpos } }
  | LSQBRACK; tm1=term; COLON; ty1=term;
      EQUALS; tm2=term; COLON; ty2=term;
    RSQBRACK
    { { term_data = TmEq {tm1; ty1; tm2; ty2}
      ; term_loc  = Location.mk $startpos $endpos } }
  | h=head
    { { term_data = Neutral (h, nil)
      ; term_loc  = Location.mk $startpos $endpos } }
  | LPAREN; ts=separated_list(COMMA, term); RPAREN
    { let rec build = function
        | []    -> failwith "FIXME: implement the unit type"
        | [t]   -> t
        | [s;t] -> { term_data = Pair (s,t)
                   ; term_loc  = Location.mk $startpos $endpos }
        | t::ts -> { term_data = Pair (t,build ts)
                   ; term_loc  = Location.mk $startpos $endpos }
      in build ts }

head:
  | COERCE; LPAREN; coercee=term;
             COMMA; src_type=term;
             COMMA; tgt_type=term;
             COMMA; eq_proof=term;
            RPAREN
    { { head_data = Coerce { coercee; src_type; tgt_type; eq_proof }
      ; head_loc  = Location.mk $startpos $endpos } }
  | id=IDENT
    { { head_data = Free id;
        head_loc  = Location.mk $startpos $endpos } }

elim:
  | t=base_term
      { Apply (t, Location.mk $startpos $endpos) }
  | BY_CASES; FOR; x=IDENT; DOT; ty=term;
      LBRACE; TRUE; ARROW; tm_t=term;
   SEMICOLON; FALSE; ARROW; tm_f=term;
      RBRACE
      { ElimBool (Scoping.bind x ty, tm_t, tm_f, Location.mk $startpos $endpos) }
  | HASH_FST
      { Project (`fst, Location.mk $startpos $endpos) }
  | HASH_SND
      { Project (`snd, Location.mk $startpos $endpos) }
