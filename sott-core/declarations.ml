let pp_msg fmt = function
  | Checker.Type_mismatch {loc; ctxt; computed_ty; expected_ty} ->
     Format.fprintf fmt
       "type mismatch at %a: expected type @ @[<v 2>@,%a@,@]@ is not equal to computed type@ @[<v 2>@,%a@,@]"
       Location.pp_without_filename loc
       (* FIXME: these are meaningless without the context in which they occur *)
       Pprint.pp_term  expected_ty
       Pprint.pp_term  computed_ty
  | Checker.Types_not_equal {loc; ctxt; ty1; ty2} ->
     Format.fprintf fmt
       "types not equal at %a:@ @[<v 2>@,%a@,@]@ is not equal to@ @[<v 2>@,%a@,@]"
       Location.pp_without_filename loc
       (* FIXME: these are meaningless without the context in which they occur *)
       Pprint.pp_term  ty1
       Pprint.pp_term  ty2
  | Checker.Term_mismatch (loc, ctxt, tm1, tm2, ty) ->
     Format.fprintf fmt
       "terms not equal at %a:@ @[<v 2>@,%a@,@]@ is not equal to@ @[<v 2>@,%a@,@]@ at type@ @[<v 2>@,%a@,@]"
       Location.pp_without_filename loc
       (* FIXME: these are meaningless without the context in which they occur *)
       Pprint.pp_term  tm1
       Pprint.pp_term  tm2
       Pprint.pp_term  ty
  | Checker.Term_is_not_a_type loc ->
     Format.fprintf fmt
       "term is not a type at %a"
       Location.pp_without_filename loc
  | Checker.BadApplication { loc; arg_loc; ctxt; ty } ->
     Format.fprintf fmt
       "Application of a non function at %a: term has type@ @[<v 2>@,%a@,@]"
       Location.pp_without_filename loc
       Pprint.pp_term               ty
  | Checker.VarNotFound (loc, nm)  ->
     Format.fprintf fmt
       "Variable '%s' not in scope at %a"
       nm
       Location.pp_without_filename loc
  | Checker.MsgLoc (loc, msg) ->
     Format.fprintf fmt "%s at %a"
       msg
       Location.pp_without_filename loc

let rec process_decls ctxt = function
  | [] ->
     Ok ()
  | `Def (id, ty, tm)::decls ->
     (match Checker.is_type ctxt ty with
       | Error msg ->
          Format.eprintf "@[<v>ERR: Checking '%s''s type: %a@]\n%!"
            id
            pp_msg msg;
          Error ()
       | Ok () ->
          let ty = Checker.Evaluation.eval0 ctxt ty in
          match Checker.has_type ctxt ty tm with
            | Error msg ->
               Format.eprintf "@[<v>ERR: Checking '%s' body: %a@]\n%!"
                 id
                 pp_msg msg;
               Error ()
            | Ok () ->
               let tm = Checker.Evaluation.eval0 ctxt tm in
               let ctxt = Checker.Context.extend_with_defn id ~ty ~tm ctxt in
               process_decls ctxt decls)

let pprint_decl (`Def (id, ty, tm)) =
  Format.printf "@[<v>@[<hov 4>define %s :@ %a@]@]@.as @[<hov 4>%a@]@]@."
    id
    Pprint.pp_term ty
    Pprint.pp_term tm

let rec pprint_decls = function
  | [] ->
     Ok ()
  | [decl] ->
     pprint_decl decl; Ok ()
  | decl::decls ->
     pprint_decl decl;
     Format.print_newline ();
     pprint_decls decls

let load_file filename =
  let ch = open_in filename in
  let lb = Lexing.from_channel ch in
  try
    let decls = Parser.file Lexer.program_token lb in
    close_in ch;
    Ok decls
  with Parser.Error ->
    close_in ch;
    Error (Printf.sprintf "Parse error at line %d, column %d"
             lb.Lexing.lex_curr_p.Lexing.pos_lnum
             (lb.Lexing.lex_curr_p.Lexing.pos_cnum-
              lb.Lexing.lex_curr_p.Lexing.pos_bol))

let process_file filename =
  match load_file filename with
    | Ok decls ->
       process_decls Checker.Context.empty decls
    | Error msg ->
       Format.printf "ERR: %s\n" msg;
       Error ()

let pprint_file filename =
  match load_file filename with
    | Ok decls ->
       Format.set_margin 100;
       pprint_decls decls
    | Error msg ->
       Format.printf "ERR: %s\n" msg;
       Error ()
