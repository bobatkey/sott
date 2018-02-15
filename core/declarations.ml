let rec process_decls ctxt = function
  | [] ->
     Ok ()
  | `Def (id, ty, tm)::decls ->
     (match Checker.is_type ctxt ty with
       | Error msg ->
          Format.eprintf "@[<v>ERR: Checking '%s''s type: %a@]\n%!"
            id
            Pprint_error.pp msg;
          Error ()
       | Ok () ->
          let ty = Checker.Evaluation.eval0 ctxt ty in
          match Checker.has_type ctxt ty tm with
            | Error msg ->
               Format.eprintf "@[<v>ERR: Checking '%s' body: %a@]\n%!"
                 id
                 Pprint_error.pp msg;
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
