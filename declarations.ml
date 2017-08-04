(*
   plan:

   - read in the declarations
   - for each decl, check the type, check the term, if OK, then add to current context
   - if error: report and stop

*)

let string_of_msg = function
  | `Msg msg         -> msg
  | `Type_mismatch _ -> "type mismatch"
  | `VarNotFound nm  -> Printf.sprintf "Variable '%s' not in scope" nm

let rec process_decls ctxt = function
  | [] ->
     Ok ctxt
  | `Def (id, ty, tm)::decls ->
     (match Syntax.is_type ctxt ty with
       | Error msg ->
          Printf.eprintf "ERR: Checking '%s''s type: %s\n%!"
            id (string_of_msg msg);
          Error ()
       | Ok () ->
          let ty = Syntax.eval0 ctxt ty in
          match Syntax.has_type ctxt ty tm with
            | Error msg ->
               Printf.eprintf "ERR: Checking '%s' body: %s\n%!"
                 id (string_of_msg msg);
               Error ()
            | Ok () ->
               let tm = Syntax.eval0 ctxt tm in
               let ctxt = Syntax.Context.extend_with_defn id ~ty ~tm ctxt in
               process_decls ctxt decls)

let process_file filename =
  let ch    = open_in filename in
  let lb    = Lexing.from_channel ch in
  let decls = Parser.file Lexer.token lb in
  process_decls Syntax.Context.empty decls
