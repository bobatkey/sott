let pp_msg fmt = function
  | `Type_mismatch (loc, ty1, ty2) ->
     Format.fprintf fmt "type mismatch at %a: %a is not equal to %a"
       Location.pp_without_filename loc
       Pprint.pp_term  ty1
       Pprint.pp_term  ty2
  | `VarNotFound (loc, nm)  ->
     Format.fprintf fmt "Variable '%s' not in scope at %a"
       nm
       Location.pp_without_filename loc
  | `MsgLoc (loc, msg) ->
     Format.fprintf fmt "%s at %a"
       msg
       Location.pp_without_filename loc

let rec process_decls ctxt = function
  | [] ->
     Ok ()
  | `Def (id, ty, tm)::decls ->
     (match Syntax.is_type ctxt ty with
       | Error msg ->
          Format.eprintf "ERR: Checking '%s''s type: %a\n%!"
            id
            pp_msg msg;
          Error ()
       | Ok () ->
          let ty = Syntax.Evaluation.eval0 ctxt ty in
          match Syntax.has_type ctxt ty tm with
            | Error msg ->
               Format.eprintf "ERR: Checking '%s' body: %a\n%!"
                 id
                 pp_msg msg;
               Error ()
            | Ok () ->
               let tm = Syntax.Evaluation.eval0 ctxt tm in
               let ctxt = Syntax.Context.extend_with_defn id ~ty ~tm ctxt in
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

let process_file filename =
  let ch    = open_in filename in
  let lb    = Lexing.from_channel ch in
  let decls = Parser.file Lexer.token lb in
  process_decls Syntax.Context.empty decls

let pprint_file filename =
  let ch    = open_in filename in
  let lb    = Lexing.from_channel ch in
  let decls = Parser.file Lexer.token lb in
  Format.set_margin 120;
  pprint_decls decls
