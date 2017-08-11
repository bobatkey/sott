open Cmdliner

let filename_arg =
  Arg.(required
       & pos 0 (some string) None
       & info []
         ~docv:"FILENAME"
         ~doc:"Name of .sott file to process")

let typecheck_cmd =
  let doc = "Typecheck a .sott file" in
  Term.(const Sott_core.Declarations.process_file $ filename_arg),
  Term.info "typecheck" ~doc ~exits:Term.default_exits

let default_cmd =
  let doc = "Simplified Observational Type Theory" in
  let sdocs = Manpage.s_common_options in
  let exits = Term.default_exits in
  Term.(ret (const (`Help (`Pager, None)))),
  Term.info "sott" ~version:"v0.0.1" ~doc ~sdocs ~exits

let () =
  Term.(exit (eval_choice default_cmd [ typecheck_cmd ]))
