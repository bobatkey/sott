open Cmdliner

let filename_arg =
  Arg.(required
       & pos 0 (some string) None
       & info []
         ~docv:"FILENAME"
         ~doc:"Name of .sott file to process")

let typecheck_cmd =
  let doc = "Typecheck a .sott file" in
  Cmd.v
    Cmd.(info "typecheck" ~doc)
    Term.(const Sott_core.Declarations.process_file $ filename_arg)

let pprint_cmd =
  let doc = "Pretty print a .sott file" in
  Cmd.v
    Cmd.(info "pprint" ~doc)
    Term.(const Sott_core.Declarations.pprint_file $ filename_arg)

let html_cmd =
  let doc = "Render a .sott file to HTML5" in
  Cmd.v
    Cmd.(info "html" ~doc)
    Term.(const Sott_core.Html_gen.of_file $ filename_arg)

let default_cmd =
  Term.(ret (const (`Help (`Pager, None))))


let () =
  let doc = "Simplified Observational Type Theory" in
  let sdocs = Manpage.s_common_options in
  let cmd =
    Cmd.group
      ~default:default_cmd
      (Cmd.info "sott" ~version:"v0.0.1" ~doc ~sdocs)
      [ typecheck_cmd
      ; pprint_cmd
      ; html_cmd
      ]
  in
  exit (Cmd.eval cmd)
