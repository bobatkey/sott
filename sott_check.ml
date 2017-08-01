let _ =
  match Declarations.process_file Sys.argv.(1) with
    | Ok _ -> print_endline "OK"; exit 0
    | Error _ -> exit 1

