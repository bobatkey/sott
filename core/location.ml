type t =
  | Generated
  | FromSource of
      { filename     : string
      ; start_line   : int
      ; start_column : int
      ; end_line     : int
      ; end_column   : int
      }

let mk loc_start loc_end =
  let open Lexing in
  FromSource { filename     = loc_start.pos_fname
             ; start_line   = loc_start.pos_lnum
             ; start_column = loc_start.pos_cnum - loc_start.pos_bol
             ; end_line     = loc_end.pos_lnum
             ; end_column   = loc_end.pos_cnum - loc_end.pos_bol
             }

let mk_span loc1 loc2 = match loc1, loc2 with
  | Generated, _ | _, Generated ->
     Generated
  | FromSource { filename; start_line; start_column },
    FromSource { end_line; end_column } ->
     FromSource { filename; start_line; start_column; end_line; end_column }

let generated = Generated

open Lexing

let pp fmt = function
  | Generated ->
     Format.pp_print_string fmt "<generated>"
  | FromSource info when info.start_line = info.end_line ->
     Format.fprintf fmt
       "file %S, line %d, characters %d-%d"
       info.filename
       info.start_line
       info.start_column
       info.end_column
  | FromSource info ->
     Format.fprintf fmt
       "file %S, line %d, character %d, to line %d, character %d, "
       info.filename
       info.start_line
       info.start_column
       info.end_line
       info.end_column

let pp_without_filename fmt = function
  | Generated ->
     Format.pp_print_string fmt "<generated>"
  | FromSource info when info.start_line = info.end_line ->
     Format.fprintf fmt
       "line %d, characters %d-%d"
       info.start_line
       info.start_column
       info.end_column
  | FromSource info ->
     Format.fprintf fmt
       "line %d, character %d, to line %d, character %d, "
       info.start_line
       info.start_column
       info.end_line
       info.end_column
