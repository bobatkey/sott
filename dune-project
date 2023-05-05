(lang dune 3.6)

(generate_opam_files true)
 
(using menhir 2.0)

(source (github bobatkey/sott))
(authors "Robert Atkey" "robert.atkey@strath.ac.uk")
 

(package
 (name sott)
 (synopsis "Simplified Observational Type Theory")
 (description "Simplified Observational Type Theory")
 (depends
  (ocaml (>= 4.14.0))
  (dune (>= 3.7))
  (menhir (>= 20230415))
  (cmdliner (>= 1.2.0))))
