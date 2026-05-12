(lang dune 3.11)
(name playground)
(generate_opam_files true)
(using coq 0.8)

(package
 (name playground)
 (synopsis "Playground Coq project")
 (allow_empty)
 (depends
  (coq (>= 8.19.0))
 ))
