(lang dune 3.11)
(name playground)
(generate_opam_files true)
(using coq 0.8)

(package
 (name playground)
 (synopsis "Playground Coq project")
 (allow_empty)
 (depends
  (coq (>= 9.1.0))
  (coq-stdlib (>= 9.0.0))
  (coq-hammer (>= "1.3.2+9.1"))
 ))
