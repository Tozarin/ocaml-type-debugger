(lang dune 3.4)

(name otp)

(generate_opam_files true)

(source
 (github tozarin/ocaml-type-debugger))

(authors "Startsev Matvey")

(maintainers "https://github.com/Tozarin")

(license LGPL-3.0-only)

(package
 (name otp)
 (synopsis "Ocaml type debugger")
 (description "Ocaml type debugger")
 (depends
  ocaml
  dune
  angstrom
  bisect_ppx
  (ppx_inline_test :with-test)
  qcheck-core
  ppx_expect
  ppx_show
  ppx_deriving
  (odoc :with-doc)
  (ocamlformat :build)
  base))
