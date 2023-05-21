open Infer
open Infertypes
open Parsetree
open Res

let code =
  {|
  let foo x = 
    match x with 
      | 1 -> x 
      | _ -> 1
    in 
  foo
  |}

let code2 = {|
    1 "123"
  |}

let code3 = {|
    let (a, b) = 
      a + b 
    in
    a
  |}

let code4 = {| 
let foo (a, b) = 
  a + b 
in
  foo (1, 2)|}

let code5 = {| 
    let (a, b) = 
      ("123", 1) 
    in 
    b|}

let code6 =
  {|
  let rec foo x = 
    match x with 
    | 1 -> 1
    | y -> foo y 
  in
  foo|}

let code7 = {|let foo x = 1 in foo 1|}

let code8 = {| 
  let x = 1;;

  let y = x in y;;

  let z = "123";;

  z
|}

let list =
  let x = tvar_unbound (unbound "x" !curr_lvl []) [] in
  new_arrow x (new_arrow x (new_poly "list" [ x ] []) []) []

let plus =
  new_arrow (tgronud int_t [])
    (new_arrow (tgronud int_t []) (tgronud int_t []) [])
    []

let env' = [ ("ll", list); ("+", plus) ]

let top_infer env expr =
  reset_typ_vars ();
  reset_lvls_to_update ();
  match expr.pstr_desc with
  | Pstr_eval (expr, _) -> (tof env expr >>| cyc_free) *> return env
  | Pstr_value _ as v -> let_value env expr.pstr_loc v
  | _ -> not_impl_h_lvl

let codes = Parse.implementation (Lexing.from_string code2)

let ts env =
  List.fold_left
    (fun acc s ->
      let* env = acc in
      top_infer env s)
    (return env) codes

let ts = ts env'

let () =
  let open Format in
  match ts with Ok _ -> printf "Ok" | Error _ -> printf "err"
