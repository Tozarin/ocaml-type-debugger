open Infer
open Infertypes
open Parsetree
open Res

let code1 =
  {|
  let foo x = 
    match x with 
      | 1 -> x 
      | _ -> 1
    in 
  foo "str"
  |}

let code2 = {|
    1 "123"
  |}

let code3 = {|
    let foo (a, b) = 
      b + a 
    in
    foo
  |}

let code4 = {| 
let foo (a, b) = 
  a + b 
in
  foo ("123", 2)|}

let code5 = {| 
    let (a, b) = 
      ("123", 1) 
    in 
    a + 1|}

let code6 =
  {|
  let rec foo x = 
    match x with 
    | 1 -> 1
    | y -> foo y 
  in
  foo "123"|}

let code7 = {|let foo x = 1 in foo 1|}

let code8 = {| 
  let x = 1;;

  let y = x in y;;

  let z = "123";;

  z
|}

let code9 = {|
  let x (Int y) = y;;

  (+) (x (Int 1)) 1
|}

let list =
  let x = tvar_unbound (unbound "x" !curr_lvl []) [] in
  new_arrow x (new_arrow x (new_poly "list" [ x ] []) []) []

let plus =
  new_arrow (tgronud int_t [])
    (new_arrow (tgronud int_t []) (tgronud int_t []) [])
    []

let const = new_arrow (tgronud int_t []) (new_poly "INT" [] []) []
let env' = [ ("ll", list); ("+", plus); ("Int", const) ]

let top_infer env expr =
  reset_typ_vars ();
  reset_lvls_to_update ();
  match expr.pstr_desc with
  | Pstr_eval (expr, _) -> (tof env expr >>| cyc_free) *> return env
  | Pstr_value _ as v -> let_value env expr.pstr_loc v
  | _ -> not_impl_h_lvl

let codes = Parse.implementation (Lexing.from_string code1)

let ts env =
  List.fold_left
    (fun acc s ->
      let* env = acc in
      top_infer env s)
    (return env) codes

let ts = ts env'

let () =
  let open Format in
  match ts with
  | Ok _ -> printf "types are correct"
  | Error err -> pp_err std_formatter err
