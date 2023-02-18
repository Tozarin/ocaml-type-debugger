open Angstrom
open Ast

let is_ws = function ' ' | '\n' | '\r' | '\t' -> true | _ -> false
let ws = skip_while is_ws
let trim p = ws *> p <* ws
let parents p = char '(' *> p <* char ')'

let conde = function
  | [] -> fail "Empty condition"
  | h :: tl -> List.fold_left ( <|> ) h tl

let is_d = function '0' .. '9' -> true | _ -> false
let nums = take_while1 is_d

let is_hex_d = function
  | '0' .. '9' | 'a' .. 'f' | 'A' .. 'F' -> true
  | _ -> false

let hex_nums = take_while1 is_hex_d
let hex_pr = option "" (string "0x")
let int_num = (hex_pr >>= function "" -> nums | _ -> hex_nums) *> return TInt

let float_num =
  (hex_pr >>= function "" -> return nums | _ -> return hex_nums) >>= fun p ->
  (p <|> string "") *> char '.' *> p *> return TFloat
(* add 1e1 case *)

let bool = (string "true" <|> string "false") *> return TBool
let ch = char '\'' *> any_char *> char '\'' *> return TChar

let str =
  char '\"'
  *> skip_while (function '\"' -> false | _ -> true)
  *> char '\"' *> return TString

let unit = string "()" *> return TUnit
let const_t = conde [ int_num; float_num; bool; ch; str; unit ]

(*******************************************tests*******************************************)
let pr_opt p str = Result.get_ok @@ parse_string ~consume:All p str
let pr_not_opt p str = Result.get_error @@ parse_string ~consume:All p str

let%expect_test _ =
  print_string @@ show_const_type (pr_opt int_num {|0|});
  [%expect {|TInt|}]

let%expect_test _ =
  print_string @@ show_const_type (pr_opt int_num {|0x0|});
  [%expect {|TInt|}]

let%expect_test _ =
  print_string @@ show_const_type (pr_opt int_num {|0xa|});
  [%expect {|TInt|}]

let%expect_test _ =
  print_string @@ show_const_type (pr_opt int_num {|0xA|});
  [%expect {|TInt|}]

let%expect_test _ =
  print_string @@ show_const_type (pr_opt int_num {|0x123456789abcdef|});
  [%expect {|TInt|}]

let%expect_test _ =
  print_string @@ pr_not_opt int_num {|a|};
  [%expect {|: count_while1|}]

let%expect_test _ =
  print_string @@ pr_not_opt int_num {|0x|};
  [%expect {|: count_while1|}]

let%expect_test _ =
  print_string @@ show_const_type (pr_opt float_num {|0.0|});
  [%expect {| TFloat |}]

let%expect_test _ =
  print_string @@ show_const_type (pr_opt float_num {|0x0.0|});
  [%expect {| TFloat |}]

let%expect_test _ =
  print_string @@ show_const_type (pr_opt float_num {|0xa.aa|});
  [%expect {| TFloat |}]

let%expect_test _ =
  print_string @@ show_const_type (pr_opt float_num {|.0|});
  [%expect {| TFloat |}]

let%expect_test _ =
  print_string @@ show_const_type (pr_opt float_num {|0x.0|});
  [%expect {| TFloat |}]

let%expect_test _ =
  print_string @@ pr_not_opt float_num {|0.|};
  [%expect {|: count_while1|}]

let%expect_test _ =
  print_string @@ pr_not_opt float_num {|.|};
  [%expect {|: count_while1|}]

let%expect_test _ =
  print_string @@ show_const_type (pr_opt bool {|true|});
  [%expect {| TBool |}]

let%expect_test _ =
  print_string @@ show_const_type (pr_opt bool {|false|});
  [%expect {| TBool |}]

let%expect_test _ =
  print_string @@ pr_not_opt bool {|True|};
  [%expect {| : not enough input |}]

let%expect_test _ =
  print_string @@ show_const_type (pr_opt ch {|'a'|});
  [%expect {| TChar |}]

let%expect_test _ =
  print_string @@ show_const_type (pr_opt ch "'\t'");
  [%expect {| TChar |}]

let%expect_test _ =
  print_string @@ pr_not_opt ch {|a|};
  [%expect {| : char '\'' |}]

let%expect_test _ =
  print_string @@ show_const_type (pr_opt str {|"string"|});
  [%expect {| TString |}]

let%expect_test _ =
  print_string @@ show_const_type (pr_opt str {|"123  string   123())(())"|});
  [%expect {| TString |}]

let%expect_test _ =
  print_string @@ pr_not_opt str {|"string|};
  [%expect {| : not enough input |}]

let%expect_test _ =
  print_string @@ pr_not_opt str {|string"|};
  [%expect {| : char '"' |}]

let%expect_test _ =
  print_string @@ pr_not_opt str {|string|};
  [%expect {| : char '"' |}]

let%expect_test _ =
  print_string
  @@ show_const_type (pr_opt const_t {|"123  string   123())(())"|});
  [%expect {| TString |}]

let%expect_test _ =
  print_string @@ show_const_type (pr_opt const_t {|()|});
  [%expect{| TUnit |}]

let%expect_test _ =
  print_string @@ show_const_type (pr_opt const_t {|0x.0|});
  [%expect {| TFloat |}]

let%expect_test _ =
  print_string @@ show_const_type (pr_opt const_t {|'a'|});
  [%expect {| TChar |}]

let%expect_test _ =
  print_string @@ show_const_type (pr_opt const_t "'\n'");
  [%expect{| TChar |}]