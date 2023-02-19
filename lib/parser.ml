open Angstrom
open Ast

let is_ws = function ' ' | '\n' | '\r' | '\t' -> true | _ -> false
let ws = skip_while is_ws
let trim p = ws *> p <* ws
let parents p = char '(' *> p <* char ')'

let conde = function
  | [] -> fail "Empty condition"
  | h :: tl -> List.fold_left ( <|> ) h tl

let id =
  let f_ch = function '_' | '0' .. '9' | 'a' .. 'z' -> true | _ -> false in
  let other_ch = function '\'' | 'A' .. 'Z' -> true | _ -> false in
  let other c = f_ch c || other_ch c in
  satisfy f_ch >>= fun f ->
  take_while other >>= fun e -> return @@ Printf.sprintf "%c%s" f e

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

let bin_op =
  let iadd = string "+" *> return IAdd in
  let isub = string "-" *> return ISub in
  let imul = string "*" *> return IMul in
  let idiv = string "\\" *> return IDiv in
  let fadd = string "+." *> return FAdd in
  let fsub = string "-." *> return FSub in
  let fmul = string "*." *> return FMul in
  let fdiv = string "\\." *> return FDiv in
  let md = string "mod" *> return Mod in
  let less = string "<" *> return Less in
  let gre = string ">" *> return Gre in
  let leq = string "<=" *> return Leq in
  let geq = string ">=" *> return Geq in
  let eq = (string "==" <|> string "=") *> return Eq in
  let neq = (string "<>" <|> string "!=") *> return Neg in
  let logand = string "&&" *> return And in
  let logor = string "||" *> return Or in
  let concat = string "::" *> return Concat in
  conde
    [
      iadd;
      isub;
      imul;
      idiv;
      fadd;
      fsub;
      fmul;
      fdiv;
      md;
      less;
      gre;
      leq;
      geq;
      eq;
      neq;
      logand;
      logor;
      concat;
    ]

let un_op =
  option "" (string "-") >>= function "" -> return Not | _ -> return Minus

let expr =
  let lit = const_t >>= fun t -> return @@ ELiteral t in
  let b_op =
    bin_op >>= fun op ->
    return @@ fun x y -> EBinOp (op, x, y)
  in
  let u_op p =
    un_op >>= fun op ->
    p >>= fun e -> return @@ EUnOp (op, e)
  in
  let app =
    option "" (string "@@") >>= fun _ ->
    return @@ fun x y -> EApp (x, y)
  in
  let eid = id >>= fun id -> return @@ EId id in
  let chainl1 e op =
    let rec go acc = lift2 (fun f x -> f acc x) op e >>= go <|> return acc in
    e >>= fun init -> go init
  in
  fix (fun self ->
      let factor =
        trim @@ conde [ u_op @@ parents self; trim @@ u_op (lit <|> eid) ]
      in
      trim @@ chainl1 factor (b_op <|> app))

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
  [%expect {| TUnit |}]

let%expect_test _ =
  print_string @@ show_const_type (pr_opt const_t {|0x.0|});
  [%expect {| TFloat |}]

let%expect_test _ =
  print_string @@ show_const_type (pr_opt const_t {|'a'|});
  [%expect {| TChar |}]

let%expect_test _ =
  print_string @@ show_const_type (pr_opt const_t "'\n'");
  [%expect {| TChar |}]
