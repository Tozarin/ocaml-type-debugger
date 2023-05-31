(** Copyright 2023, Startsev Matvey *)

(** SPDX-License-Identifier: LGPL-3.0-or-later *)

open Warnings

type name = string [@@deriving show { with_path = false }]
type lvl = int [@@deriving show { with_path = false }]

type ground_typ = Int | String | Char | Bool | Float
[@@deriving show { with_path = false }]

let int_t = Int
let string_t = String
let char_t = Char
let bool_t = Bool
let float_t = Float
let pp_loc = Location.print_loc

type lvls = { mutable old_lvl : lvl; mutable new_lvl : lvl }
[@@deriving show { with_path = false }]

type typ =
  | TVar of tv ref * reasons
  | TArrow of typ * typ * lvls * reasons
  | TPoly of name * typ list * lvls * reasons
  | TGround of ground_typ * reasons
  | TTuple of typ list * lvls * reasons

and tv = Unbound of name * lvl * reasons | Link of typ * reasons

and reason =
  | InitConst of ground_typ * loc
  | InitVar of name * loc
  | NoReason
  | ResultOf of name * loc
  | ResultOfWithoutName of loc
  | ResultOfApply of typ * loc
  | LetExpr of name * loc
  | NamelessFunction of loc
  | InitTuple of loc
  | PatAnyVar of loc
  | PatConst of ground_typ * loc
  | PatIntervalConst of ground_typ * loc
  | PatTuple of loc
  | ResOfPatMatch of loc
  | ArgOf of int * loc
  | ApplyAs of int * typ * loc
  | RecDef of loc
  | ResOfConstr of name * loc
  | PatConstr of name * loc

and reasons = reason list [@@deriving show { with_path = false }]

let unbound name lvl rs = Unbound (name, lvl, rs)
let link t rs = Link (t, rs)
let tvar_unbound unb rs = TVar (ref unb, rs)
let tvar_link link rs = TVar (ref link, rs)
let tarrow t1 t2 lvls r = TArrow (t1, t2, lvls, r)
let tgronud t rs = TGround (t, rs)
let tpoly name ts lvls rs = TPoly (name, ts, lvls, rs)
let ttuple ts lvls rs = TTuple (ts, lvls, rs)
let reasons r = [ r ]
let init_const t loc = reasons @@ InitConst (t, loc)
let init_var name loc = reasons @@ InitVar (name, loc)
let no_reason = reasons @@ NoReason
let result_of name loc = reasons @@ ResultOf (name, loc)
let res_of_nameless loc = reasons @@ ResultOfWithoutName loc
let let_expr name loc = reasons @@ LetExpr (name, loc)
let nl_fun loc = reasons @@ NamelessFunction loc
let init_tuple loc = reasons @@ InitTuple loc
let pat_any loc = reasons @@ PatAnyVar loc
let pat_const t loc = reasons @@ PatConst (t, loc)
let pat_interval_const t loc = reasons @@ PatIntervalConst (t, loc)
let pat_tuple loc = reasons @@ PatTuple loc
let res_of_pm loc = reasons @@ ResOfPatMatch loc
let arg_of n loc = reasons @@ ArgOf (n, loc)
let rec_dec loc = reasons @@ RecDef loc
let res_of_apply f loc = reasons @@ ResultOfApply (f, loc)
let res_of_const name loc = reasons @@ ResOfConstr (name, loc)
let pat_constr name loc = reasons @@ PatConstr (name, loc)

let rec map_reason f = function
  | TVar (({ contents = Unbound (name, lvl, u_tr) } as tvr), _) as t ->
      tvr := Unbound (name, lvl, f u_tr);
      t
  | TVar (({ contents = Link (l_t, l_tr) } as tvr), _) as t ->
      tvr := Link (map_reason f l_t, l_tr);
      t
  | TArrow (t1, t2, l, tr) -> TArrow (t1, t2, l, f tr)
  | TGround (t, tr) -> TGround (t, f tr)
  | TPoly (name, ts, lvls, tr) -> TPoly (name, ts, lvls, f tr)
  | TTuple (ts, lvls, tr) -> TTuple (ts, lvls, f tr)

let rec map_reasons f = function
  | TVar ({ contents = Unbound (name, lvl, u_tr) }, v_tr) ->
      tvar_unbound (unbound name lvl (f u_tr)) (f v_tr)
  | TVar ({ contents = Link (l_t, l_tr) }, v_tr) ->
      tvar_link (link (map_reasons f l_t) (f l_tr)) (f v_tr)
  | TArrow (t1, t2, l, tr) ->
      TArrow (map_reasons f t1, map_reasons f t2, l, f tr)
  | TGround (t, tr) -> TGround (t, f tr)
  | TPoly (name, ts, lvls, tr) ->
      TPoly (name, List.map (map_reasons f) ts, lvls, f tr)
  | TTuple (ts, lvls, tr) -> TTuple (List.map (map_reasons f) ts, lvls, f tr)

let clear_reasons = map_reasons (fun _ -> [])
let concat_reasons t tr = map_reason (fun tr' -> tr' @ tr) t
let add_reason t r = map_reason (fun ts -> r :: ts) t

let take_reasons = function
  | TVar (_, tr) -> tr
  | TArrow (_, _, _, tr) -> tr
  | TGround (_, tr) -> tr
  | TPoly (_, _, _, tr) -> tr
  | TTuple (_, _, tr) -> tr

let new_reasons t rs = map_reason (fun _ -> rs) t

type err =
  | PlaceHolder
  | OccursFail
  | MissingInvariant
  | UnifyFail of typ * typ
  | IntervalPatternFail
  | NotImplementedPattern
  | NoSuchFunction of name
  | RecNotImplementedPart
  | NotImplementedExpression
  | NotImplementedHightLvl
  | ExpectedLet
  | UnexpectedConstructSig
  | NoSuchConstr of name
  | UnsupportedCoreType
  | NotImplementedType
[@@deriving show { with_path = false }]

module Res : sig
  type 'a t = ('a, err) Result.t

  val return : 'a -> 'a t
  val error : err -> 'a t
  val ( >>= ) : 'a t -> ('a -> 'b t) -> 'b t
  val ( let* ) : 'a t -> ('a -> 'b t) -> 'b t
  val ( *> ) : 'a t -> 'b t -> 'b t
  val ( >>| ) : 'a t -> ('a -> 'b) -> 'b t
  val occurs_fail : 'a t
  val miss_invar : 'a t
  val unify_fail : typ -> typ -> 'a t
  val interval_pat_fail : 'a t
  val not_impl_pat : 'a t
  val no_fun : name -> 'a t
  val rec_no_impl : 'a t
  val no_impl_expr : 'a t
  val not_impl_h_lvl : 'a t
  val exp_let : 'a t
  val constr_sig : 'a t
  val no_constr : name -> 'a t
  val unsup_core : 'a t
  val not_impl_t_d : 'a t
  val ph : 'a t
end = struct
  type 'a t = ('a, err) Result.t

  let return : 'a -> 'a t = fun x -> Ok x
  let error : err -> 'a t = fun msg -> Error msg
  let ( >>= ) : 'a t -> ('a -> 'b t) -> 'b t = Result.bind
  let ( let* ) = ( >>= )

  let ( *> ) : 'a t -> 'b t -> 'b t =
   fun x y -> match x with Ok _ -> y | Error msg -> error msg

  let ( >>| ) : 'a t -> ('a -> 'b) -> 'b t =
   fun x f -> match x with Ok x -> Ok (f x) | Error msg -> error msg

  let occurs_fail = error OccursFail
  let miss_invar = error MissingInvariant
  let unify_fail t1 t2 = error @@ UnifyFail (t1, t2)
  let interval_pat_fail = error @@ IntervalPatternFail
  let not_impl_pat = error @@ NotImplementedPattern
  let no_fun f = error @@ NoSuchFunction f
  let rec_no_impl = error @@ RecNotImplementedPart
  let no_impl_expr = error @@ NotImplementedExpression
  let not_impl_h_lvl = error @@ NotImplementedHightLvl
  let exp_let = error @@ ExpectedLet
  let constr_sig = error @@ UnexpectedConstructSig
  let no_constr constr = error @@ NoSuchConstr constr
  let unsup_core = error @@ UnsupportedCoreType
  let not_impl_t_d = error @@ NotImplementedType
  let ph = error @@ PlaceHolder
end

(********************tests********************)

(*****************ground_typ_tests************)
let gr_test = pp_ground_typ Format.std_formatter

let%expect_test _ =
  gr_test @@ int_t;
  [%expect {| Int |}]

let%expect_test _ =
  gr_test @@ string_t;
  [%expect {| String |}]

let%expect_test _ =
  gr_test @@ char_t;
  [%expect {| Char |}]

let%expect_test _ =
  gr_test @@ bool_t;
  [%expect {| Bool |}]

let%expect_test _ =
  gr_test @@ float_t;
  [%expect {| Float |}]

(*****************tv_tests********************)
let tv_test = pp_tv Format.std_formatter

let%expect_test _ =
  tv_test @@ unbound "name" 1 [];
  [%expect {| (Unbound ("name", 1, [])) |}]

let%expect_test _ =
  tv_test @@ link (tgronud int_t []) [];
  [%expect {| (Link ((TGround (Int, [])), [])) |}]

(****************typ_tests********************)
let typ_test = pp_typ Format.std_formatter
let tt = tgronud int_t []
let lvls = { new_lvl = 0; old_lvl = 0 }

let%expect_test _ =
  typ_test @@ tvar_unbound (unbound "name" 1 []) [];
  [%expect {| (TVar (ref ((Unbound ("name", 1, []))), [])) |}]

let%expect_test _ =
  typ_test @@ tvar_link (link tt []) [];
  [%expect {| (TVar (ref ((Link ((TGround (Int, [])), []))), [])) |}]

let%expect_test _ =
  typ_test @@ tarrow tt tt lvls [];
  [%expect
    {|
    (TArrow ((TGround (Int, [])), (TGround (Int, [])),
       { old_lvl = 0; new_lvl = 0 }, [])) |}]

let%expect_test _ =
  typ_test @@ tgronud int_t [];
  [%expect {| (TGround (Int, [])) |}]

let%expect_test _ =
  typ_test @@ tpoly "name" [] lvls [];
  [%expect {| (TPoly ("name", [], { old_lvl = 0; new_lvl = 0 }, [])) |}]

let%expect_test _ =
  typ_test @@ ttuple [] lvls [];
  [%expect {| (TTuple ([], { old_lvl = 0; new_lvl = 0 }, [])) |}]

(************reasons_tests********************)
let res_test = pp_reasons Format.std_formatter

let%expect_test _ =
  res_test @@ reasons NoReason;
  [%expect {| [NoReason] |}]

let%expect_test _ =
  typ_test
  @@ map_reason (fun _ -> no_reason) (tvar_unbound (unbound "name" 1 []) []);
  [%expect {| (TVar (ref ((Unbound ("name", 1, [NoReason]))), [])) |}]

let%expect_test _ =
  typ_test @@ map_reason (fun _ -> no_reason) (tvar_link (link tt []) []);
  [%expect {| (TVar (ref ((Link ((TGround (Int, [NoReason])), []))), [])) |}]

let%expect_test _ =
  typ_test @@ map_reason (fun _ -> no_reason) (tarrow tt tt lvls []);
  [%expect
    {|
    (TArrow ((TGround (Int, [])), (TGround (Int, [])),
       { old_lvl = 0; new_lvl = 0 }, [NoReason])) |}]

let%expect_test _ =
  typ_test @@ map_reason (fun _ -> no_reason) tt;
  [%expect {| (TGround (Int, [NoReason])) |}]

let%expect_test _ =
  typ_test @@ map_reason (fun _ -> no_reason) (tpoly "name" [] lvls []);
  [%expect {| (TPoly ("name", [], { old_lvl = 0; new_lvl = 0 }, [NoReason])) |}]

let%expect_test _ =
  typ_test @@ map_reason (fun _ -> no_reason) (ttuple [] lvls []);
  [%expect {| (TTuple ([], { old_lvl = 0; new_lvl = 0 }, [NoReason])) |}]

let%expect_test _ =
  typ_test
  @@ map_reasons (fun _ -> no_reason) (tvar_unbound (unbound "name" 1 []) []);
  [%expect {| (TVar (ref ((Unbound ("name", 1, [NoReason]))), [NoReason])) |}]

let%expect_test _ =
  typ_test @@ map_reasons (fun _ -> no_reason) (tvar_link (link tt []) []);
  [%expect {| (TVar (ref ((Link ((TGround (Int, [NoReason])), [NoReason]))), [NoReason])) |}]

let%expect_test _ =
  typ_test @@ map_reasons (fun _ -> no_reason) (tarrow tt tt lvls []);
  [%expect
    {|
    (TArrow ((TGround (Int, [NoReason])), (TGround (Int, [NoReason])),
       { old_lvl = 0; new_lvl = 0 }, [NoReason])) |}]

let%expect_test _ =
  typ_test @@ map_reasons (fun _ -> no_reason) tt;
  [%expect {| (TGround (Int, [NoReason])) |}]

let%expect_test _ =
  typ_test @@ map_reasons (fun _ -> no_reason) (tpoly "name" [] lvls []);
  [%expect {| (TPoly ("name", [], { old_lvl = 0; new_lvl = 0 }, [NoReason])) |}]

let%expect_test _ =
  typ_test @@ map_reasons (fun _ -> no_reason) (ttuple [] lvls []);
  [%expect {| (TTuple ([], { old_lvl = 0; new_lvl = 0 }, [NoReason])) |}]

let%expect_test _ =
  typ_test @@ clear_reasons (tgronud int_t no_reason);
  [%expect {| (TGround (Int, [])) |}]

let%expect_test _ =
  typ_test @@ concat_reasons tt no_reason;
  [%expect {| (TGround (Int, [NoReason])) |}]

let%expect_test _ =
  typ_test @@ add_reason tt NoReason;
  [%expect {| (TGround (Int, [NoReason])) |}]

let%expect_test _ =
  res_test @@ take_reasons tt;
  [%expect {| [] |}]

let%expect_test _ =
  res_test @@ take_reasons (tvar_unbound (unbound "name" 1 []) no_reason);
  [%expect {| [NoReason] |}]

let%expect_test _ =
  res_test @@ take_reasons (tarrow tt tt lvls no_reason);
  [%expect {| [NoReason] |}]

let%expect_test _ =
  res_test @@ take_reasons (tpoly "name" [] lvls no_reason);
  [%expect {| [NoReason] |}]

let%expect_test _ =
  res_test @@ take_reasons (ttuple [] lvls no_reason);
  [%expect {| [NoReason] |}]

let%expect_test _ =
  typ_test @@ new_reasons tt no_reason;
  [%expect {| (TGround (Int, [NoReason])) |}]