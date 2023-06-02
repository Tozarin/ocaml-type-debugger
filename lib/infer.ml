(** Copyright 2023, Startsev Matvey *)

(** SPDX-License-Identifier: LGPL-3.0-or-later *)

open Parsetree
open Location
open Infertypes
open Res

let generic_lvl = 100500
let marked_lvl = -1

let rec repr = function
  | TVar (({ contents = Link (t, tr_link) } as tvr), tr_tvar) ->
      let t = repr t in
      tvr := Link (t, tr_link);
      concat_reasons t tr_tvar
  | t -> t

let get_lvl : typ -> lvl = function
  | TVar ({ contents = Unbound (_, l, _) }, _) -> l
  | TArrow (_, _, ls, _) | TPoly (_, _, ls, _) | TTuple (_, ls, _) -> ls.new_lvl
  | _ -> 0

let gensym_counter = ref 0
let reset_gensym () = gensym_counter := 0

let gensym () =
  let n = !gensym_counter in
  let () = incr gensym_counter in
  if n < 26 then String.make 1 (Char.chr (Char.code 'a' + n))
  else "t" ^ string_of_int n

let curr_lvl = ref 0
let reset_curr_lvl () = curr_lvl := 0

let reset_typ_vars () =
  reset_gensym ();
  reset_curr_lvl ()

let enter_lvl () = incr curr_lvl
let leave_lvl () = decr curr_lvl

let newvar () rs =
  let name = gensym () in
  tvar_unbound (unbound name !curr_lvl rs) []

let new_arrow t1 t2 rs =
  tarrow t1 t2 { new_lvl = !curr_lvl; old_lvl = !curr_lvl } rs

let new_poly name ts rs =
  tpoly name ts { new_lvl = !curr_lvl; old_lvl = !curr_lvl } rs

let new_tuple ts rs = ttuple ts { new_lvl = !curr_lvl; old_lvl = !curr_lvl } rs

let rec cyc_free = function
  | TVar ({ contents = Unbound _ }, _) | TGround _ -> return ()
  | TVar ({ contents = Link (ty, _) }, _) -> cyc_free ty
  | (TArrow (_, _, ls, _) | TPoly (_, _, ls, _) | TTuple (_, ls, _))
    when ls.new_lvl = marked_lvl ->
      occurs_fail
  | TArrow (t1, t2, ls, _) ->
      let lvl = ls.new_lvl in
      ls.new_lvl <- marked_lvl;
      cyc_free t1 *> cyc_free t2 *> return (ls.new_lvl <- lvl)
  | TPoly (_, ts, ls, _) | TTuple (ts, ls, _) ->
      let lvl = ls.new_lvl in
      ls.new_lvl <- marked_lvl;
      List.fold_left (fun acc t -> acc *> cyc_free t) (return ()) ts
      *> return (ls.new_lvl <- lvl)

let lvls_to_update = ref []
let reset_lvls_to_update () = lvls_to_update := []

let update_lvl l = function
  | TVar (({ contents = Unbound (t, l', tr) } as tvr), _) ->
      if l' = generic_lvl then miss_invar
      else if l < l' then return (tvr := Unbound (t, l, tr))
      else return ()
  | (TArrow (_, _, ls, _) | TPoly (_, _, ls, _) | TTuple (_, ls, _)) as t ->
      if ls.new_lvl = generic_lvl then miss_invar
      else if ls.new_lvl = marked_lvl then occurs_fail
      else if l < ls.new_lvl then
        if ls.new_lvl = ls.old_lvl then
          return (lvls_to_update := t :: !lvls_to_update)
          *> return (ls.new_lvl <- l)
        else return ()
      else return ()
  | _ -> return ()

let force_lvls_update () =
  let rec helper acc level ty =
    match repr ty with
    | TVar (({ contents = Unbound (name, l, tr) } as tvr), _) when l > level ->
        tvr := Unbound (name, level, tr);
        acc
    | (TArrow (_, _, ls, _) | TPoly (_, _, ls, _) | TTuple (_, ls, _))
      when ls.new_lvl = marked_lvl ->
        occurs_fail
    | (TArrow (_, _, ls, _) | TPoly (_, _, ls, _) | TTuple (_, ls, _)) as ty ->
        if ls.new_lvl > level then ls.new_lvl <- level;
        update_one acc ty
    | _ -> acc
  and update_one acc = function
    | (TArrow (_, _, ls, _) | TPoly (_, _, ls, _) | TTuple (_, ls, _)) as ty
      when ls.old_lvl <= !curr_lvl ->
        let* acc = acc in
        return (ty :: acc)
    | (TArrow (_, _, ls, _) | TPoly (_, _, ls, _) | TTuple (_, ls, _))
      when ls.old_lvl = ls.new_lvl ->
        acc
    | TArrow (ty1, ty2, ls, _) ->
        let lvl = ls.new_lvl in
        ls.new_lvl <- marked_lvl;
        let acc = helper acc lvl ty1 in
        let acc = helper acc lvl ty2 in
        ls.new_lvl <- lvl;
        ls.old_lvl <- lvl;
        acc
    | TPoly (_, ts, ls, _) | TTuple (ts, ls, _) ->
        let lvl = ls.new_lvl in
        ls.new_lvl <- marked_lvl;
        let acc = List.fold_left (fun acc t -> helper acc lvl t) acc ts in
        ls.new_lvl <- lvl;
        ls.old_lvl <- lvl;
        acc
    | _ -> ph
  in
  let* ls_to_update = List.fold_left update_one (return []) !lvls_to_update in
  return (lvls_to_update := ls_to_update)

let rec unify t1 t2 =
  if t1 == t2 then return ()
  else
    match (repr t1, repr t2) with
    | ( (TVar (({ contents = Unbound (_, l1, tr1) } as tv1), _) as t1),
        (TVar (({ contents = Unbound (_, l2, tr2) } as tv2), _) as t2) ) ->
        if tv1 == tv2 then return ()
        else if l1 > l2 then return (tv1 := Link (t2, tr2 @ tr1))
        else return (tv2 := Link (t1, tr1 @ tr2))
    | TVar (({ contents = Unbound (_, l, tr) } as tv), _), t
    | t, TVar (({ contents = Unbound (_, l, tr) } as tv), _) ->
        update_lvl l t *> return (tv := Link (t, take_reasons t @ tr))
    | TArrow (l_ty1, l_ty2, l_ls, _), TArrow (r_ty1, r_ty2, r_ls, _) ->
        if l_ls.new_lvl = marked_lvl || r_ls.new_lvl = marked_lvl then
          occurs_fail
        else
          let min_level = min l_ls.new_lvl r_ls.new_lvl in
          l_ls.new_lvl <- marked_lvl;
          r_ls.new_lvl <- marked_lvl;
          unify_lev min_level l_ty1 r_ty1
          *> unify_lev min_level l_ty2 r_ty2
          *> return
               (l_ls.new_lvl <- min_level;
                r_ls.new_lvl <- min_level)
    | TPoly (l_name, _, _, _), TPoly (r_name, _, _, _) when l_name <> r_name ->
        unify_fail t1 t2
    | TPoly (_, l_ts, l_ls, _), TPoly (_, r_ts, r_ls, _)
    | TTuple (l_ts, l_ls, _), TTuple (r_ts, r_ls, _) ->
        if l_ls.new_lvl = marked_lvl || r_ls.new_lvl = marked_lvl then
          occurs_fail
        else
          let min_level = min l_ls.new_lvl r_ls.new_lvl in
          l_ls.new_lvl <- marked_lvl;
          r_ls.new_lvl <- marked_lvl;
          List.fold_left2
            (fun acc l_t r_t -> acc *> unify_lev min_level l_t r_t)
            (return ()) l_ts r_ts
          *> return
               (l_ls.new_lvl <- min_level;
                r_ls.new_lvl <- min_level)
    | TGround (t1, _), TGround (t2, _) when t1 = t2 -> return ()
    | _ -> unify_fail t1 t2

and unify_lev l ty1 ty2 =
  let ty1 = repr ty1 in
  update_lvl l ty1 *> unify ty1 ty2

let gen t =
  let rec helper t =
    match repr t with
    | TVar (({ contents = Unbound (name, l, tr) } as tvr), _) when l > !curr_lvl
      ->
        tvr := Unbound (name, generic_lvl, tr)
    | TArrow (t1, t2, ls, _) when ls.new_lvl > !curr_lvl ->
        let t1 = repr t1 and t2 = repr t2 in
        helper t1;
        helper t2;
        let l = max (get_lvl t1) (get_lvl t2) in
        ls.old_lvl <- l;
        ls.new_lvl <- l
    | (TPoly (_, ts, ls, _) | TTuple (ts, ls, _)) when ls.new_lvl > !curr_lvl ->
        let l =
          List.fold_left
            (fun acc t ->
              let t = repr t in
              helper t;
              max acc (get_lvl t))
            0 ts
        in
        ls.old_lvl <- l;
        ls.new_lvl <- l
    | _ -> ()
  in
  force_lvls_update () *> return (helper t)

type env = (name * typ) list

let inst =
  let rec helper sb = function
    | TVar ({ contents = Unbound (name, l, tr) }, tr_tvar) when l = generic_lvl
      -> (
        try (List.assoc name sb, sb)
        with Not_found ->
          let t = newvar () (tr_tvar @ tr) in
          (t, (name, t) :: sb))
    | TVar ({ contents = Link (t, tr) }, tr_tvar) ->
        (* helper sb (concat_reasons t (tr_tvar @ tr)) *)
        helper sb (map_reason (fun _ -> tr_tvar @ tr) t)
    | TArrow (t1, t2, ls, tr) when ls.new_lvl = generic_lvl ->
        let t1, sb = helper sb t1 in
        let t2, sb = helper sb t2 in
        (new_arrow t1 t2 tr, sb)
    | TPoly (name, ts, ls, rs) when ls.new_lvl = generic_lvl ->
        let ts, sb =
          List.fold_right
            (fun t (ts, sb) ->
              let t, sb = helper sb t in
              (t :: ts, sb))
            ts ([], sb)
        in
        (new_poly name ts rs, sb)
    | TTuple (ts, ls, rs) when ls.new_lvl = generic_lvl ->
        let ts, sb =
          List.fold_right
            (fun t (ts, sb) ->
              let t, sb = helper sb t in
              (t :: ts, sb))
            ts ([], sb)
        in
        (new_tuple ts rs, sb)
    | t -> (t, sb)
  in
  fun t -> fst (helper [] t)

let match_const = function
  | Pconst_integer _ -> Int
  | Pconst_char _ -> Char
  | Pconst_string _ -> String
  | Pconst_float _ -> Float

let eq_const c1 c2 = match_const c1 = match_const c2

let arg_res_fun f loc =
  let apply_as n f loc = ApplyAs (n, clear_reasons f, loc) in
  let rec helper n = function
    | TArrow (l, (TArrow _ as r), lvl, tr) ->
        let l = add_reason l (apply_as n f loc) in
        let n, r = helper (n + 1) r in
        (n, tarrow l r lvl tr)
    | TArrow (l, r, lvl, tr) ->
        let l = add_reason l (apply_as n f loc) in
        let r = add_reason r (apply_as (n + 1) f loc) in
        (n + 2, tarrow l r lvl tr)
    | t -> (n, t)
  in
  snd @@ helper 1 f

let count_of_args e =
  let rec helper n = function
    | Pexp_fun (_, _, _, body) -> helper (n + 1) body.pexp_desc
    | _ -> n
  in
  helper 0 e

let gen_fun n loc =
  let rec helper = function
    | 0 -> newvar () (rec_dec loc)
    | n -> new_arrow (newvar () (rec_dec loc)) (helper (n - 1)) (rec_dec loc)
  in
  helper n

let rec ppat env p t =
  let loc = p.ppat_loc in
  match (p.ppat_desc, t) with
  | Ppat_any, t -> return (new_reasons t (pat_any loc), env)
  | Ppat_var var, t ->
      let t = add_reason t (PatAnyVar loc) in
      return (t, (var.txt, t) :: env)
  | Ppat_constant c, _ ->
      let c = match_const c in
      return (tgronud c (pat_const c loc), env)
  | Ppat_interval (c1, c2), _ ->
      let c = match_const c1 in
      if eq_const c1 c2 then return (tgronud c (pat_interval_const c loc), env)
      else interval_pat_fail
  | Ppat_tuple ps, TTuple (ts, _, rs) ->
      let* ts, env =
        List.fold_right2
          (fun p t acc ->
            let* acc, env = acc in
            let* t, env = ppat env p t in
            return (t :: acc, env))
          ps ts
          (return ([], env))
      in
      return (new_tuple ts (pat_tuple loc @ rs), env)
  | Ppat_tuple ps, _ ->
      let ts = List.map (fun _ -> newvar () []) ps in
      let t = new_tuple ts [] in
      ppat env p t
  | Ppat_construct (id, ps), _ -> (
      let id = String.concat "." (Longident.flatten id.txt) in
      let* t =
        try return @@ inst (List.assoc id env) with Not_found -> no_constr id
      in
      match (t, ps) with
      | (TPoly _ as t), None -> return (new_reasons t (pat_constr id loc), env)
      | TArrow (t, res, _, _), Some ps ->
          let _, p = ps in
          let* _, env = ppat env p t in
          return (new_reasons res (pat_constr id loc), env)
      | _ -> constr_sig)
  | _ -> not_impl_pat

let tof =
  let rec helper : env -> expression -> typ Res.t =
   fun env expr ->
    let loc = expr.pexp_loc in
    let expr = expr.pexp_desc in
    match expr with
    | Pexp_constant c ->
        let c = match_const c in
        return @@ tgronud c (init_const c loc)
    | Pexp_ident id ->
        let id = String.concat "." (Longident.flatten id.txt) in
        let* t =
          try return @@ inst (List.assoc id env) with Not_found -> no_fun id
        in
        return @@ concat_reasons t (result_of id loc)
    | Pexp_tuple es ->
        let* ts =
          List.fold_right
            (fun e acc ->
              let* acc = acc in
              let* e = helper env e in
              return (e :: acc))
            es (return [])
        in
        return @@ new_tuple ts (init_tuple loc)
    | Pexp_fun (_, _, arg, body) ->
        let* t_arg, env = ppat env arg (newvar () []) in
        let* t_body = helper env body in
        return @@ new_arrow t_arg t_body (nl_fun loc)
    | Pexp_apply (expr, args) ->
        let* t_fun = helper env expr in
        let t_fun = arg_res_fun t_fun loc in
        let* t_args =
          List.fold_right
            (fun (_, e) acc ->
              let* acc = acc in
              let* e = helper env e in
              return (e :: acc))
            args (return [])
        in
        let t_res = newvar () (res_of_nameless loc) in
        let t_args =
          List.fold_right (fun e acc -> new_arrow e acc no_reason) t_args t_res
        in
        unify t_fun t_args *> return t_res
    | Pexp_let (Recursive, v_bs, expr) ->
        let* env =
          List.fold_left
            (fun env v ->
              enter_lvl ();
              let p = v.pvb_pat in
              let e = v.pvb_expr in
              let rec_t = gen_fun (count_of_args e.pexp_desc) loc in
              let* env = env in
              let* _, env =
                ppat env p rec_t
                (* match p.ppat_desc with
                   | Ppat_any -> return env
                   | Ppat_var id -> return ((id.txt, rec_t) :: env)
                   | _ -> rec_no_impl *)
              in
              let* t_e = helper env e in
              unify t_e rec_t *> return (leave_lvl ()) *> gen t_e *> return env)
            (return env) v_bs
        in
        helper env expr
    | Pexp_let (Nonrecursive, v_bs, expr) ->
        let* env =
          List.fold_left
            (fun env v ->
              enter_lvl ();
              let e = v.pvb_expr in
              let p = v.pvb_pat in
              let* env = env in
              let* t_e = helper env e in
              let* arg, env = ppat env p t_e in
              unify t_e arg *> return (leave_lvl ()) *> gen t_e *> return env)
            (return env) v_bs
        in
        helper env expr
    | Pexp_match (expr, cs) ->
        let* e_match = helper env expr in
        List.fold_left
          (fun acc case ->
            let* acc = acc in
            let* p_t, env = ppat env case.pc_lhs (newvar () []) in
            unify e_match p_t
            *> let* case_e = helper env case.pc_rhs in
               unify (inst acc) case_e *> return acc
            (* match case.pc_guard with
               | None -> ()
               | Some e -> (match helper env e with _ -> ())); *))
          (return (newvar () (res_of_pm loc)))
          cs
    | Pexp_construct (id, es) -> (
        let id = String.concat "." (Longident.flatten id.txt) in
        let* t =
          try return @@ inst (List.assoc id env)
          with Not_found -> no_constr id
        in
        match (t, es) with
        | (TPoly _ as t), None -> return (add_reason t (ResOfConstr (id, loc)))
        | TArrow (t, (TPoly _ as res), _, _), Some arg ->
            let* arg = helper env arg in
            unify t arg *> return (add_reason res (ResOfConstr (id, loc)))
        | _ -> constr_sig)
    | _ -> no_impl_expr
  in
  helper

let let_value env loc = function
  | Pstr_value (Recursive, v_bs) ->
      List.fold_left
        (fun env v ->
          enter_lvl ();
          let p = v.pvb_pat in
          let e = v.pvb_expr in
          let rec_t = gen_fun (count_of_args e.pexp_desc) loc in
          let* env = env in
          let* env =
            match p.ppat_desc with
            | Ppat_any -> return env
            | Ppat_var id -> return ((id.txt, rec_t) :: env)
            | _ -> rec_no_impl
          in
          let* t_e = tof env e in
          unify t_e rec_t *> return (leave_lvl ()) *> gen t_e *> return env)
        (return env) v_bs
  | Pstr_value (Nonrecursive, v_bs) ->
      List.fold_left
        (fun env v ->
          enter_lvl ();
          let e = v.pvb_expr in
          let p = v.pvb_pat in
          let* env = env in
          let* t_e = tof env e in
          let* arg, env = ppat env p (newvar () []) in
          unify t_e arg *> return (leave_lvl ()) *> gen t_e *> return env)
        (return env) v_bs
  | _ -> exp_let

let top_infer env expr =
  reset_typ_vars ();
  reset_lvls_to_update ();
  match expr.pstr_desc with
  | Pstr_eval (expr, _) -> (tof env expr >>| cyc_free) *> return env
  | Pstr_value _ as v -> let_value env expr.pstr_loc v
  | _ -> not_impl_h_lvl

let rec from_core = function
  | Ptyp_any -> return @@ newvar () []
  | Ptyp_var name -> return @@ tvar_unbound (unbound name 0 []) []
  | Ptyp_arrow (_, { ptyp_desc = l; _ }, { ptyp_desc = r; _ }) ->
      let* l = from_core l in
      let* r = from_core r in
      return @@ new_arrow l r []
  | Ptyp_tuple ls ->
      let* ts =
        List.fold_right
          (fun { ptyp_desc = t; _ } acc ->
            let* acc = acc in
            let* t = from_core t in
            return @@ (t :: acc))
          ls (return [])
      in
      return @@ new_tuple ts []
  | Ptyp_constr (id, cs) -> (
      match (String.concat "." (Longident.flatten id.txt), cs) with
      | "int", [] -> return @@ tgronud int_t []
      | "string", [] -> return @@ tgronud string_t []
      | "float", [] -> return @@ tgronud float_t []
      | "char", [] -> return @@ tgronud char_t []
      | "bool", [] -> return @@ tgronud bool_t []
      | name, cs ->
          let* ts =
            List.fold_right
              (fun { ptyp_desc = t; _ } acc ->
                let* acc = acc in
                let* t = from_core t in
                return @@ (t :: acc))
              cs (return [])
          in
          return @@ new_poly name ts [])
  | _ -> unsup_core

(********************tests********************)

let tt = tgronud int_t []
let ll = link tt []
let tl = tvar_link ll []
let typ_test = pp_typ Format.std_formatter
let lvls = { new_lvl = 0; old_lvl = 0 }
let arr = tarrow tt tt lvls []
let pol = tpoly "name" [] lvls []
let tup = ttuple [] lvls []

let%expect_test _ =
  typ_test @@ repr tl;
  [%expect {| (TGround (Int, [])) |}]

let%expect_test _ =
  typ_test @@ repr tt;
  [%expect {| (TGround (Int, [])) |}]

let%expect_test _ =
  print_int @@ get_lvl (tvar_unbound (unbound "name" 1 []) []);
  [%expect {| 1 |}]

let%expect_test _ =
  print_int @@ get_lvl tt;
  [%expect {| 0 |}]

let%expect_test _ =
  print_int @@ get_lvl arr;
  [%expect {| 0 |}]

let%expect_test _ =
  print_int @@ get_lvl pol;
  [%expect {| 0 |}]

let%expect_test _ =
  print_int @@ get_lvl tup;
  [%expect {| 0 |}]

let%expect_test _ =
  reset_gensym ();
  print_int !gensym_counter;
  [%expect {| 0 |}]

let%expect_test _ =
  print_string @@ gensym ();
  [%expect {| a |}]

let%expect_test _ =
  let rec loop = function
    | n when n < 26 ->
        let _ = gensym () in
        loop @@ (n + 1)
    | _ -> gensym ()
  in
  print_string @@ loop 0;
  [%expect {| t27 |}]

let%expect_test _ =
  reset_typ_vars ();
  print_int !curr_lvl;
  [%expect {| 0 |}]

let%expect_test _ =
  enter_lvl ();
  print_int !curr_lvl;
  [%expect {| 1 |}]

let%expect_test _ =
  leave_lvl ();
  print_int !curr_lvl;
  [%expect {| 0 |}]

let%expect_test _ =
  typ_test @@ newvar () [];
  [%expect {| (TVar (ref ((Unbound ("a", 0, []))), [])) |}]

let%expect_test _ =
  typ_test @@ new_arrow tt tt [];
  [%expect
    {|
    (TArrow ((TGround (Int, [])), (TGround (Int, [])),
       { old_lvl = 0; new_lvl = 0 }, [])) |}]

let%expect_test _ =
  typ_test @@ new_poly "name" [] [];
  [%expect {| (TPoly ("name", [], { old_lvl = 0; new_lvl = 0 }, [])) |}]

let%expect_test _ =
  typ_test @@ new_tuple [] [];
  [%expect {| (TTuple ([], { old_lvl = 0; new_lvl = 0 }, [])) |}]

(***********cyc_free tests********************)

let c_test t =
  match cyc_free t with Error err -> pp_err Format.std_formatter err | _ -> ()

let%expect_test _ =
  c_test tt;
  [%expect {||}]

let%expect_test _ =
  c_test @@ tvar_unbound (unbound "name" 1 []) [];
  [%expect {||}]

let%expect_test _ =
  c_test tl;
  [%expect {||}]

let%expect_test _ =
  c_test arr;
  [%expect {||}]

let%expect_test _ =
  c_test pol;
  [%expect {||}]

let%expect_test _ =
  c_test tup;
  [%expect {||}]

let m_lvl = { new_lvl = marked_lvl; old_lvl = 0 }

let%expect_test _ =
  c_test @@ tarrow tt tt m_lvl [];
  [%expect {| OccursFail |}]

let%expect_test _ =
  c_test @@ tpoly "name" [] m_lvl [];
  [%expect {| OccursFail |}]

let%expect_test _ =
  c_test @@ ttuple [] m_lvl [];
  [%expect {| OccursFail |}]

(********************tests********************)

let%expect_test _ =
  reset_lvls_to_update ();
  (match !lvls_to_update with
  | [] -> print_string "ok"
  | _ -> print_string "err");
  [%expect {| ok |}]

(********************tests********************)

let upd_test t l =
  let fmt = Format.std_formatter in
  match update_lvl l t with Ok _ -> pp_typ fmt t | Error err -> pp_err fmt err

let%expect_test _ =
  upd_test tt 5;
  [%expect {| (TGround (Int, [])) |}]

let%expect_test _ =
  upd_test (tvar_unbound (unbound "name" 10 []) []) 5;
  [%expect {| (TVar (ref ((Unbound ("name", 5, []))), [])) |}]

let%expect_test _ =
  upd_test (tvar_unbound (unbound "name" 0 []) []) 5;
  [%expect {| (TVar (ref ((Unbound ("name", 0, []))), [])) |}]

let%expect_test _ =
  upd_test (tvar_unbound (unbound "name" generic_lvl []) []) 5;
  [%expect {| MissingInvariant |}]

let%expect_test _ =
  upd_test (tarrow tt tt { new_lvl = generic_lvl; old_lvl = 0 } []) 5;
  [%expect {| MissingInvariant |}]

let%expect_test _ =
  upd_test (tarrow tt tt { new_lvl = marked_lvl; old_lvl = 0 } []) 5;
  [%expect {| OccursFail |}]

let%expect_test _ =
  upd_test (tarrow tt tt { new_lvl = 10; old_lvl = 0 } []) 5;
  [%expect
    {|
    (TArrow ((TGround (Int, [])), (TGround (Int, [])),
       { old_lvl = 0; new_lvl = 10 }, [])) |}]

let%expect_test _ =
  upd_test (tarrow tt tt { new_lvl = 0; old_lvl = 0 } []) 5;
  [%expect
    {|
    (TArrow ((TGround (Int, [])), (TGround (Int, [])),
       { old_lvl = 0; new_lvl = 0 }, [])) |}]

let%expect_test _ =
  upd_test (tarrow tt tt { new_lvl = 10; old_lvl = 10 } []) 5;
  reset_lvls_to_update ();
  [%expect
    {|
    (TArrow ((TGround (Int, [])), (TGround (Int, [])),
       { old_lvl = 10; new_lvl = 5 }, [])) |}]

let%expect_test _ =
  upd_test (tpoly "name" [] { new_lvl = 10; old_lvl = 0 } []) 5;
  [%expect {|
    (TPoly ("name", [], { old_lvl = 0; new_lvl = 10 }, [])) |}]

let%expect_test _ =
  upd_test (tpoly "name" [] { new_lvl = 0; old_lvl = 0 } []) 5;
  [%expect {|
    (TPoly ("name", [], { old_lvl = 0; new_lvl = 0 }, [])) |}]

let%expect_test _ =
  upd_test (tpoly "name" [] { new_lvl = 10; old_lvl = 10 } []) 5;
  reset_lvls_to_update ();
  [%expect {|
    (TPoly ("name", [], { old_lvl = 10; new_lvl = 5 }, [])) |}]

let%expect_test _ =
  upd_test (ttuple [] { new_lvl = 10; old_lvl = 0 } []) 5;
  [%expect {|
    (TTuple ([], { old_lvl = 0; new_lvl = 10 }, [])) |}]

let%expect_test _ =
  upd_test (ttuple [] { new_lvl = 0; old_lvl = 0 } []) 5;
  [%expect {|
    (TTuple ([], { old_lvl = 0; new_lvl = 0 }, [])) |}]

let%expect_test _ =
  upd_test (ttuple [] { new_lvl = 10; old_lvl = 10 } []) 5;
  reset_lvls_to_update ();
  [%expect {|
    (TTuple ([], { old_lvl = 10; new_lvl = 5 }, [])) |}]

(**************unify_tests********************)

let u_test t1 t2 =
  let fmt = Format.std_formatter in
  match unify t1 t2 with
  | Ok _ ->
      pp_typ fmt t1;
      pp_typ fmt t2
  | Error err -> pp_err fmt err

let%expect_test _ =
  u_test tt tt;
  [%expect {| (TGround (Int, []))(TGround (Int, [])) |}]

let%expect_test _ =
  let unb = unbound "name" 0 [] in
  u_test (tvar_unbound unb []) (tvar_unbound unb []);
  [%expect
    {|
    (TVar (ref ((Unbound ("name", 0, []))), []))(TVar (
                                                   ref ((Link (
                                                           (TVar (
                                                              ref ((Unbound (
                                                                      "name", 0,
                                                                      []))),
                                                              [])),
                                                           []))),
                                                   [])) |}]

let%expect_test _ =
  u_test
    (tvar_unbound (unbound "name" 0 []) [])
    (tvar_unbound (unbound "name" 1 []) []);
  [%expect
    {|
    (TVar (ref ((Unbound ("name", 0, []))), []))(TVar (
                                                   ref ((Link (
                                                           (TVar (
                                                              ref ((Unbound (
                                                                      "name", 0,
                                                                      []))),
                                                              [])),
                                                           []))),
                                                   [])) |}]

let%expect_test _ =
  u_test
    (tvar_unbound (unbound "name" 1 []) [])
    (tvar_unbound (unbound "name" 0 []) []);
  [%expect
    {|
    (TVar (ref ((Link ((TVar (ref ((Unbound ("name", 0, []))), [])), []))), []))(
    TVar (ref ((Unbound ("name", 0, []))), [])) |}]

let%expect_test _ =
  u_test (tvar_unbound (unbound "name" 0 []) []) tt;
  [%expect
    {|
    (TVar (ref ((Link ((TGround (Int, [])), []))), []))(TGround (Int, [])) |}]

let%expect_test _ =
  u_test tt (tvar_unbound (unbound "name" 0 []) []);
  [%expect
    {|
    (TGround (Int, []))(TVar (ref ((Link ((TGround (Int, [])), []))), [])) |}]

let%expect_test _ =
  u_test (tarrow tt tt m_lvl []) (tarrow tt tt lvls []);
  [%expect {|
    OccursFail |}]

let%expect_test _ =
  u_test (tarrow tt tt lvls []) (tarrow tt tt m_lvl []);
  [%expect {|
    OccursFail |}]

let%expect_test _ =
  u_test (tarrow tt tt lvls []) (tarrow tt tt lvls []);
  [%expect
    {|
    (TArrow ((TGround (Int, [])), (TGround (Int, [])),
       { old_lvl = 0; new_lvl = 0 }, []))(TArrow ((TGround (Int, [])),
                                            (TGround (Int, [])),
                                            { old_lvl = 0; new_lvl = 0 },
                                            [])) |}]

let%expect_test _ =
  u_test (tpoly "name1" [] lvls []) (tpoly "name2" [] lvls []);
  [%expect
    {|
      (UnifyFail ((TPoly ("name1", [], { old_lvl = 0; new_lvl = 0 }, [])),
         (TPoly ("name2", [], { old_lvl = 0; new_lvl = 0 }, [])))) |}]

let%expect_test _ =
  u_test (tpoly "name" [] m_lvl []) (tpoly "name" [] lvls []);
  [%expect {| OccursFail |}]

let%expect_test _ =
  u_test (tpoly "name" [] lvls []) (tpoly "name" [] m_lvl []);
  [%expect {| OccursFail |}]

let%expect_test _ =
  u_test (tpoly "name" [ tt ] lvls []) (tpoly "name" [ tt ] lvls []);
  [%expect
    {|
      (TPoly ("name", [(TGround (Int, []))], { old_lvl = 0; new_lvl = 0 }, []))(
      TPoly ("name", [(TGround (Int, []))], { old_lvl = 0; new_lvl = 0 }, [])) |}]

let%expect_test _ =
  u_test (ttuple [] m_lvl []) (ttuple [] lvls []);
  [%expect {| OccursFail |}]

let%expect_test _ =
  u_test (ttuple [] lvls []) (ttuple [] m_lvl []);
  [%expect {| OccursFail |}]

let%expect_test _ =
  u_test (ttuple [ tt ] lvls []) (ttuple [ tt ] lvls []);
  [%expect
    {|
      (TTuple ([(TGround (Int, []))], { old_lvl = 0; new_lvl = 0 }, []))(TTuple (
                                                                          [(TGround (
                                                                          Int,
                                                                          []))],
                                                                          { old_lvl =
                                                                          0;
                                                                          new_lvl =
                                                                          0 },
                                                                          [])) |}]

let%expect_test _ =
  u_test (tgronud int_t []) (tgronud int_t []);
  [%expect {| (TGround (Int, []))(TGround (Int, [])) |}]

let%expect_test _ =
  u_test tt arr;
  [%expect
    {|
      (UnifyFail ((TGround (Int, [])),
         (TArrow ((TGround (Int, [])), (TGround (Int, [])),
            { old_lvl = 0; new_lvl = 0 }, []))
         )) |}]

(****************gen_tests********************)

let g_test t =
  let fmt = Format.std_formatter in
  match gen t with Ok _ -> pp_typ fmt t | Error err -> pp_err fmt err

let%expect_test _ =
  g_test @@ tvar_unbound (unbound "name" 10 []) [];
  [%expect {| (TVar (ref ((Unbound ("name", 100500, []))), [])) |}]

let%expect_test _ =
  g_test @@ tvar_unbound (unbound "name" 0 []) [];
  [%expect {| (TVar (ref ((Unbound ("name", 0, []))), [])) |}]

let%expect_test _ =
  g_test arr;
  [%expect
    {|
    (TArrow ((TGround (Int, [])), (TGround (Int, [])),
       { old_lvl = 0; new_lvl = 0 }, [])) |}]

let%expect_test _ =
  g_test @@ tarrow tt tt { new_lvl = 10; old_lvl = 0 } [];
  [%expect
    {|
    (TArrow ((TGround (Int, [])), (TGround (Int, [])),
       { old_lvl = 0; new_lvl = 0 }, [])) |}]

let%expect_test _ =
  g_test tt;
  [%expect {| (TGround (Int, [])) |}]

let%expect_test _ =
  g_test @@ tpoly "name" [] lvls [];
  [%expect {| (TPoly ("name", [], { old_lvl = 0; new_lvl = 0 }, [])) |}]

let%expect_test _ =
  g_test @@ tpoly "name" [ tt ] { new_lvl = 10; old_lvl = 0 } [];
  [%expect
    {| (TPoly ("name", [(TGround (Int, []))], { old_lvl = 0; new_lvl = 0 }, [])) |}]

let%expect_test _ =
  g_test @@ ttuple [] lvls [];
  [%expect {| (TTuple ([], { old_lvl = 0; new_lvl = 0 }, [])) |}]

let%expect_test _ =
  g_test @@ ttuple [ tt ] { new_lvl = 10; old_lvl = 0 } [];
  [%expect
    {| (TTuple ([(TGround (Int, []))], { old_lvl = 0; new_lvl = 0 }, [])) |}]

(***************inst_tests********************)

let i_test t = pp_typ Format.std_formatter (inst t)

let%expect_test _ =
  i_test @@ tvar_unbound (unbound "name" generic_lvl []) [];
  [%expect {| (TVar (ref ((Unbound ("b", 0, []))), [])) |}]

let%expect_test _ =
  i_test tt;
  [%expect {| (TGround (Int, [])) |}]

let%expect_test _ =
  i_test tl;
  [%expect {| (TGround (Int, [])) |}]

let%expect_test _ =
  i_test @@ tarrow tt tt { new_lvl = generic_lvl; old_lvl = generic_lvl } [];
  [%expect
    {|
    (TArrow ((TGround (Int, [])), (TGround (Int, [])),
       { old_lvl = 0; new_lvl = 0 }, [])) |}]

let%expect_test _ =
  i_test
  @@ tpoly "name" [ tt ] { new_lvl = generic_lvl; old_lvl = generic_lvl } [];
  [%expect
    {| (TPoly ("name", [(TGround (Int, []))], { old_lvl = 0; new_lvl = 0 }, [])) |}]

let%expect_test _ =
  i_test @@ ttuple [ tt ] { new_lvl = generic_lvl; old_lvl = generic_lvl } [];
  [%expect
    {| (TTuple ([(TGround (Int, []))], { old_lvl = 0; new_lvl = 0 }, [])) |}]

(********************tests********************)

open Lexing

let get_code code =
  let s = List.hd @@ Parse.implementation (Lexing.from_string code) in
  match s.pstr_desc with Pstr_eval (expr, _) -> return expr | _ -> ph

let loc =
  let pos = { pos_fname = "name"; pos_lnum = 0; pos_bol = 0; pos_cnum = 0 } in
  { loc_start = pos; loc_end = pos; loc_ghost = false }

let mc_test c = pp_ground_typ Format.std_formatter (match_const c)

let%expect_test _ =
  mc_test @@ Pconst_integer ("1", None);
  [%expect {| Int |}]

let%expect_test _ =
  mc_test @@ Pconst_char 'c';
  [%expect {| Char |}]

let%expect_test _ =
  mc_test @@ Pconst_string ("string", loc, None);
  [%expect {| String |}]

let%expect_test _ =
  mc_test @@ Pconst_float ("1,2", None);
  [%expect {| Float |}]

let%expect_test _ =
  print_string
    (if eq_const (Pconst_char 'c') (Pconst_char 'c') then "ok" else "err");
  [%expect {| ok |}]

let%expect_test _ =
  pp_typ Format.std_formatter (gen_fun 2 loc);
  [%expect
    {|
    (TArrow (
       (TVar (
          ref ((Unbound ("e", 0, [(RecDef File "name", line 1, characters 0-0)]))),
          [])),
       (TArrow (
          (TVar (
             ref ((Unbound ("d", 0,
                     [(RecDef File "name", line 1, characters 0-0)]))),
             [])),
          (TVar (
             ref ((Unbound ("c", 0,
                     [(RecDef File "name", line 1, characters 0-0)]))),
             [])),
          { old_lvl = 0; new_lvl = 0 },
          [(RecDef File "name", line 1, characters 0-0)])),
       { old_lvl = 0; new_lvl = 0 },
       [(RecDef File "name", line 1, characters 0-0)])) |}]

let%expect_test _ =
  (match get_code {|fun x -> fun y -> fun z -> z|} with
  | Ok e -> print_int @@ count_of_args e.pexp_desc
  | Error err -> pp_err Format.std_formatter err);
  [%expect {| 3 |}]

let%expect_test _ =
  pp_typ Format.std_formatter (arg_res_fun tt loc);
  [%expect {| (TGround (Int, [])) |}]

let%expect_test _ =
  pp_typ Format.std_formatter (arg_res_fun (gen_fun 2 loc) loc);
  [%expect
    {|
    (TArrow (
       (TVar (
          ref ((Unbound ("h", 0,
                  [(ApplyAs (1,
                      (TArrow ((TVar (ref ((Unbound ("h", 0, []))), [])),
                         (TArrow ((TVar (ref ((Unbound ("g", 0, []))), [])),
                            (TVar (ref ((Unbound ("f", 0, []))), [])),
                            { old_lvl = 0; new_lvl = 0 }, [])),
                         { old_lvl = 0; new_lvl = 0 }, [])),
                      File "name", line 1, characters 0-0));
                    (RecDef File "name", line 1, characters 0-0)]
                  ))),
          [])),
       (TArrow (
          (TVar (
             ref ((Unbound ("g", 0,
                     [(ApplyAs (2,
                         (TArrow ((TVar (ref ((Unbound ("h", 0, []))), [])),
                            (TArrow ((TVar (ref ((Unbound ("g", 0, []))), [])),
                               (TVar (ref ((Unbound ("f", 0, []))), [])),
                               { old_lvl = 0; new_lvl = 0 }, [])),
                            { old_lvl = 0; new_lvl = 0 }, [])),
                         File "name", line 1, characters 0-0));
                       (RecDef File "name", line 1, characters 0-0)]
                     ))),
             [])),
          (TVar (
             ref ((Unbound ("f", 0,
                     [(ApplyAs (3,
                         (TArrow ((TVar (ref ((Unbound ("h", 0, []))), [])),
                            (TArrow ((TVar (ref ((Unbound ("g", 0, []))), [])),
                               (TVar (ref ((Unbound ("f", 0, []))), [])),
                               { old_lvl = 0; new_lvl = 0 }, [])),
                            { old_lvl = 0; new_lvl = 0 }, [])),
                         File "name", line 1, characters 0-0));
                       (RecDef File "name", line 1, characters 0-0)]
                     ))),
             [])),
          { old_lvl = 0; new_lvl = 0 },
          [(RecDef File "name", line 1, characters 0-0)])),
       { old_lvl = 0; new_lvl = 0 },
       [(RecDef File "name", line 1, characters 0-0)])) |}]

let tof_test code =
  match
    top_infer [] (List.hd @@ Parse.implementation (Lexing.from_string code))
  with
  | Ok _ -> print_string "ok"
  | Error err -> pp_err Format.std_formatter err

let%expect_test _ =
  tof_test {|1 + 1|};
  [%expect {| (NoSuchFunction "+") |}]

let%expect_test _ =
  tof_test {|1|};
  [%expect {| ok |}]

let%expect_test _ =
  tof_test {|let foo x = match x with | 1 -> 1 | y -> y|};
  [%expect {| ok |}]

let%expect_test _ =
  tof_test {|let foo (a, b) = match a, b with | 1, 1 -> 1 | a, b -> a|};
  [%expect {| ok |}]

let%expect_test _ =
  tof_test {|let foo _ = 1|};
  [%expect {| ok |}]
