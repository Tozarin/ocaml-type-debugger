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
        let* acc in
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
    | _ -> assert false
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
    | TPoly (l_name, _, _, _), TPoly (r_name, _, _, _) when l_name != r_name ->
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

let add_arg_reason t loc =
  let rec helper acc = function
    | TArrow (t1, t2, _, _) (* ls, rs ??? *) ->
        let t2, n = helper (acc + 1) t2 in
        let t1 = add_reason t1 (ArgOf (n - 1, loc)) in
        let t2 =
          match t2 with
          | [] -> failwith ""
          | t2 :: tl when n != acc + 1 -> add_reason t2 (ArgOf (n, loc)) :: tl
          | t2 -> t2
        in
        (t1 :: t2, n - 2)
    | t ->
        if acc = 1 then ([ t ], 1)
        else ([ add_reason t (ResultOfWithoutName loc) ], acc)
  in
  fst @@ helper 1 t

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

let rec ppat env p =
  let loc = p.ppat_loc in
  match p.ppat_desc with
  | Ppat_any -> return (newvar () (pat_any loc), env)
  | Ppat_var var ->
      let t = newvar () (pat_any loc) in
      return (t, (var.txt, t) :: env)
  | Ppat_constant c ->
      let c = match_const c in
      return (tgronud c (pat_const c loc), env)
  | Ppat_interval (c1, c2) ->
      let c = match_const c1 in
      if eq_const c1 c2 then return (tgronud c (pat_interval_const c loc), env)
      else interval_pat_fail
  | Ppat_tuple ps ->
      let* ts, env =
        List.fold_right
          (fun p acc ->
            let* acc, env = acc in
            let* t, env = ppat env p in
            return (t :: acc, env))
          ps
          (return ([], env))
      in
      return (new_tuple ts (pat_tuple loc), env)
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
              let* acc in
              let* e = helper env e in
              return (e :: acc))
            es (return [])
        in
        return @@ new_tuple ts (init_tuple loc)
    | Pexp_fun (_, _, arg, body) ->
        let* t_arg, env = ppat env arg in
        let* t_body = helper env body in
        return @@ new_arrow t_arg t_body (nl_fun loc)
    | Pexp_apply (expr, args) ->
        let* t_fun = helper env expr in
        let* _, t_args =
          List.fold_right
            (fun (_, e) acc ->
              let* i, acc = acc in
              let* e = helper env e in
              let arg = add_reason e (ApplyAs (i, clear_reasons t_fun, loc)) in
              return (i + 1, arg :: acc))
            args
            (return (1, []))
        in
        let t_res = newvar () (res_of_apply t_fun t_args loc) in
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
              let* env in
              let* env =
                match p.ppat_desc with
                | Ppat_any -> return env
                | Ppat_var id -> return ((id.txt, rec_t) :: env)
                | _ -> rec_no_impl
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
              let* env in
              let* t_e = helper env e in
              let* arg, env = ppat env p in
              unify t_e arg *> return (leave_lvl ()) *> gen t_e *> return env)
            (return env) v_bs
        in
        helper env expr
    | Pexp_match (expr, cs) ->
        let* e_match = helper env expr in
        List.fold_left
          (fun acc case ->
            let* acc in
            let* p_t, env = ppat env case.pc_lhs in
            unify e_match p_t
            *> let* case_e = helper env case.pc_rhs in
               unify (inst acc) case_e *> return acc
            (* match case.pc_guard with
               | None -> ()
               | Some e -> (match helper env e with _ -> ())); *))
          (return (newvar () (res_of_pm loc)))
          cs
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
          let* env in
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
          let* env in
          let* t_e = tof env e in
          let* arg, env = ppat env p in
          unify t_e arg *> return (leave_lvl ()) *> gen t_e *> return env)
        (return env) v_bs
  | _ -> exp_let