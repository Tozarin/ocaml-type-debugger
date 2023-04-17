open Infertypes
open R

let to_list n loc =
  let rec helper acc = function
    | TRArr (l, r, _) ->
        let acc = helper acc r in
        helper acc l
    | n -> n :: acc
  in
  let list = helper [] n in
  let open List in
  let args = rev (tl @@ rev list) in
  let args =
    fst
    @@ fold_right
         (fun n (acc, num) ->
           let n = concat_reason n (reasons (arg_of num) loc) in
           (n :: acc, num + 1))
         args ([], 1)
  in
  let rez = concat_reason (hd @@ rev list) (reasons rez_of loc) in
  (rez, args)

let rec occurs_in v = function
  | TRVar (n, _) -> n = v
  | TRArr (n1, n2, _) -> occurs_in v n1 || occurs_in v n2
  | TRGround _ -> false
  | TRTuple (ns, _) | TRPoly (ns, _, _) ->
      List.fold_left (fun acc n -> acc || occurs_in v n) false ns

module Subst : sig
  type t

  val empty : t
  val singleton : typ_var_number -> tr_node -> t R.t
  val find : t -> typ_var_number -> tr_node option
  val find_exn : t -> typ_var_number -> tr_node
  val remove : t -> typ_var_number -> t
  val apply : t -> tr_node -> tr_node
  val unify : t -> tr_node -> tr_node -> t R.t
  val extend : t -> typ_var_number -> tr_node -> t R.t
  val compose : t -> t -> t R.t
  val compose_all : t list -> t R.t
  val pp : Format.formatter -> t -> unit
end = struct
  type t = (typ_var_number, tr_node, Base.Int.comparator_witness) Base.Map.t

  let empty = Base.Map.empty (module Base.Int)

  let occurs_check k v =
    if occurs_in k v then fail `OccursFail else return (k, v)

  let singleton k v =
    let* k, v = occurs_check k v in
    return @@ Base.Map.update empty k ~f:(fun _ -> v)

  let find = Base.Map.find
  let find_exn = Base.Map.find_exn
  let remove = Base.Map.remove

  let rec apply sb = function
    | TRVar (n, rs) -> (
        match find sb n with
        | None -> tr_var n rs
        | Some n -> concat_reason n rs)
    | TRArr (n1, n2, rs) -> tr_arr (apply sb n1) (apply sb n2) rs
    | TRPoly (ns, id, rs) ->
        let ns = List.map (apply sb) ns in
        tr_poly ns id rs
    | TRTuple (ns, rs) ->
        let ns = List.map (apply sb) ns in
        tr_tuple ns rs
    | gr -> gr

  let rec unify sb l r =
    match (apply sb l, apply sb r) with
    | TRGround (l, _), TRGround (r, _) when l = r -> return sb
    | TRVar (l, rs), TRVar (r, rs') ->
        if l = r then return sb else extend sb l (tr_var r (rs' @ rs))
    | TRVar (n, rs), t | t, TRVar (n, rs) -> extend sb n (concat_reason t rs)
    | TRArr (l, r, _), TRArr (l', r', _) ->
        let* sb = unify sb l l' in
        unify sb r r'
    | TRPoly (ns, id, _), TRPoly (ns', id', _) when id = id' ->
        List.fold_left2
          (fun sb n n' ->
            let* sb in
            unify sb n n')
          (return sb) ns ns'
    | TRTuple (ns, _), TRTuple (ns', _) ->
        List.fold_left2
          (fun sb n n' ->
            let* sb in
            unify sb n n')
          (return sb) ns ns'
    | _ -> fail @@ `UnifyFail (l, r)

  and extend sb k v =
    match find sb k with
    | Some n -> unify sb n v
    | None ->
        let v = apply sb v in
        let* sb' = singleton k v in
        Base.Map.fold_right sb ~init:(return sb') ~f:(fun ~key:k ~data:v acc ->
            let* acc in
            let v = apply sb' v in
            let* k, v = occurs_check k v in
            return @@ Base.Map.update acc k ~f:(fun _ -> v))

  let compose sb1 sb2 =
    Base.Map.fold_right sb1 ~init:(return sb2) ~f:(fun ~key:k ~data:v acc ->
        let* acc in
        extend acc k v)

  let compose_all ss =
    List.fold_left
      (fun acc sb ->
        let* acc in
        compose acc sb)
      (return empty) ss

  let pp ppf sb =
    Format.fprintf ppf "@[[@[";
    Base.Map.iteri sb ~f:(fun ~key:k ~data:n ->
        Format.fprintf ppf "@[\"%n\" %a@],@\n" k pp_tr_node n);
    Format.fprintf ppf "@]]@]"
end

type expr = tr_node * Subst.t

module TypeEnv : sig
  type t

  val empty : t
  val singleton : id -> tr_node -> Subst.t -> t
  val find : t -> id -> expr option
  val find_exn : t -> id -> expr
  val find_r : t -> id -> expr R.t
  val remove : t -> id -> t
  val extend : t -> id -> expr -> t
  val pp : Format.formatter -> t -> unit
end = struct
  type t = (id, expr, Base.String.comparator_witness) Base.Map.t

  let empty = Base.Map.empty (module Base.String)
  let singleton id n sb = Base.Map.update empty id ~f:(fun _ -> (n, sb))
  let find = Base.Map.find
  let find_exn = Base.Map.find_exn
  let remove = Base.Map.remove

  let find_r env id =
    match find env id with
    | None -> fail @@ `MissingFunction id
    | Some x -> return x

  let extend env id expr = Base.Map.update env id ~f:(fun _ -> expr)

  let pp ppf env =
    Format.fprintf ppf "@[[@[";
    Base.Map.iteri env ~f:(fun ~key:id ~data:(n, sb) ->
        Format.fprintf ppf "@[\"%s\" type: %a\n\twith sb %a@],@\n" id pp_tr_node
          n Subst.pp sb);
    Format.fprintf ppf "@]]@]"
end

open Parsetree
open Longident

let const_match c f loc =
  match c with
  | Pconst_integer _ -> return (tr_ground Int (reasons (f Int) loc))
  | Pconst_char _ -> return (tr_ground Char (reasons (f Char) loc))
  | Pconst_string _ -> return (tr_ground String (reasons (f String) loc))
  | Pconst_float _ -> return (tr_ground Float (reasons (f Float) loc))

let count_of_args e =
  let rec helper n = function
    | Pexp_fun (_, _, _, body) -> helper (n + 1) body.pexp_desc
    | _ -> n
  in
  helper 0 e

let infer =
  let rec helper : TypeEnv.t -> expression -> expr R.t =
    let empty = Subst.empty in
    let apply = Subst.apply in
    let unify = Subst.unify in
    let compose = Subst.compose in
    let compose_all = Subst.compose_all in
    let extend = TypeEnv.extend in
    let fresh_var loc =
      fresh >>= fun n -> return @@ tr_var n (reasons (i_var n) loc)
    in
    let fun_with_args n loc =
      let rec helper = function
        | n' when n' <= 0 -> fail @@ `PlaceHolder "fun_with_args n was <= 0"
        | n' when n' > n ->
            fresh_var loc >>| fun t -> new_reason t (reasons rez_of loc)
        | n' ->
            let* l =
              fresh_var loc >>| fun t -> new_reason t (reasons (arg_of n') loc)
            in
            let* r = helper (n + 1) in
            return @@ tr_arr l r (reasons no_res loc)
      in
      helper 1
    in
    let rec ppat env p =
      let loc = p.ppat_loc in
      match p.ppat_desc with
      | Ppat_any -> fresh_var loc >>= fun v -> return (v, env)
      | Ppat_var var ->
          let* typ_var = fresh_var var.loc in
          let env' = extend env var.txt (unreason typ_var, empty) in
          return (typ_var, env')
      | Ppat_constant const ->
          let* const = const_match const p_const loc in
          return (const, env)
      | Ppat_interval (c, c') ->
          let eq = function
            | Pconst_integer _, Pconst_integer _
            | Pconst_string _, Pconst_string _
            | Pconst_char _, Pconst_char _
            | Pconst_float _, Pconst_float _ ->
                true
            | _ -> false
          in
          if eq (c, c') then
            let* const = const_match c p_interval loc in
            return (const, env)
          else fail `IntervalFail
      | Ppat_tuple ps ->
          let* ps, env =
            List.fold_right
              (fun p acc ->
                let* acc, env = acc in
                let* p, env = ppat env p in
                return (p :: acc, env))
              ps
              (return ([], env))
          in

          let rez_t = tr_tuple ps (reasons p_tuple loc) in
          return (rez_t, env)
      | _ -> fail `NotImplemented
    in
    fun env expr ->
      let loc = expr.pexp_loc in
      let expr = expr.pexp_desc in
      match expr with
      | Pexp_constant const ->
          let* const = const_match const i_cosnt loc in
          return (const, empty)
      | Pexp_ident id ->
          let id = String.concat "." (Longident.flatten id.txt) in
          let* t, sb =
            match TypeEnv.find env id with
            | Some (t, sb) ->
                let t = concat_reason t (reasons rez_of loc) in
                return (t, sb)
            | None ->
                let* t = fresh_var loc in
                return (t, empty)
          in
          return (t, sb)
      | Pexp_fun (_, _, argument, body) ->
          let* t, env' = ppat env argument in
          let* body_t, sb = helper env' body in
          let t = apply sb t in
          let rez_t = tr_arr t body_t (reasons nl_fun loc) in
          return (rez_t, sb)
      (* | Pexp_let (_, v_bs, expr) ->
          (* todo rec *)
          let* env', sb =
            List.fold_left
              (fun acc v_b ->
                let* env, sb = acc in
                let p = v_b.pvb_pat in
                let ex = v_b.pvb_expr in
                let* e, sb' = helper env ex in
                let* sb = compose sb sb' in
                let rec helper' env sb p e =
                  match p.ppat_desc with
                  | Ppat_var var -> return (extend env var.txt (e, sb), sb)
                  (* | Ppat_var var ->
                      let* t =
                        match count_of_args ex.pexp_desc with
                        | 0 ->
                            fresh_var var.loc >>| fun t ->
                            new_reason t (reasons rec_fun var.loc)
                        | n -> fun_with_args n var.loc
                      in
                      let env = TypeEnv.extend env var.txt (t, sb) in
                      let* e, sb' = helper env ex in
                      let* sb = compose sb sb' in
                      return (extend env var.txt (e, sb), sb) *)
                  | Ppat_tuple ps -> (
                      match e with
                      | TRTuple (ns, _) -> (
                          match Base.List.zip ps (List.rev ns) with
                          | Base.List.Or_unequal_lengths.Unequal_lengths ->
                              fail @@ `PlaceHolder "lengs of lists"
                          | Base.List.Or_unequal_lengths.Ok zipped ->
                              List.fold_left
                                (fun acc (p, n) ->
                                  let* env, sb = acc in
                                  helper' env sb p n)
                                (return (env, sb))
                                zipped)
                      | _ -> fail @@ `UnexpectedType (tr_tuple [] [], e))
                  | _ -> fail `NotImplemented
                in
                helper' env sb p e)
              (return (env, empty))
              v_bs
          in
          let* t, sb' = helper env' expr in
          let* sb = compose sb sb' in
          return (t, sb) *)
      | Pexp_let (rec_f, v_bs, expr) ->
          let* env', sb =
            List.fold_left
              (fun acc v ->
                let* env, sb = acc in
                let p = v.pvb_pat in
                let e = v.pvb_expr in
                match p.ppat_desc with
                | Ppat_var var ->
                    let* env =
                      match rec_f with
                      | Nonrecursive -> return env
                      | Recursive ->
                          let* t =
                            match count_of_args e.pexp_desc with
                            | 0 ->
                                fresh_var var.loc >>| fun t ->
                                new_reason t (reasons rec_fun var.loc)
                            | n -> fun_with_args n var.loc
                          in
                          return @@ extend env var.txt (t, empty)
                    in
                    let* e, sb' = helper env e in
                    let* sb = compose sb sb' in
                    return (extend env var.txt (e, sb), sb)
                | _ -> fail `NotImplemented)
              (return (env, empty))
              v_bs
          in
          let* expr, sb' = helper env' expr in
          let* sb = compose sb sb' in
          let expr = apply sb expr in
          return (expr, sb)
      | Pexp_apply (expr, args) ->
          let* f, f_sb = helper env expr in
          let* args =
            List.fold_right
              (fun (_, n) acc ->
                let* acc in
                let* p = helper env n in
                return @@ (p :: acc))
              args (return [])
          in
          let rez, f = to_list f expr.pexp_loc in
          let* ss =
            List.fold_right2
              (fun (t, sb) n acc ->
                let* acc in
                let* sb = unify sb t n in
                return @@ (sb :: acc))
              args f (return [])
          in
          let* sb = compose_all (f_sb :: ss) in
          return (apply sb rez, sb)
      | Pexp_tuple es ->
          let* l, sb =
            List.fold_right
              (fun e acc ->
                let* acc, sb = acc in
                let* hd, hd_sb = helper env e in
                let* sb = compose sb hd_sb in
                return (hd :: acc, sb))
              es
              (return ([], empty))
          in
          let rez_t = tr_tuple l (reasons i_tuple loc) in
          return (rez_t, sb)
      | Pexp_match (expr, case) | Pexp_try (expr, case) ->
          let* e, e_sb = helper env expr in
          List.fold_left
            (fun acc case ->
              let* t, sb = acc in
              let* p_t, env' = ppat env case.pc_lhs in
              let* sb = unify sb t p_t in
              let* g_sb =
                match case.pc_guard with
                | None -> return empty
                | Some e -> helper env' e >>| fun (_, sb) -> sb
              in
              let* c_t, c_sb = helper env' case.pc_rhs in
              let* sb = compose_all [ sb; c_sb; g_sb ] in
              let* sb = unify sb t c_t in
              let t = apply sb c_t in
              return (t, sb))
            (return (e, e_sb))
            case
      | _ -> fail `NotImplemented
  in
  helper

let empty = Base.Map.empty (module Base.Int)

let () =
  let file = Sys.argv.(1) in
  try
    let code = In_channel.with_open_bin file In_channel.input_all in
    let fmt = Format.std_formatter in
    let plus =
      tr_arr (tr_ground Int [])
        (tr_arr (tr_ground Int []) (tr_ground Int []) [])
        []
    in
    let list = tr_arr (tr_var 0 []) (tr_poly [ tr_var 0 [] ] "list" []) [] in
    let test = tr_arr (tr_ground Int []) (tr_ground String []) [] in
    let con =
      tr_arr
        (tr_poly [ tr_var 0 [] ] "list" [])
        (tr_arr
           (tr_poly [ tr_var 0 [] ] "list" [])
           (tr_poly [ tr_var 0 [] ] "list" [])
           [])
        []
    in
    (* let vplus =
         tr_arr
           (tr_tuple [ tr_ground Int []; tr_ground Int [] ] [])
           (tr_arr
              (tr_tuple [ tr_ground Int []; tr_ground Int [] ] [])
              (tr_tuple [ tr_ground Int []; tr_ground Int [] ] [])
              [])
           []
       in *)
    let env = TypeEnv.singleton "l" list Subst.empty in
    let env = TypeEnv.extend env "+" (plus, Subst.empty) in
    let env = TypeEnv.extend env "ts" (test, Subst.empty) in
    let env = TypeEnv.extend env "cn" (con, Subst.empty) in
    let run_infer expr = run @@ infer env expr in
    let print_rez expr =
      match run_infer expr with
      | Ok (t, sb) -> TypeEnv.pp fmt (TypeEnv.singleton "fst" t sb)
      | Error err -> pp_error fmt err
    in
    let code = Parse.implementation (Lexing.from_string code) in
    let ncode = match List.hd code with { pstr_desc = desc; _ } -> desc in
    let ncode =
      match ncode with Pstr_eval (exp, _) -> exp | _ -> failwith ""
    in
    Printast.implementation fmt code;
    Format.printf "\n\n\n";
    print_rez ncode
  with e -> raise e
