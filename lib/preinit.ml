(** Copyright 2023, Startsev Matvey *)

(** SPDX-License-Identifier: LGPL-3.0-or-later *)

open Parsetree
open Infer
open Infertypes
open Res

let add_from_sig env { psig_desc = s; _ } =
  match s with
  | Psig_value { pval_name = name; pval_type = { ptyp_desc = t; _ }; _ } ->
      let* t = from_core t in
      return @@ ((name.txt, t) :: env)
  | Psig_type (_, ts) ->
      let m_t = function
        | {
            ptype_name = name;
            ptype_params = _;
            ptype_cstrs = _;
            ptype_kind = Ptype_variant ds;
            ptype_private = _;
            ptype_manifest = None;
            _;
          } ->
            return (name.txt, ds)
        | _ -> not_impl_t_d
      in
      let ts = List.map m_t ts in
      let m_cd = function
        | { pcd_name = name; pcd_args = Pcstr_tuple cs; _ } ->
            return (name.txt, cs)
        | _ -> not_impl_t_d
      in
      List.fold_left
        (fun acc t ->
          let* acc = acc in
          let* name, ds = t in
          let rez_t = new_poly name [] [] in
          List.fold_left
            (fun env cd ->
              let* env = env in
              let* name, cs = m_cd cd in
              let* constr =
                match cs with
                | [] -> return @@ rez_t
                | [ { ptyp_desc = c; _ } ] ->
                    from_core c >>| fun arg -> new_arrow arg rez_t []
                | cs ->
                    let* ts =
                      List.fold_right
                        (fun { ptyp_desc = cs; _ } acc ->
                          let* acc = acc in
                          let* c = from_core cs in
                          return (c :: acc))
                        cs (return [])
                    in
                    return @@ new_arrow (new_tuple ts []) rez_t []
              in
              return @@ ((name, constr) :: env))
            (return acc) ds)
        (return env) ts
  | _ -> not_impl_t_d

let get_env file =
  let file = In_channel.with_open_bin file In_channel.input_all in
  let ss = Parse.interface (Lexing.from_string file) in
  List.fold_left
    (fun acc s ->
      let* acc = acc in
      add_from_sig acc s)
    (return []) ss
