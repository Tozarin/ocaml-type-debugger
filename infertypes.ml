open Location
open Warnings
open Lexing

type typ_var_number = int [@@deriving show { with_path = false }]
type id = string [@@deriving show { with_path = false }]

type ground_type = Int | String | Char | Bool | Float | Unit
[@@deriving show { with_path = false }]

type tr_node =
  | TRVar of typ_var_number * reasons
  | TRGround of ground_type * reasons
  | TRArr of tr_node * tr_node * reasons
  | TRTuple of tr_node list * reasons
  | TRPoly of tr_node list * id * reasons (* 'a 'b 'c ty *)

and reason =
  | InitConst of ground_type
  | InitVar of typ_var_number
  | InitTuple
  | NlFunction
  | RezultOf
  | ArgumentOf of int
  | PatConst of ground_type
  | PatInterval of ground_type
  | PatTuple
  | RecFunction
  | NoReason

and loc_res = reason * loc
and reasons = loc_res list

let tr_var n r = TRVar (n, r)
let tr_ground t r = TRGround (t, r)
let tr_arr t1 t2 r = TRArr (t1, t2, r)
let tr_tuple ts r = TRTuple (ts, r)
let tr_poly ns id r = TRPoly (ns, id, r)
let i_cosnt t = InitConst t
let i_var n = InitVar n
let i_tuple = InitTuple
let nl_fun = NlFunction
let rez_of = RezultOf
let arg_of n = ArgumentOf n
let p_const t = PatConst t
let p_interval t = PatInterval t
let p_tuple = PatTuple
let rec_fun = RecFunction
let no_res = NoReason
let loc_res r loc = (r, loc)
let reasons r loc = [ loc_res r loc ]

let map_reason n f =
  match n with
  | TRVar (n, rs) -> tr_var n (f rs)
  | TRGround (gr, rs) -> tr_ground gr (f rs)
  | TRArr (t1, t2, rs) -> tr_arr t1 t2 (f rs)
  | TRTuple (ts, rs) -> tr_tuple ts (f rs)
  | TRPoly (ns, id, rs) -> tr_poly ns id (f rs)

let concat_reason n rs = map_reason n (fun rs' -> rs' @ rs)
let new_reason n rs = map_reason n (fun _ -> rs)
let unreason n = map_reason n (fun _ -> [])

type error =
  [ `UnifyFail of tr_node * tr_node
  | `NotImplemented
  | `OccursFail
  | `MissingFunction of id
  | `IntervalFail
  | `UnexpectedType of tr_node * tr_node
  | `PlaceHolder of string ]

let pp_loc_res fmt (r, loc) =
  let open Format in
  let fmt_position with_name l =
    let fname = if with_name then l.pos_fname else "" in
    if l.pos_lnum = -1 then sprintf "%s[%d]" fname l.pos_cnum
    else
      sprintf "%s[%d,%d+%d]" fname l.pos_lnum l.pos_bol (l.pos_cnum - l.pos_bol)
  in
  let show_loc loc =
    if not !Clflags.locations then ""
    else
      let ghost = if loc.loc_ghost then " ghost" else "" in
      let p_2nd_name = loc.loc_start.pos_fname <> loc.loc_end.pos_fname in
      sprintf "(%s..%s%s)"
        (fmt_position true loc.loc_start)
        (fmt_position p_2nd_name loc.loc_end)
        ghost
  in
  let s_loc = show_loc loc in
  match r with
  | InitConst c ->
      fprintf fmt "init as %s literal at %s" (show_ground_type c) s_loc
  | InitVar n ->
      fprintf fmt "init as uncertain type %s at %s "
        ("'" ^ Char.escaped (Char.chr (n + 97)))
        s_loc
  | InitTuple -> fprintf fmt "init as tuple at %s" s_loc
  | NlFunction -> fprintf fmt "rezult of nameless function at %s" s_loc
  | RezultOf -> fprintf fmt "rezult of function that at %s" s_loc
  | ArgumentOf n -> fprintf fmt "%d argument of function that at %s" n s_loc
  | PatConst c ->
      fprintf fmt "defined as %s literal in pattern matching at %s"
        (show_ground_type c) s_loc
  | PatInterval c ->
      fprintf fmt "defined as %s literal in interval pattern matching at %s"
        (show_ground_type c) s_loc
  | PatTuple -> fprintf fmt "defined as tuple in pettern mathing at %s" s_loc
  | RecFunction -> fprintf fmt "defined as recursive function at %s" s_loc
  | NoReason -> fprintf fmt "no reason at %s" s_loc

let pp_reasons fmt rs =
  let open Format in
  (pp_print_list
     ~pp_sep:(fun _ _ -> fprintf fmt " => ")
     (fun fmt loc_r -> pp_loc_res fmt loc_r))
    fmt rs

let rec pp_tr_node fmt =
  let open Format in
  function
  | TRVar (n, rs) ->
      fprintf fmt "%s: %a\n"
        ("'" ^ Char.escaped (Char.chr (n + 97)))
        pp_reasons rs
  | TRGround (gr, rs) ->
      fprintf fmt "%s: %a\n" (show_ground_type gr) pp_reasons rs
  | TRArr (n1, n2, rs) ->
      fprintf fmt "trarr where\n\t%a\n\t%a\ncause %a" pp_tr_node n1 pp_tr_node
        n2 pp_reasons rs
  | TRTuple (ts, rs) ->
      fprintf fmt "trtuple where %a\ncause %a\n"
        (pp_print_list
           ~pp_sep:(fun _ _ -> fprintf fmt "\n\t")
           (fun fmt n -> pp_tr_node fmt n))
        ts pp_reasons rs
  | TRPoly (ns, id, rs) ->
      fprintf fmt "trpoly %s where %a\ncause %a\n" id
        (pp_print_list
           ~pp_sep:(fun _ _ -> fprintf fmt "\n\t")
           (fun fmt n -> pp_tr_node fmt n))
        ns pp_reasons rs

let pp_error fmt =
  let open Format in
  function
  | `UnifyFail (l, r) ->
      fprintf fmt "Can't unify these types\n";
      pp_tr_node fmt l;
      pp_tr_node fmt r
  | `NotImplemented -> fprintf fmt "Not implemeted part"
  | `OccursFail -> fprintf fmt "Occurs fail"
  | `MissingFunction id -> fprintf fmt "Can't find function %s" id
  | `IntervalFail ->
      fprintf fmt
        "There are not same type concstans in interval pattern matching"
  | `UnexpectedType (e, g) ->
      fprintf fmt "Expected type\n";
      pp_tr_node fmt e;
      fprintf fmt "but getted\n";
      pp_tr_node fmt g
  | `PlaceHolder e -> fprintf fmt "Place holder %s" e

module R : sig
  type 'a t

  val bind : 'a t -> f:('a -> 'b t) -> 'b t
  val return : 'a -> 'a t
  val fail : error -> 'a t
  val ( >>= ) : 'a t -> ('a -> 'b t) -> 'b t
  val ( >>| ) : 'a t -> ('a -> 'b) -> 'b t
  val ( let* ) : 'a t -> ('a -> 'b t) -> 'b t
  val fresh : int t
  val run : 'a t -> ('a, error) Result.t
end = struct
  type 'a t = int -> int * ('a, error) Result.t

  let ( >>= ) : 'a 'b. 'a t -> ('a -> 'b t) -> 'b t =
   fun monad f state ->
    let last, result = monad state in
    match result with Error e -> (last, Error e) | Ok value -> f value last

  let fail error state = (state, Base.Result.fail error)
  let return value last = (last, Base.Result.return value)
  let bind x ~f = x >>= f

  let ( >>| ) : 'a 'b. 'a t -> ('a -> 'b) -> 'b t =
   fun x f state ->
    match x state with
    | state, Ok x -> (state, Ok (f x))
    | state, Error e -> (state, Error e)

  let ( let* ) x f = bind x ~f
  let fresh : int t = fun last -> (last + 1, Result.Ok last)
  let run monad = snd (monad 0)
end
