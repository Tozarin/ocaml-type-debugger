type id = string [@@deriving show { with_path = false }]
type constructor_name = string [@@deriving show { with_path = false }]

type const_type = TInt | TFloat | TBool | TChar | TString | TUnit
[@@deriving show { with_path = false }]
(* mb more things or another type for this*)

type bin_op =
  | IAdd
  | ISub
  | IMul
  | IDiv
  | FAdd
  | FSub
  | FMul
  | FDiv
  | Mod
  | Less
  | Gre
  | Leq
  | Geq
  | Eq
  | Neg
  | And
  | Or
  | Concat
[@@deriving show { with_path = false }]

type un_op = Minus | Not [@@deriving show { with_path = false }]
type recursive = Rec | Not [@@deriving show { with_path = false }]

type expr =
  | ELiteral of const_type
  | EBinOp of bin_op * expr * expr
  | EUnOp of un_op * expr
  | EApp of expr * expr
  | EId of id
  | EFun of id list * expr
  | EList of expr list
  | ETup of expr list
  | EDeclaration of recursive * id * id list * expr
  | ELetIn of expr list * expr
  | EIf of expr * expr * expr
  | EMatch of expr * (expr * expr) list
  (* mb type for patterns *)
  | EConstructor of constructor_name * expr option
[@@deriving show { with_path = false }]

(* TODO: custom types (single, adt, gadt mb)*)
(* TODO: update like https://v2.ocaml.org/manual/expr.html*)