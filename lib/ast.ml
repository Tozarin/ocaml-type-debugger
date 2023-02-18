type id = string
type constructor_name = string
type const_type = TInt | TFloat | TBool | TChar | TString | TUnit
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

type un_op = Minus | Not
type recursive = Rec | Not

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

(* TODO: custom types (single, adt, gadt mb)*)