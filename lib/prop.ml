(* Atomic Proposition *)


type id = string
[@@deriving show]


module IdMap = Map.Make (struct type t = id let compare = compare end)

type location = int IdMap.t


type memory = int array
[@@deriving show]

type expr =
  | EInt of int
  | EVar of id
  | EAdd of expr * expr
  | ESub of expr * expr
  | EMul of expr * expr
  | EDiv of expr * expr
  | EMod of expr * expr
[@@deriving show]

(* Arithmetic Proposition *)
type arith =
  | AP_Eq of expr * expr
  | AP_Lt of expr * expr
  | AP_Le of expr * expr
  | AP_Gt of expr * expr
  | AP_Ge of expr * expr
[@@deriving show]

(* Proposition *)
type boolean =
  | PTrue
  | PArith of arith
  | PNot   of boolean
  | PAnd   of boolean list
  | POr    of boolean list
[@@deriving show]



let rec eval_expr location memory = function
  | EInt v -> v
  | EVar x -> memory.(IdMap.find x location)
  | EAdd (l, r) -> eval_expr location memory l  +  eval_expr location memory r
  | ESub (l, r) -> eval_expr location memory l  -  eval_expr location memory r
  | EMul (l, r) -> eval_expr location memory l  *  eval_expr location memory r
  | EDiv (l, r) -> eval_expr location memory l  /  eval_expr location memory r
  | EMod (l, r) -> eval_expr location memory l mod eval_expr location memory r

let eval_arith location memory = function
  | AP_Eq (l, r) -> eval_expr location memory l =  eval_expr location memory r
  | AP_Lt (l, r) -> eval_expr location memory l <  eval_expr location memory r
  | AP_Le (l, r) -> eval_expr location memory l <= eval_expr location memory r
  | AP_Gt (l, r) -> eval_expr location memory l >  eval_expr location memory r
  | AP_Ge (l, r) -> eval_expr location memory l >= eval_expr location memory r

let rec eval_boolean location memory = function
  | PTrue -> true
  | PArith a -> eval_arith location memory a
  | PNot b -> not (eval_boolean location memory b)
  | PAnd bs -> List.for_all (eval_boolean location memory) bs
  | POr bs -> List.exists (eval_boolean location memory) bs