
(* Negation Normalized LTL term *)
type 'p nn_t =
  | NN_False
  | NN_True
  | NN_Ap  of 'p
  | NN_NAp of 'p
  | NN_And of 'p nn_t * 'p nn_t
  | NN_Or  of 'p nn_t * 'p nn_t
  | NN_X   of 'p nn_t
  | NN_U   of 'p nn_t * 'p nn_t
  | NN_R   of 'p nn_t * 'p nn_t
[@@deriving show]

let true_ = NN_True

let false_ = NN_False

let ap p = NN_Ap p

let and_ f g = NN_And (f, g)

let or_ f g = NN_Or (f, g)

let rec not_ = function
  | NN_True -> NN_False
  | NN_False -> NN_True
  | NN_Ap p -> NN_NAp p
  | NN_NAp p -> NN_Ap p
  | NN_And (f, g) -> NN_Or (not_ f, not_ g)
  | NN_Or (f, g) -> NN_And (not_ f, not_ g)
  | NN_X f -> NN_X (not_ f)
  | NN_U (f, g) -> NN_R (not_ f, not_ g)
  | NN_R (f, g) -> NN_U (not_ f, not_ g)

let implies f g = NN_Or (not_ f, g)

let next f = NN_X f

let until f g = NN_U (f, g)

let release f g = NN_R (f, g)

(* G f = false R f *)
let globally f = release NN_False f

(* F f = true U f *)
let future f = until NN_True f



let extract_prop = function
  | NN_False -> assert false
  | NN_True -> None
  | NN_Ap p -> Some (Prop.PArith p)
  | NN_NAp p -> Some (Prop.PNot (Prop.PArith p))
  | _ -> None
