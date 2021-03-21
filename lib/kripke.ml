(* fair kripke structure (node) *)

type node_id = int
type ltl_t = Prop.arith Ltl.nn_t
module IdSet = Set.Make (struct type t = node_id let compare = compare end)
module IdMap = Map.Make (struct type t = node_id let compare = compare end)
module LtlSet = Set.Make (struct type t = ltl_t let compare = compare end)

(* kripke state *)
type node = {
  node_id : node_id; (* 0 is as an initial state *)
  mutable node_incoming : IdSet.t;
  mutable node_new : LtlSet.t;
  mutable node_now : LtlSet.t;
  mutable node_next : LtlSet.t;
}

type fair_structure = {
  fs_states : node list;
  fs_fairness : (node_id list) list;
}


let show_node n =
  Printf.printf "(%d, " n.node_id;
  Printf.printf "{"; IdSet.iter (fun x -> Printf.printf "%d," x) n.node_incoming; Printf.printf "}, ";
  Printf.printf "{"; LtlSet.iter (fun x -> Printf.printf "%s," (Ltl.show_nn_t Prop.pp_arith x)) n.node_now; Printf.printf "})\n"

let show_fair_structure s =
  Printf.printf "[States: {\n";
  List.iter (fun n -> show_node n) s.fs_states;
  Printf.printf "}, \nFairness: {";
  List.iter (fun f -> Printf.printf "{"; List.iter (fun x -> Printf.printf "%d," x) f; Printf.printf "}") s.fs_fairness;
  Printf.printf "}]"


(* translate from ltl to fair kripke structure *)
let from_ltl (phi : ltl_t) =
  let state_counter = ref 0 in
  let fresh_id () =
    let s = !state_counter in
    incr state_counter; s
  in
  let rec loop closed = function
    | [] -> closed
    | q :: opens ->
      if LtlSet.is_empty q.node_new then
        update_closed closed opens q
      else
        let psi = LtlSet.choose q.node_new in
        q.node_new <- LtlSet.remove psi q.node_new;
        q.node_now <- LtlSet.add psi q.node_now;
        update_opens closed opens q psi
  and update_closed closed opens q =
    try
      let q' = List.find (fun q' -> LtlSet.equal q.node_now q'.node_now && LtlSet.equal q.node_next q'.node_next) closed in
      q'.node_incoming <- IdSet.union q'.node_incoming q.node_incoming;
      loop closed opens
    with Not_found ->
      let q' = {
        node_id = fresh_id ();
        node_incoming = IdSet.singleton q.node_id;
        node_new = q.node_next;
        node_now = LtlSet.empty;
        node_next = LtlSet.empty;
      } in
      loop (q :: closed) (q' :: opens)
  and update_opens closed opens q psi =
    match psi with
    | Ltl.NN_False -> loop closed opens (* discard *)
    | Ltl.NN_True | Ltl.NN_Ap _ | Ltl.NN_NAp _ -> loop closed (q :: opens) (* skip *)
    | Ltl.NN_And (f, g) ->
      q.node_new <- LtlSet.add f q.node_new;
      q.node_new <- LtlSet.add g q.node_new;
      loop closed (q :: opens)
    | Ltl.NN_Or (f, g) ->
      let r = {q with node_id = fresh_id ()} in
      q.node_new <- LtlSet.add f q.node_new;
      r.node_new <- LtlSet.add g r.node_new;
      loop closed (q :: r :: opens)
    | Ltl.NN_X f ->
      q.node_next <- LtlSet.add f q.node_next;
      loop closed (q :: opens)
    | Ltl.NN_U (f, g) ->
      let r = {q with node_id = fresh_id ()} in
      q.node_new <- LtlSet.add g q.node_new;
      r.node_new <- LtlSet.add f r.node_new;
      r.node_new <- LtlSet.add (Ltl.NN_X psi) r.node_new;
      loop closed (q :: r :: opens)
    | Ltl.NN_R (f, g) ->
      let r = {q with node_id = fresh_id ()} in
      q.node_new <- LtlSet.add f q.node_new;
      q.node_new <- LtlSet.add g q.node_new;
      r.node_new <- LtlSet.add g r.node_new;
      r.node_new <- LtlSet.add (Ltl.NN_X psi) r.node_new;
      loop closed (q :: r :: opens)
  in
  let rec all_until_term = function
    | Ltl.NN_False | Ltl.NN_True | Ltl.NN_Ap _ | Ltl.NN_NAp _ -> LtlSet.empty
    | Ltl.NN_And (f, g) -> LtlSet.union (all_until_term f) (all_until_term g)
    | Ltl.NN_Or (f, g) -> LtlSet.union (all_until_term f) (all_until_term g)
    | Ltl.NN_X f -> all_until_term f
    | Ltl.NN_U (f, g) as psi -> LtlSet.add psi (LtlSet.union (all_until_term f) (all_until_term g))
    | Ltl.NN_R (f, g) -> LtlSet.union (all_until_term f) (all_until_term g)
  in
  let init_id = fresh_id () in (* Initial ID must be 0 *)
  let start_node = {
    node_id = fresh_id ();
    node_incoming = IdSet.singleton init_id;
    node_new  = LtlSet.singleton phi;
    node_now  = LtlSet.empty;
    node_next = LtlSet.empty;
  } in
  let fs_states = loop [] [start_node] in
  let fairness =
    LtlSet.fold (fun u l -> u :: l) (all_until_term phi) []
    |> List.map (fun u ->
      let g = match u with Ltl.NN_U (_, g) -> g | _ -> assert false in
      fs_states
      |> List.filter (fun q -> LtlSet.mem g q.node_now || not (LtlSet.mem u q.node_now))
      |> List.map (fun q -> q.node_id))
  in
  {
    fs_states;
    fs_fairness =
      match fairness with
      | [] -> [List.map (fun n -> n.node_id) fs_states]
      | _ -> fairness
      ;
  }

