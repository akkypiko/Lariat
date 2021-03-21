(* Buchi Automaton *)


type state_pair = Kripke.node_id * int
module PairStateSet = Set.Make (struct type t = state_pair let compare = compare end)
module PairStateMap = Map.Make (struct type t = state_pair let compare = compare end)

(* genaralized (pair state) buchi automaton from fair kripke structure by ltl formula *)
type intermediate_buchi = {
  ib_props : Prop.boolean PairStateMap.t;             (* state -> proposition   *)
  ib_init : state_pair;                            (* initial state          *)
  ib_successor : (state_pair list ref) PairStateMap.t; (* state -> state_id list *)
  ib_accept : PairStateSet.t;                      (* state set              *)
}


type state_t = int
[@@deriving show]
module StateSet = Set.Make (struct type t = state_t let compare = compare end)

type buchi = {
  buchi_props : Prop.boolean array;  (* state_id -> proposition   *)
  buchi_init : state_t;                        (* initial state_id          *)
  buchi_successor : (state_t list) array;    (* state_id -> state_id list *)
  buchi_accept : StateSet.t;                 (* state_id set              *)
}


let show_buchi ba =
  Printf.printf "Buchi Automaton {\n";
  Printf.printf "Init: %d\n" ba.buchi_init;
  Printf.printf "Accept: {";
  StateSet.iter (fun x -> Printf.printf "%d," x) ba.buchi_accept;
  Printf.printf "}\n";
  Array.iteri (fun from nexts -> nexts |> List.iter (fun too -> Printf.printf "(%d, %d)\n" from too)) ba.buchi_successor;
  Array.iteri (fun s p -> Printf.printf "[%d: %s]\n" s (Prop.show_boolean p)) ba.buchi_props;
  Printf.printf "}\n"


(* translate from fair kripke to intermediate buchi automaton *)
let degeneralize (ks : Kripke.fair_structure) =
  let open Kripke in
  let k = List.length ks.fs_fairness in
  let round = List.init k (fun i -> i+1) in
  let ib_init = (0, 1) in
  let ib_accept = List.hd ks.fs_fairness |> List.map (fun n -> n, 1) |> PairStateSet.of_list in
  let ib_props =
    let init_map = List.fold_left (fun m i -> PairStateMap.add (0, i) (Prop.PAnd []) m) PairStateMap.empty round in
    ks.fs_states
    |> List.map (fun n ->
      let props =
        LtlSet.fold (fun t l -> t :: l) n.node_now []
        |> List.filter_map Ltl.extract_prop
      in
      n.node_id, Prop.PAnd props)
    |> List.map (fun (n, p) -> List.map (fun r -> (n, r), p) round)
    |> List.flatten
    |> List.fold_left (fun m (s, p) -> PairStateMap.add s p m) init_map
  in
  let ib_successor =
    (*Printf.printf "DEBUG: round length: %d\n" (List.length round);*)
    let init_map = List.fold_left (fun m i -> PairStateMap.add (0, i) (ref []) m) PairStateMap.empty round in
    ks.fs_states
    |> List.fold_left (fun m n ->
      List.fold_left (fun m i -> PairStateMap.add (n.node_id, i) (ref []) m) m round) init_map
  in
  if k = 1 then
    (* すでに受理集合が1つのときラウンド1のみでペア状態にする *)
    ks.fs_states
    |> List.iter (fun to_node ->
      to_node.node_incoming
      |> IdSet.iter (fun from_node ->
        let succ = PairStateMap.find (from_node, 1) ib_successor in
        succ := (to_node.node_id, 1) :: !succ))
  else (* k >= 2 *)
    (* degeneralize: https://sites.cs.ucsb.edu/~bultan/courses/267/lectures/l8.pdf *)
    ks.fs_states
    |> List.iter (fun to_node ->
      to_node.node_incoming
      |> IdSet.iter (fun from_node ->
        round
        |> List.iter (fun i ->
          let f = List.nth ks.fs_fairness (i - 1) in
          let j = if List.mem to_node.node_id f then (i mod k) + 1 else i in
          (*Printf.printf "DEBUG: from_node: %d, i: %d\n" from_node i;*)
          let succ = PairStateMap.find (from_node, i) ib_successor in
          succ := (to_node.node_id, j) :: !succ )));
  {
    ib_props;
    ib_init;
    ib_successor;
    ib_accept;
  }




let rename (ib : intermediate_buchi) =
  (* state_pair -> int のマッピング作って状態のリネームする *)
  let counter = ref 0 in
  let fresh () =
    let c = !counter in
    incr counter; c
  in
  let mapping = Hashtbl.create 100 in
  let rec dfs s =
    Hashtbl.add mapping s (fresh ());
    (*Printf.printf "DEBUG: (108:s): %d, %d\n" (fst s) (snd s);*)
    let succ = PairStateMap.find s ib.ib_successor in
    List.iter (fun next -> if not (Hashtbl.mem mapping next) then dfs next) !succ
  in
  dfs ib.ib_init;
  let state_num = !counter in
  let buchi_props = Array.make state_num Prop.PTrue in
  ib.ib_props
  |> PairStateMap.iter (fun s p ->
    try
      let i = Hashtbl.find mapping s in
      buchi_props.(i) <- p
    with Not_found -> ());
  let buchi_init = Hashtbl.find mapping ib.ib_init in
  let buchi_successor = Array.make state_num [] in
  ib.ib_successor
  |> PairStateMap.iter (fun s nexts ->
    try
      let i = Hashtbl.find mapping s in
      let nexts = try List.map (Hashtbl.find mapping) !nexts with Not_found -> assert false in
      buchi_successor.(i) <- nexts
    with Not_found -> ());
  let buchi_accept = PairStateSet.fold (fun s a -> try StateSet.add (Hashtbl.find mapping s) a with Not_found -> a) ib.ib_accept StateSet.empty in
  {
    buchi_props;
    buchi_init;
    buchi_successor;
    buchi_accept;
  }

(* translate from fair kripke structure to buchi automaton *)
let from_fair_kripke (ks : Kripke.fair_structure) =
  ks |> degeneralize |> rename


