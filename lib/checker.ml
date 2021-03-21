(* LTL Model Checker *)

type state_t = Prop.memory * Automaton.state_t
[@@deriving show]

type witness_t =
  | WEmpty of {
      wt_state_num_dfs1 : int;
      wt_state_num_dfs2 : int;
    }
  | WFound of {
      wt_trail_dfs1 : state_t list;
      wt_trail_dfs2 : state_t list;
      wt_state_num_dfs1 : int;
      wt_state_num_dfs2 : int;
    }
[@@deriving show]


let check_emptiness (system : System.transition_system) (spec : Automaton.buchi) =
  let exception Found_counterexample of witness_t in
  let visited_dfs1 = Hashtbl.create 100 in
  let visited_dfs2 = Hashtbl.create 100 in
  let foreach_successor q f =
    let (current_memory, current_spec_state) = q in
    System.foreach_next_memory system.ts_location system.ts_procs current_memory (fun next_memory ->
      spec.buchi_successor.(current_spec_state)
      |> List.iter (fun next_spec_state ->
        let p = spec.buchi_props.(next_spec_state) in
        let v =  Prop.eval_boolean system.ts_location next_memory p in
        let q' = (next_memory, next_spec_state) in
        if v then f q') )
  in
  (* nested dfs *)
  let rec dfs2 stack_dfs1 stack (q : Prop.memory * Automaton.state_t) =
    Hashtbl.add visited_dfs2 q true;
    foreach_successor q (fun q' ->
      if List.mem q' stack_dfs1 then
        raise (Found_counterexample (WFound {
          wt_trail_dfs1 = List.rev stack_dfs1;
          wt_trail_dfs2 = List.rev (q' :: q :: stack);
          wt_state_num_dfs1 = Hashtbl.length visited_dfs1;
          wt_state_num_dfs2 = Hashtbl.length visited_dfs2;
        }))
      else if not (Hashtbl.mem visited_dfs2 q') then dfs2 stack_dfs1 (q :: stack) q')
  in
  (* first dfs *)
  let rec dfs1 stack (q : Prop.memory * Automaton.state_t) =
    Hashtbl.add visited_dfs1 q true;
    foreach_successor q (fun q' ->
      if not (Hashtbl.mem visited_dfs1 q') then dfs1 (q :: stack) q');
    if Automaton.StateSet.mem (snd q) spec.buchi_accept then
      dfs2 (q :: stack) [] q  (* interleave dfs2*)
    in
  try
    (*
    dfs1 [] (system.ts_init, spec.buchi_init); (* これだとシステムの初期状態が検査できてない(一個ずれてる) *)
    *)

    (* specのオートマトンの先頭にはダミーの初期状態がある *)
    (* systemの先頭にはダミー状態はないので，specの本当の開始状態からの遷移をそれぞれ行う必要がある． *)
    spec.buchi_successor.(spec.buchi_init)
    |> List.iter (fun init_spec ->
      let p = spec.buchi_props.(init_spec) in
      if Prop.eval_boolean system.ts_location system.ts_init p then
        dfs1 [] (system.ts_init, init_spec) );

    WEmpty {
      wt_state_num_dfs1 = Hashtbl.length visited_dfs1;
      wt_state_num_dfs2 = Hashtbl.length visited_dfs2;
    }
  with Found_counterexample w -> w



