
type transition = {
  tr_guard : Prop.boolean; (* ガード *)
  tr_update : Prop.expr; (* 更新式 *)
}
[@@deriving show]

(* 変数idについてのプロセス(動作) target_var, transitions, else_update *)
type process = Prop.id * transition list * Prop.expr 
[@@deriving show]

(* transition system *)
type transition_system = {
  ts_location : Prop.location; (* 変数名と番号(メモリ位置) *)
  ts_init : Prop.memory; (* 初期メモリ *)
  ts_procs : process list; (* プロセス(変数とその更新動作)たち *)
}

let show_transition_system s =
  Printf.printf "{ts_location: {";
  Prop.IdMap.iter (fun k v -> Printf.printf "%s -> %d, " k v) s.ts_location;
  Printf.printf "} , ts_init: %s, ts_procs: [" (Prop.show_memory s.ts_init);
  List.iter (fun p -> Printf.printf "%s, " (show_process p)) s.ts_procs;
  Printf.printf "]}\n"



let foreach_next_memory location procs current_memory f =
  let rec aux choosen = function
    | [] ->
      let next = Array.copy current_memory in
      List.iter (fun (i, v) -> next.(i) <- v) choosen;
      f next
    | (var_loc, new_values) :: ps ->
      List.iter (fun v -> aux ((var_loc, v) :: choosen) ps) new_values
  in
  procs
  (* calc for each process *)
  |> List.map (fun (target_var, transitions, else_update) ->
    let new_values =
      transitions
      |> List.filter (fun t -> Prop.eval_boolean location current_memory t.tr_guard)
      |> List.map (fun t -> Prop.eval_expr location current_memory t.tr_update)
    in
    let var_loc = Prop.IdMap.find target_var location in
    match new_values with (* else節の選択*)
    | [] -> var_loc, [Prop.eval_expr location current_memory else_update]
    | _ -> var_loc, new_values )
  (* composition *)
  |> aux []

