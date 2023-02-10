open Lariat

let () =
  let system_file = ref "" in
  let spec_file = ref "" in
  let speclist =
    [
      ( "-system",
        Arg.Set_string system_file,
        "System Description File (.system)" );
      ("-spec", Arg.Set_string spec_file, "Specification (LTL) File (.ltl)");
    ]
  in
  Arg.parse speclist (fun _ -> ()) "";
  let spec =
    let ichan = open_in !spec_file in
    let lexbuf = Lexing.from_channel ichan in
    try Ltl_parser.parse Ltl_lexer.read lexbuf
    with Ltl_parser.Error ->
      let pos = lexbuf.lex_curr_p in
      let msg =
        Printf.sprintf "Syntax error (ltl) in %s : Line %d, Char %d"
          !system_file pos.pos_lnum
          (pos.pos_cnum - pos.pos_bol + 1)
      in
      close_in_noerr ichan;
      Printf.printf "%s\n" msg;
      assert false
  in
  Printf.printf "LTL: %s\n" (Ltl.show_nn_t Prop.pp_arith spec);
  let system =
    let ichan = open_in !system_file in
    let lexbuf = Lexing.from_channel ichan in
    try System_parser.parse System_lexer.read lexbuf
    with System_parser.Error ->
      let pos = lexbuf.lex_curr_p in
      let msg =
        Printf.sprintf "Syntax error (system) in %s : Line %d, Char %d"
          !system_file pos.pos_lnum
          (pos.pos_cnum - pos.pos_bol + 1)
      in
      close_in_noerr ichan;
      Printf.printf "%s\n" msg;
      assert false
  in
  Printf.printf "System: ";
  System.show_transition_system system;
  Printf.printf "\n";
  let kripke = Kripke.from_ltl spec in
  (*kripke.show_fair_structure k; print_endline "\n";*)
  let ba = Automaton.from_fair_kripke kripke in
  Automaton.show_buchi ba;
  Printf.printf
    "=========================== CHECK ==================================\n";
  let w = Checker.check_emptiness system ba in
  Printf.printf "RESULT : %s\n" (Checker.show_witness_t w)

(*


(* ====================== SAMPLE ========================= *)
open Lariat.System
open Lariat.Prop
open Lariat.Ltl

let system_alpha =
  {
    ts_location =
      [ ("a", 0); ("b", 1); ("sw", 2) ]
      |> List.fold_left (fun a (x, l) -> Prop.IdMap.add x l a) Prop.IdMap.empty;
    ts_init = [| 0; 0; 0 |];
    ts_procs =
      [
        ( "a",
          [
            {
              tr_guard = PArith (AP_Eq (EVar "b", EInt 1));
              tr_update = EVar "a";
            };
            {
              tr_guard =
                PAnd
                  [
                    PNot (PArith (AP_Eq (EVar "b", EInt 1)));
                    PArith (AP_Eq (EVar "a", EInt 0));
                  ];
              tr_update = EInt 1;
            };
            {
              tr_guard =
                PAnd
                  [
                    PNot (PArith (AP_Eq (EVar "b", EInt 1)));
                    PArith (AP_Eq (EVar "a", EInt 1));
                  ];
              tr_update = EInt 2;
            };
            {
              tr_guard =
                PAnd
                  [
                    PNot (PArith (AP_Eq (EVar "b", EInt 1)));
                    PArith (AP_Eq (EVar "a", EInt 2));
                  ];
              tr_update = EInt 0;
            };
          ],
          EVar "a" );
        ( "b",
          [
            {
              tr_guard = PArith (AP_Eq (EVar "a", EVar "b"));
              tr_update = EVar "b";
            };
            {
              tr_guard =
                PAnd
                  [
                    PNot (PArith (AP_Eq (EVar "a", EVar "b")));
                    PArith (AP_Eq (EVar "b", EInt 0));
                  ];
              tr_update = EInt 1;
            };
            {
              tr_guard =
                PAnd
                  [
                    PNot (PArith (AP_Eq (EVar "a", EVar "b")));
                    PArith (AP_Eq (EVar "b", EInt 1));
                  ];
              tr_update = EInt 2;
            };
            {
              tr_guard =
                PAnd
                  [
                    PNot (PArith (AP_Eq (EVar "a", EVar "b")));
                    PArith (AP_Eq (EVar "b", EInt 2));
                  ];
              tr_update = EInt 0;
            };
          ],
          EVar "b" );
        ( "sw",
          [
            {
              tr_guard =
                PAnd
                  [
                    PArith (AP_Eq (EVar "a", EInt 2));
                    PArith (AP_Eq (EVar "b", EInt 2));
                  ];
              tr_update = EInt 1;
            };
            {
              tr_guard =
                PAnd
                  [
                    PArith (AP_Eq (EVar "a", EInt 1));
                    PArith (AP_Eq (EVar "b", EInt 1));
                  ];
              tr_update = EInt 0;
            };
          ],
          EVar "sw" );
      ];
  }

(* G((sw = 0) -> F(sw = 1))  *)
let system_alpha_spec_1 =
  globally
    (implies
       (ap (AP_Eq (EVar "sw", EInt 0)))
       (future (ap (AP_Eq (EVar "sw", EInt 1)))))

(* G((sw = 1) -> F(sw = 0))  *)
let system_alpha_spec_2 =
  globally
    (implies
       (ap (AP_Eq (EVar "sw", EInt 1)))
       (future (ap (AP_Eq (EVar "sw", EInt 0)))))

let mini_life_game =
  {
    ts_location =
      [
        ("d1", 0);
        ("d2", 1);
        ("d3", 2);
        ("d4", 3);
        ("d5", 4);
        ("d6", 5);
        ("d7", 6);
        ("d8", 7);
      ]
      |> List.fold_left (fun a (x, l) -> Prop.IdMap.add x l a) Prop.IdMap.empty;
    ts_init = [| 1; 0; 0; 0; 0; 0; 0; 0 |];
    ts_procs =
      [
        (*"dX",
          [
            {tr_guard = PArith (AP_Eq (EAdd (EAdd (EVar "dX-1", EVar "dX"), EVar "dX+1"), EInt 3)); tr_update = EInt 0};
            {tr_guard = PArith (AP_Eq (EAdd (EAdd (EVar "dX-1", EVar "dX"), EVar "dX+1"), EInt 2)); tr_update = EInt 1};
            {tr_guard = PArith (AP_Eq (EAdd (EAdd (EVar "dX-1", EVar "dX"), EVar "dX+1"), EInt 2)); tr_update = EInt 0};
            {tr_guard = PArith (AP_Eq (EAdd (EAdd (EVar "dX-1", EVar "dX"), EVar "dX+1"), EInt 1)); tr_update = EInt 1};
            {tr_guard = PArith (AP_Eq (EAdd (EAdd (EVar "dX-1", EVar "dX"), EVar "dX+1"), EInt 0)); tr_update = EInt 0};
          ],
          EVar "dX";*)
        ( "d1",
          [
            {
              tr_guard =
                PArith
                  (AP_Eq (EAdd (EAdd (EInt 0, EVar "d1"), EVar "d2"), EInt 3));
              tr_update = EInt 0;
            };
            {
              tr_guard =
                PArith
                  (AP_Eq (EAdd (EAdd (EInt 0, EVar "d1"), EVar "d2"), EInt 2));
              tr_update = EInt 1;
            };
            {
              tr_guard =
                PArith
                  (AP_Eq (EAdd (EAdd (EInt 0, EVar "d1"), EVar "d2"), EInt 2));
              tr_update = EInt 0;
            };
            {
              tr_guard =
                PArith
                  (AP_Eq (EAdd (EAdd (EInt 0, EVar "d1"), EVar "d2"), EInt 1));
              tr_update = EInt 1;
            };
            {
              tr_guard =
                PArith
                  (AP_Eq (EAdd (EAdd (EInt 0, EVar "d1"), EVar "d2"), EInt 0));
              tr_update = EInt 0;
            };
          ],
          EVar "d1" );
        ( "d2",
          [
            {
              tr_guard =
                PArith
                  (AP_Eq (EAdd (EAdd (EVar "d1", EVar "d2"), EVar "d3"), EInt 3));
              tr_update = EInt 0;
            };
            {
              tr_guard =
                PArith
                  (AP_Eq (EAdd (EAdd (EVar "d1", EVar "d2"), EVar "d3"), EInt 2));
              tr_update = EInt 1;
            };
            {
              tr_guard =
                PArith
                  (AP_Eq (EAdd (EAdd (EVar "d1", EVar "d2"), EVar "d3"), EInt 2));
              tr_update = EInt 0;
            };
            {
              tr_guard =
                PArith
                  (AP_Eq (EAdd (EAdd (EVar "d1", EVar "d2"), EVar "d3"), EInt 1));
              tr_update = EInt 1;
            };
            {
              tr_guard =
                PArith
                  (AP_Eq (EAdd (EAdd (EVar "d1", EVar "d2"), EVar "d3"), EInt 0));
              tr_update = EInt 0;
            };
          ],
          EVar "d2" );
        ( "d3",
          [
            {
              tr_guard =
                PArith
                  (AP_Eq (EAdd (EAdd (EVar "d2", EVar "d3"), EVar "d4"), EInt 3));
              tr_update = EInt 0;
            };
            {
              tr_guard =
                PArith
                  (AP_Eq (EAdd (EAdd (EVar "d2", EVar "d3"), EVar "d4"), EInt 2));
              tr_update = EInt 1;
            };
            {
              tr_guard =
                PArith
                  (AP_Eq (EAdd (EAdd (EVar "d2", EVar "d3"), EVar "d4"), EInt 2));
              tr_update = EInt 0;
            };
            {
              tr_guard =
                PArith
                  (AP_Eq (EAdd (EAdd (EVar "d2", EVar "d3"), EVar "d4"), EInt 1));
              tr_update = EInt 1;
            };
            {
              tr_guard =
                PArith
                  (AP_Eq (EAdd (EAdd (EVar "d2", EVar "d3"), EVar "d4"), EInt 0));
              tr_update = EInt 0;
            };
          ],
          EVar "d3" );
        ( "d4",
          [
            {
              tr_guard =
                PArith
                  (AP_Eq (EAdd (EAdd (EVar "d3", EVar "d4"), EVar "d5"), EInt 3));
              tr_update = EInt 0;
            };
            {
              tr_guard =
                PArith
                  (AP_Eq (EAdd (EAdd (EVar "d3", EVar "d4"), EVar "d5"), EInt 2));
              tr_update = EInt 1;
            };
            {
              tr_guard =
                PArith
                  (AP_Eq (EAdd (EAdd (EVar "d3", EVar "d4"), EVar "d5"), EInt 2));
              tr_update = EInt 0;
            };
            {
              tr_guard =
                PArith
                  (AP_Eq (EAdd (EAdd (EVar "d3", EVar "d4"), EVar "d5"), EInt 1));
              tr_update = EInt 1;
            };
            {
              tr_guard =
                PArith
                  (AP_Eq (EAdd (EAdd (EVar "d3", EVar "d4"), EVar "d5"), EInt 0));
              tr_update = EInt 0;
            };
          ],
          EVar "d4" );
        ( "d5",
          [
            {
              tr_guard =
                PArith
                  (AP_Eq (EAdd (EAdd (EVar "d4", EVar "d5"), EVar "d6"), EInt 3));
              tr_update = EInt 0;
            };
            {
              tr_guard =
                PArith
                  (AP_Eq (EAdd (EAdd (EVar "d4", EVar "d5"), EVar "d6"), EInt 2));
              tr_update = EInt 1;
            };
            {
              tr_guard =
                PArith
                  (AP_Eq (EAdd (EAdd (EVar "d4", EVar "d5"), EVar "d6"), EInt 2));
              tr_update = EInt 0;
            };
            {
              tr_guard =
                PArith
                  (AP_Eq (EAdd (EAdd (EVar "d4", EVar "d5"), EVar "d6"), EInt 1));
              tr_update = EInt 1;
            };
            {
              tr_guard =
                PArith
                  (AP_Eq (EAdd (EAdd (EVar "d4", EVar "d5"), EVar "d6"), EInt 0));
              tr_update = EInt 0;
            };
          ],
          EVar "d5" );
        ( "d6",
          [
            {
              tr_guard =
                PArith
                  (AP_Eq (EAdd (EAdd (EVar "d5", EVar "d6"), EVar "d7"), EInt 3));
              tr_update = EInt 0;
            };
            {
              tr_guard =
                PArith
                  (AP_Eq (EAdd (EAdd (EVar "d5", EVar "d6"), EVar "d7"), EInt 2));
              tr_update = EInt 1;
            };
            {
              tr_guard =
                PArith
                  (AP_Eq (EAdd (EAdd (EVar "d5", EVar "d6"), EVar "d7"), EInt 2));
              tr_update = EInt 0;
            };
            {
              tr_guard =
                PArith
                  (AP_Eq (EAdd (EAdd (EVar "d5", EVar "d6"), EVar "d7"), EInt 1));
              tr_update = EInt 1;
            };
            {
              tr_guard =
                PArith
                  (AP_Eq (EAdd (EAdd (EVar "d5", EVar "d6"), EVar "d7"), EInt 0));
              tr_update = EInt 0;
            };
          ],
          EVar "d6" );
        ( "d7",
          [
            {
              tr_guard =
                PArith
                  (AP_Eq (EAdd (EAdd (EVar "d6", EVar "d7"), EVar "d8"), EInt 3));
              tr_update = EInt 0;
            };
            {
              tr_guard =
                PArith
                  (AP_Eq (EAdd (EAdd (EVar "d6", EVar "d7"), EVar "d8"), EInt 2));
              tr_update = EInt 1;
            };
            {
              tr_guard =
                PArith
                  (AP_Eq (EAdd (EAdd (EVar "d6", EVar "d7"), EVar "d8"), EInt 2));
              tr_update = EInt 0;
            };
            {
              tr_guard =
                PArith
                  (AP_Eq (EAdd (EAdd (EVar "d6", EVar "d7"), EVar "d8"), EInt 1));
              tr_update = EInt 1;
            };
            {
              tr_guard =
                PArith
                  (AP_Eq (EAdd (EAdd (EVar "d6", EVar "d7"), EVar "d8"), EInt 0));
              tr_update = EInt 0;
            };
          ],
          EVar "d7" );
        ( "d8",
          [
            {
              tr_guard =
                PArith
                  (AP_Eq (EAdd (EAdd (EVar "d7", EVar "d8"), EInt 0), EInt 3));
              tr_update = EInt 0;
            };
            {
              tr_guard =
                PArith
                  (AP_Eq (EAdd (EAdd (EVar "d7", EVar "d8"), EInt 0), EInt 2));
              tr_update = EInt 1;
            };
            {
              tr_guard =
                PArith
                  (AP_Eq (EAdd (EAdd (EVar "d7", EVar "d8"), EInt 0), EInt 2));
              tr_update = EInt 0;
            };
            {
              tr_guard =
                PArith
                  (AP_Eq (EAdd (EAdd (EVar "d7", EVar "d8"), EInt 0), EInt 1));
              tr_update = EInt 1;
            };
            {
              tr_guard =
                PArith
                  (AP_Eq (EAdd (EAdd (EVar "d7", EVar "d8"), EInt 0), EInt 0));
              tr_update = EInt 0;
            };
          ],
          EVar "d8" );
      ];
  }

(* F(d1 + d2 + d3 + d4 + d5 + d6 + d7 + d8 = 8) *)
let mini_life_game_spec1 =
  future
    (ap
       (AP_Eq
          ( EAdd
              ( EAdd
                  ( EAdd
                      ( EAdd
                          ( EAdd
                              ( EAdd (EAdd (EVar "d1", EVar "d2"), EVar "d3"),
                                EVar "d4" ),
                            EVar "d5" ),
                        EVar "d6" ),
                    EVar "d7" ),
                EVar "d8" ),
            EInt 8 )))

let is1 s = ap (AP_Eq (EVar s, EInt 1))
let is0 s = ap (AP_Eq (EVar s, EInt 0))

(* F(d1...d8=1) && G((d1...d8=1) -> F(d1=1,d2...d8=0)) *)
let mini_life_game_spec2 =
  let p =
    future
      (and_
         (and_
            (and_
               (and_
                  (and_
                     (and_ (and_ (is1 "d1") (is1 "d2")) (is1 "d3"))
                     (is1 "d4"))
                  (is1 "d5"))
               (is1 "d6"))
            (is1 "d7"))
         (is1 "d8"))
  in
  let q =
    and_
      (and_
         (and_
            (and_
               (and_ (and_ (and_ (is1 "d1") (is1 "d2")) (is1 "d3")) (is1 "d4"))
               (is1 "d5"))
            (is1 "d6"))
         (is1 "d7"))
      (is1 "d8")
  in
  let r =
    future
      (and_
         (and_
            (and_
               (and_
                  (and_
                     (and_ (and_ (is1 "d1") (is0 "d2")) (is0 "d3"))
                     (is0 "d4"))
                  (is0 "d5"))
               (is0 "d6"))
            (is0 "d7"))
         (is0 "d8"))
  in
  let s = globally (implies q r) in
  and_ p s

(* F(d1 + d2 + d3 + d4 + d5 + d6 + d7 + d8 = 2) *)
let mini_life_game_spec5 =
  future
    (ap
       (AP_Eq
          ( EAdd
              ( EAdd
                  ( EAdd
                      ( EAdd
                          ( EAdd
                              ( EAdd (EAdd (EVar "d1", EVar "d2"), EVar "d3"),
                                EVar "d4" ),
                            EVar "d5" ),
                        EVar "d6" ),
                    EVar "d7" ),
                EVar "d8" ),
            EInt 2 )))

(* F(d1 + d2 + d3 + d4 + d5 + d6 + d7 + d8 = 3) *)
let mini_life_game_spec6 =
  future
    (ap
       (AP_Eq
          ( EAdd
              ( EAdd
                  ( EAdd
                      ( EAdd
                          ( EAdd
                              ( EAdd (EAdd (EVar "d1", EVar "d2"), EVar "d3"),
                                EVar "d4" ),
                            EVar "d5" ),
                        EVar "d6" ),
                    EVar "d7" ),
                EVar "d8" ),
            EInt 3 )))

let kaidan =
  {
    ts_location =
      [ ("posA", 0); ("posB", 1) ]
      |> List.fold_left (fun a (x, l) -> Prop.IdMap.add x l a) Prop.IdMap.empty;
    ts_init = [| 0; 0 |];
    ts_procs =
      [
        ( "posA",
          [
            {
              tr_guard =
                PAnd
                  [
                    PAnd
                      [
                        PArith (AP_Lt (EVar "posA", EInt 10));
                        PArith (AP_Lt (EVar "posB", EInt 10));
                      ];
                    PArith (AP_Eq (ESub (EVar "posA", EVar "posB"), EInt 3));
                  ];
              tr_update = EVar "posB";
            };
            {
              tr_guard =
                PAnd
                  [
                    PAnd
                      [
                        PArith (AP_Lt (EVar "posA", EInt 10));
                        PArith (AP_Lt (EVar "posB", EInt 10));
                      ];
                    PArith (AP_Le (ESub (EVar "posA", EVar "posB"), EInt 2));
                  ];
              tr_update = EAdd (EVar "posA", EInt 1);
            };
            {
              tr_guard =
                PAnd
                  [
                    PAnd
                      [
                        PArith (AP_Lt (EVar "posA", EInt 10));
                        PArith (AP_Lt (EVar "posB", EInt 10));
                      ];
                    PArith (AP_Le (ESub (EVar "posA", EVar "posB"), EInt 2));
                  ];
              tr_update = EAdd (EVar "posA", EInt 2);
            };
          ],
          EVar "posA" );
        ( "posB",
          [
            {
              tr_guard =
                PAnd
                  [
                    PAnd
                      [
                        PArith (AP_Lt (EVar "posA", EInt 10));
                        PArith (AP_Lt (EVar "posB", EInt 10));
                      ];
                    PArith (AP_Eq (ESub (EVar "posB", EVar "posA"), EInt 3));
                  ];
              tr_update = EVar "posA";
            };
            {
              tr_guard =
                PAnd
                  [
                    PAnd
                      [
                        PArith (AP_Lt (EVar "posA", EInt 10));
                        PArith (AP_Lt (EVar "posB", EInt 10));
                      ];
                    PArith (AP_Le (ESub (EVar "posB", EVar "posA"), EInt 2));
                  ];
              tr_update = EAdd (EVar "posB", EInt 1);
            };
            {
              tr_guard =
                PAnd
                  [
                    PAnd
                      [
                        PArith (AP_Lt (EVar "posA", EInt 10));
                        PArith (AP_Lt (EVar "posB", EInt 10));
                      ];
                    PArith (AP_Le (ESub (EVar "posB", EVar "posA"), EInt 2));
                  ];
              tr_update = EAdd (EVar "posB", EInt 2);
            };
          ],
          EVar "posB" );
      ];
  }

let kaidan_spec3 =
  not_
    (future
       (and_
          (ap (AP_Eq (EVar "posA", EInt 5)))
          (future
             (and_
                (not_ (ap (AP_Eq (EVar "posA", EInt 5))))
                (future (ap (AP_Eq (EVar "posA", EInt 5))))))))

let tmp () =
  let system = kaidan in
  let spec = not_ kaidan_spec3 in

  let k = Kripke.from_ltl spec in
  Kripke.show_fair_structure k;
  print_endline "\n";
  let ba = Automaton.from_fair_kripke k in
  Automaton.show_buchi ba;
  Printf.printf
    "=========================== CHECK ==================================\n";
  let w = Checker.check_emptiness system ba in
  Printf.printf "RESULT : %s\n" (Checker.show_witness_t w)


  *)