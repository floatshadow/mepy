(** Test suite - translated from test.sml *)

open Inference
open Term

(* Helper constructors *)
let var x = Var x
let con0 s = Con (s, [])
let con1 s t = Con (s, [ t ])
let con2 s t1 t2 = Con (s, [ t1; t2 ])

module SaturateTest = struct
  let x = var "x"
  let y = var "y"
  let z = var "z"
  let a = con0 "a"
  let b = con0 "b"
  let c = con0 "c"
  let d = con0 "d"
  let edge x y = con2 "edge" x y
  let node x = con1 "node" x
  let path x y = con2 "path" x y
  let sym = Rule ([ edge x y ], [ edge y x ])
  let refl = Rule ([ node x ], [ path x x ])
  let step = Rule ([ path x y; edge y z ], [ path x z ])

  let test () =
    let bad_refl = Rule ([], [ path x x ]) in
    assert (not (range_restricted bad_refl));
    let db0 =
      State.sort_set
        [ node a; node b; node c; node d; edge a b; edge b c; edge a c; edge b d ]
    in
    print_string ("% db0\n" ^ State.pp_state db0);
    let db1 = Saturate.saturate [ sym ] db0 in
    print_string ("% db1\n" ^ State.pp_state db1);
    let db1_expected =
      [ edge a b
      ; edge a c
      ; edge b a
      ; edge b c
      ; edge b d
      ; edge c a
      ; edge c b
      ; edge d b
      ; node a
      ; node b
      ; node c
      ; node d
      ]
    in
    assert (db1 = db1_expected);
    let db2 = Saturate.saturate [ sym; refl; step ] db0 in
    let db2_expected =
      [ edge a b
      ; edge a c
      ; edge b a
      ; edge b c
      ; edge b d
      ; edge c a
      ; edge c b
      ; edge d b
      ; node a
      ; node b
      ; node c
      ; node d
      ; path a a
      ; path a b
      ; path a c
      ; path a d
      ; path b a
      ; path b b
      ; path b c
      ; path b d
      ; path c a
      ; path c b
      ; path c c
      ; path c d
      ; path d a
      ; path d b
      ; path d c
      ; path d d
      ]
    in
    print_string ("% db2\n" ^ State.pp_state db2);
    assert (db2 = db2_expected);
    print_endline "Saturate tests passed!"
  ;;
end

module LinearTest = struct
  let quarter = con0 "quarter"
  let dime = con0 "dime"
  let nickel = con0 "nickel"
  let q = Rule ([ quarter ], [ dime; nickel; nickel ])
  let d = Rule ([ dime ], [ nickel; nickel ])

  let test_coin_exchange () =
    let _ex0 = Linear.apply_rule q [ quarter ] in
    let ex1 = Federation.sort [ State.sort_multiset [ quarter; dime ] ] in
    print_string ("# ex1\n" ^ Federation.pp_states ex1 ^ "\n");
    let ex2 = Linear.apply_rule d (State.sort_multiset [ quarter; dime ]) in
    print_string ("# ex2\n" ^ Federation.pp_states ex2 ^ "\n");
    let ex3 = Federation.sort (List.concat_map (Linear.apply_rule d) ex2) in
    print_string ("# ex3\n" ^ Federation.pp_states ex3 ^ "\n");
    let ex4 = Linear.iterate [ q; d ] ex1 in
    print_string ("# ex4\n" ^ Federation.pp_states ex4 ^ "\n");
    let ex4_expected =
      [ [ dime; dime; nickel; nickel ]
      ; [ dime; nickel; nickel; nickel; nickel ]
      ; [ dime; quarter ]
      ; [ nickel; nickel; nickel; nickel; nickel; nickel ]
      ; [ nickel; nickel; quarter ]
      ]
    in
    assert (ex4 = ex4_expected);
    print_endline "Coin exchange tests passed!"
  ;;

  let on x y = con2 "on" x y
  let clear x = con1 "clear" x
  let empty = con0 "empty"
  let holds x = con1 "holds" x
  let table = con0 "table"
  let a = con0 "a"
  let b = con0 "b"
  let _c = con0 "c"
  let x_ = var "X"
  let y_ = var "Y"
  let pickup = Rule ([ empty; clear x_; on x_ y_ ], [ holds x_; clear y_ ])
  let putdown = Rule ([ holds x_; clear y_ ], [ empty; clear x_; on x_ y_ ])

  let test_blocksworld () =
    let s0 = [ [ empty; on b table; on a b; clear a; clear table ] ] in
    print_string ("# s0\n" ^ Federation.pp_states s0 ^ "\n");
    let s1 = Linear.iterate [ pickup; putdown ] s0 in
    print_string ("# s1\n" ^ Federation.pp_states s1 ^ "\n");
    let s1_expected =
      [ [ clear a; clear b; empty; on a table; on b table ]
      ; [ clear a; clear table; empty; on a b; on b table ]
      ; [ clear a; clear table; holds b; on a table ]
      ; [ clear b; clear table; empty; on a table; on b a ]
      ; [ clear b; clear table; holds a; on b table ]
      ]
    in
    assert (s1 = s1_expected);
    print_endline "Blocks world tests passed!"
  ;;

  let test () =
    test_coin_exchange ();
    test_blocksworld ();
    print_endline "All Linear tests passed!"
  ;;
end

module OrderedTest = struct
  let b0 = con0 "b0"
  let b1 = con0 "b1"
  let e = con0 "e"
  let inc = con0 "inc"
  let inc_b0 = Rule ([ b0; inc ], [ b1 ])
  let inc_b1 = Rule ([ b1; inc ], [ inc; b0 ])
  let inc_e = Rule ([ e; inc ], [ e; b1 ])

  let test_increment () =
    let s5 = [ e; b1; b0; b1 ] in
    let ex5 = Ordered.iterate [ inc_b0; inc_b1; inc_e ] [ s5 ] in
    print_string ("# ex5\n" ^ Federation.pp_states ex5 ^ "\n");
    let ex6 = Ordered.iterate [ inc_b0; inc_b1; inc_e ] [ s5 @ [ inc ] ] in
    print_string ("# ex6\n" ^ Federation.pp_states ex6 ^ "\n");
    let ex6_expected =
      [ [ e; b1; b0; b1; inc ]; [ e; b1; b0; inc; b0 ]; [ e; b1; b1; b0 ] ]
    in
    assert (ex6 = ex6_expected);
    print_endline "Increment test passed!"
  ;;

  let l = con0 "("
  let r = con0 ")"
  let lr = Rule ([ l; r ], [])

  let test_vanish () =
    let m1 = Ordered.iterate [ lr ] [ [ l; l; r; l; r; r ] ] in
    print_string ("# m1\n" ^ Federation.pp_states m1 ^ "\n");
    let m1_expected = [ []; [ l; l; r; l; r; r ]; [ l; l; r; r ]; [ l; r ] ] in
    assert (m1 = m1_expected);
    let m2 = Ordered.iterate [ lr ] [ [ r; l; l; r; l; r; r; l ] ] in
    print_string ("# m2\n" ^ Federation.pp_states m2 ^ "\n");
    let m2_expected =
      [ [ r; l ]; [ r; l; l; r; l; r; r; l ]; [ r; l; l; r; r; l ]; [ r; l; r; l ] ]
    in
    assert (m2 = m2_expected);
    print_endline "Vanishing parentheses test passed!"
  ;;

  let t_ = con0 "T"
  let s_ = con0 "S"
  let b_ = con0 "<"
  let e_ = con0 ">"
  let t1 = Rule ([ l; r ], [ t_ ])
  let t2 = Rule ([ l; t_; r ], [ t_ ])
  let t3 = Rule ([ t_; t_ ], [ t_ ])
  let s0 = Rule ([ b_; e_ ], [ s_ ])
  let s1 = Rule ([ b_; t_; e_ ], [ s_ ])

  let test_parse () =
    let p1 = Ordered.iterate [ t1; t2; t3; s0; s1 ] [ [ b_; l; l; r; l; r; r; e_ ] ] in
    print_string ("# p1\n" ^ Federation.pp_states p1 ^ "\n");
    let p1_expected =
      [ [ b_; l; l; r; l; r; r; e_ ]
      ; [ b_; l; l; r; t_; r; e_ ]
      ; [ b_; l; t_; l; r; r; e_ ]
      ; [ b_; l; t_; r; e_ ]
      ; [ b_; l; t_; t_; r; e_ ]
      ; [ b_; t_; e_ ]
      ; [ s_ ]
      ]
    in
    assert (p1 = p1_expected);
    let p2 =
      Ordered.iterate [ t1; t2; t3; s0; s1 ] [ [ b_; r; l; l; r; l; r; r; l; e_ ] ]
    in
    print_string ("# p2\n" ^ Federation.pp_states p2 ^ "\n");
    let p2_expected =
      [ [ b_; r; l; l; r; l; r; r; l; e_ ]
      ; [ b_; r; l; l; r; t_; r; l; e_ ]
      ; [ b_; r; l; t_; l; r; r; l; e_ ]
      ; [ b_; r; l; t_; r; l; e_ ]
      ; [ b_; r; l; t_; t_; r; l; e_ ]
      ; [ b_; r; t_; l; e_ ]
      ]
    in
    assert (p2 = p2_expected);
    let p3 = Ordered.quiesce [ t1; t2; t3; s0; s1 ] [ b_; l; l; r; l; r; r; e_ ] in
    print_string ("# p3: " ^ Federation.pp_state p3 ^ "\n");
    let p3_expected = [ s_ ] in
    assert (p3 = p3_expected);
    let p4 = Ordered.quiesce [ t1; t2; t3; s0; s1 ] [ b_; r; l; l; r; l; r; r; l; e_ ] in
    print_string ("# p4: " ^ Federation.pp_state p4 ^ "\n");
    let p4_expected = [ b_; r; t_; l; e_ ] in
    assert (p4 = p4_expected);
    print_endline "Parsing example passed!"
  ;;

  let test () =
    test_increment ();
    test_vanish ();
    test_parse ();
    print_endline "All Ordered tests passed!"
  ;;
end

let () =
  SaturateTest.test ();
  LinearTest.test ();
  OrderedTest.test ();
  print_endline "% regression testing succeeded"
;;
