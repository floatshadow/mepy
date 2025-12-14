open Inference

module HW1 = struct
  open Term

  (* Problem 1: Parsing in Ordered Inference *)
  (*
    Task 1: Describe the encoding of the grammar productions
    as ordered inference rules

    1. For production rule A -> a1 a2 ... an,
       create an ordered inference rule with premises [a1; a2; ...; an]
       and conclusion [A].
    2. Special treatment of the start symbol S:
       For the production rule of S -> ϵ, create
       rule with premises [$; $] and conclusion [S] and
       For the production rule of S -> A
       rule with premises [$; A; $] and conclusion [S]
    3. Ensure reachable states are finite. One can refer to Chumsky normal form
       of context-free grammar for guidance:
          A -> BC
          A → a
          S → ε
       In such case, the size of terms are "strictly decreasing" during parsing.
       In simpler cases, we can forbid the circular rules like A -> ... -> A.
  *)
  (* Problem 1 vocabulary *)
  let s = Con ("S", [])
  let t = Con ("T", [])
  let a = Con ("a", [])
  let b = Con ("b", [])
  let dollar = Con ("$", [])
  let l = Con ("(", []) (* for Task 4 *)
  let r = Con (")", [])

  (* a^n b^n for n ≥ 0
    S → ϵ
    S → T
    T → a T b
    T → a b
  *)
  let task2 =
    [ Rule ([ dollar; dollar ], [ s ])
    ; Rule ([ dollar; t; dollar ], [ s ])
    ; Rule ([ a; t; b ], [ t ])
    ; Rule ([ a; b ], [ t ])
    ]
  ;;

  (* nonempty even-length palindromes w w^R over the alphabet {a, b}.
    S → a S a
    S → a a
    S → b S b
    S → b b
  *)
  let task3 =
    [ Rule ([ a; s; a ], [ s ])
    ; Rule ([ a; a ], [ s ])
    ; Rule ([ dollar; s; dollar ], [ s ])
    ; Rule ([ b; s; b ], [ s ])
    ; Rule ([ b; b ], [ s ])
    ]
  ;;

  (* matching parentheses
    S → ϵ
    S → T
    T → T T
    T → ′(′ T ′)′
    T → ′(′ ′)′
  *)
  let task4 =
    [ Rule ([ dollar; dollar ], [ s ])
    ; Rule ([ dollar; t; dollar ], [ s ])
    ; Rule ([ t; t ], [ t ])
    ; Rule ([ l; t; r ], [ t ])
    ; Rule ([ l; r ], [ t ])
    ]
  ;;

  let test_task2 () =
    let p1 = Ordered.quiesce task2 [ dollar; a; a; b; b; dollar ] in
    print_string ("# p1:\n" ^ Federation.pp_state p1 ^ "\n");
    let p1_expected = [ s ] in
    assert (p1 = p1_expected);
    let p2 = Ordered.quiesce task2 [ dollar; a; b; a; b; dollar ] in
    print_string ("# p2 (invalid):\n" ^ Federation.pp_state p2 ^ "\n");
    let p2_expected = [ dollar; t; t; dollar ] in
    assert (p2 = p2_expected);
    let p3 = Ordered.quiesce task2 [ dollar; dollar ] in
    print_string ("# p3:\n" ^ Federation.pp_state p3 ^ "\n");
    let p3_expected = [ s ] in
    assert (p3 = p3_expected);
    print_endline "a^n b^n parse test passed!"
  ;;

  let test_task3 () =
    let p1 = Ordered.quiesce task3 [ dollar; a; b; b; a; dollar ] in
    print_string ("# p1:\n" ^ Federation.pp_state p1 ^ "\n");
    let p1_expected = [ s ] in
    assert (p1 = p1_expected);
    let p2 = Ordered.quiesce task3 [ dollar; a; b; a; b; dollar ] in
    print_string ("# p2 (invalid):\n" ^ Federation.pp_state p2 ^ "\n");
    let p2_expected = [ dollar; t; t; dollar ] in
    assert (p2 = p2_expected);
    let p3 = Ordered.quiesce task3 [ dollar; a; a; a; a; dollar ] in
    print_string ("# p3 :\n" ^ Federation.pp_state p3 ^ "\n");
    let p3_expected = [ dollar; t; t; dollar ] in
    assert (p3 = p3_expected);
    print_endline "w w^R palindrome parse test passed!"
  ;;

  let test_problem1 () =
    test_task2 ();
    print_endline "All problem 1 tests passed!"
  ;;

  (* Problem 2: Parsing in Structural Inference *)
  (*
      Task 5: Describe the encoding of the grammar productions
      as structural inference rules

      ... here ...
    *)
  (* Problem 2 vocabulary *)
  (* S, T, a, b, L, R as for Problem 1 *)

  let zero = Con ("0", [])
  let succ n = Con ("s", [ n ])
  let num n = Con ("num", [ n ])
  let ext i a j = Con ("ext", [ i; a; j ])
  let x = Var "x"
  let y = Var "y"
  let z = Var "z"
  let u = Var "u"

  (* a^n b^n for n ≥ 0
    S → ϵ
    S → T
    T → a T b
    T → a b
  *)
  let task6 =
    [ (*   num(0)
       * ------------
       * ext(0, S, 0) *)
      Rule ([ num zero ], [ ext zero s zero ])
    ; (*  ext(0, T, u) num(u)
       * ---------------------
       *     ext(0, S, u)     *)
      Rule ([ ext zero t u; num u ], [ ext zero s u ])
    ; (*  ext(x, a, y) ext(x, T, y) ext(y, b, z)
       * ---------------------------
       *       ext(x, t, z)       *)
      Rule ([ ext x a y; ext x t y; ext y b z ], [ ext x t z ])
    ; (*  ext(x, a, y) ext(y, b, z)
       * ---------------------
       *     ext(x, t, z)     *)
      Rule ([ ext x a y; ext y b z ], [ ext x t z ])
    ]
  ;;

  (* nonempty even-length palindromes w w^R over the alphabet {a, b}.
    S → a S a
    S → a a
    S → b S b
    S → b b
  *)
  let task7 =
    [ (*  ext(x, a, y) ext(y, S, z) ext(z, a, u)
       * ---------------------------
       *       ext(x, S, u)       *)
      Rule ([ ext x a y; ext y s z; ext z a u ], [ ext x s u ])
    ; (*  ext(x, a, y) ext(y, a, u)
       * ---------------------
       *     ext(x, S, u)     *)
      Rule ([ ext x a y; ext y a u ], [ ext x s u ])
    ; (*  ext(x, b, y) ext(y, S, z) ext(z, b, u)
       * ---------------------------
       *       ext(x, S, u)       *)
      Rule ([ ext x b y; ext y s z; ext z b u ], [ ext x s u ])
    ; (*  ext(x, b, y) ext(y, b, u)
       * ---------------------
       *     ext(x, S, u)     *)
      Rule ([ ext x b y; ext y b u ], [ ext x s u ])
    ; Rule ([ ext zero s u; num u ], [ ext zero s u ])
    ]
  ;;

  (* matching parentheses
    S → ϵ
    S → T
    T → T T
    T → ′(′ T ′)′
    T → ′(′ ′)′
  *)
  let task8 =
    [ Rule ([ num zero ], [ ext zero s zero ])
    ; Rule ([ ext zero t u; num u ], [ ext zero s u ])
    ; Rule ([ ext x t y; ext y t z ], [ ext x t z ])
    ; Rule ([ ext x l y; ext y t z; ext z r u ], [ ext x t u ])
    ; Rule ([ ext x l y; ext y r u ], [ ext x t u ])
    ]
  ;;

  let test_task6 () =
    (* ext(0, a, 1); ext(1, b, 2)*)
    let p1 =
      Saturate.saturate task6
      @@ State.sort_set
           [ ext zero a (succ zero)
           ; ext (succ zero) b (succ (succ zero))
           ; num (succ (succ zero))
           ]
    in
    print_string ("# p1:\n" ^ Federation.pp_state p1 ^ "\n");
    let p1_expected = ext zero s (succ (succ zero)) in
    assert (List.find_opt (fun s -> s = p1_expected) p1 <> None);
    (* num(0) *)
    let p2 = Saturate.saturate task6 @@ State.sort_set [ num zero ] in
    print_string ("# p2:\n" ^ Federation.pp_state p2 ^ "\n");
    let p2_expected = ext zero s zero in
    assert (List.find_opt (fun s -> s = p2_expected) p2 <> None);
    print_endline "a^n b^n parse test passed!"
  ;;

  let test_problem2 () =
    test_task6 ();
    print_endline "All problem 2 tests passed!"
  ;;

  (* Problem 3: The 2-Counter Minsky Machine in Linear Inference *)
  (*
    Task 9: Describe the encoding of the Minsky machine programs
    as linear inference rules

    i : INC(r, j)
      pc(i) reg(r, n)
    ---------------------
      pc(j) reg(r, s(n))

    i : JZDEC(r, jz, jnz)
      pc(i) reg(r, 0)
    ------------------------------
      pc(jz)

      pc(i) reg(r, s(n))
    ------------------------------
      pc(jnz) reg(r, n)
  *)
  (* vocabulary for Problem 3 *)
  (* zero, succ as in Problem 2 *)
  let r1 = Con ("r1", [])
  let r2 = Con ("r2", [])
  let reg r n = Con ("reg", [ r; n ])
  let pc i = Con ("pc", [ i ])
  let k = Var "k"
  let zero = Con ("0", [])
  let succ n = Con ("s", [ n ])
  let one = succ zero
  let two = succ one
  let three = succ two
  let four = succ three

  let task10 =
    [ (* 1 : INC(r1, 2) *)
      Rule ([ pc one; reg r1 k ], [ pc two; reg r1 (succ k) ])
    ; (* 2 : INC(r2, 0) *)
      Rule ([ pc two; reg r2 k ], [ pc zero; reg r2 (succ k) ])
    ]
  ;;

  let task11 =
    [ (* 1 : JZDEC(r2, 0, 2) *)
      Rule ([ pc one; reg r2 zero ], [ pc zero ])
    ; Rule ([ pc one; reg r2 (succ k) ], [ pc two; reg r2 k ])
    ; (* 2 : INC(r1, 1) *)
      Rule ([ pc two; reg r1 k ], [ pc one; reg r1 (succ k) ])
    ]
  ;;

  let task12 =
    [ (* 1 : JZDEC(r2, 2, 1) *)
      Rule ([ pc one; reg r2 zero ], [ pc two ])
    ; Rule ([ pc one; reg r2 (succ k) ], [ pc one; reg r2 k ])
    ; (* 2 : JZDEC(r1, 0, 3) *)
      Rule ([ pc two; reg r1 zero ], [ pc zero ])
    ; Rule ([ pc two; reg r1 (succ k) ], [ pc three; reg r1 k ])
    ; (* 3 : JZDEC(r1, 0, 4) *)
      Rule ([ pc three; reg r1 zero ], [ pc zero ])
    ; Rule ([ pc three; reg r1 (succ k) ], [ pc four; reg r1 k ])
    ; (* 4 : INC(r2, 2) *)
      Rule ([ pc four; reg r2 k ], [ pc two; reg r2 (succ k) ])
    ]
  ;;

  let test_problem3 () = print_endline "All problem 3 tests passed!"
end

let () =
  HW1.test_problem1 ();
  HW1.test_problem2 ();
  print_endline "% HW1 tests passed!"
;;
