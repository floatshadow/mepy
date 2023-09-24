open OUnit2
open Syntax

let test_compile exprs = 
  let instrs = compile exprs in
    assert_equal (Tiny.eval exprs) (Stack.eval instrs [])

let tests = "test compilation..." >::: [
  "0" >:: (fun _ -> test_compile (Tiny.Const 43));
  "1" >:: (fun _ -> test_compile (Tiny.Add(Tiny.Const 1, Tiny.Const 2)));
  "2" >:: (fun _ -> test_compile (Tiny.Mul(Tiny.Const 1, Tiny.Const 2)));
  "3" >:: (fun _ -> test_compile (Tiny.Add(Tiny.Mul(Tiny.Const 1, Tiny.Const 2),Tiny.Const 3)))
]

let _ = run_test_tt_main tests