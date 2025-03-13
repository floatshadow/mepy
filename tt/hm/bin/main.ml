open! Base
open Hm
open Util
open Infer
open Type
open Syntax
open Stdlib

[@@@warning "-32"]

let () = Printexc.record_backtrace true

let infer_without_let expr =
  print_newline ();
  (* 也可以将 print_expr 换成 print_expr_in_ocaml，这样的打印出的 term 可以直接在 utop 中使用并被给出其类型 *)
  (* 这是一种很好的调试手段 *)
  print_expr_in_ocaml expr;
  print_newline ();
  print_ty @@ Infer_no_let.infer Infer_no_let.initial_ctx expr

let infer_with_let expr =
  print_newline ();
  print_expr expr;
  print_newline ();
  print_ty @@ Infer.infer Infer.initial_ctx expr

let () =
  infer_without_let ?@{|\x. x + 1|};
  (* infer_without_let ?@{|\f. (\x. f (x x)) (\x. f (x x))|}; *)
  infer_with_let ?@{|let id = \x. x in let add = \f. \g. \x. (f (g x)) in (add id)|};
  infer_with_let ?@{|\x. let a = x true in x 0|};
  infer_with_let ?@{|\f. if f true then f 0 else f 0|};
  infer_with_let ?@{|let s = \x. \y. \z. (x z) (y z) in s|};
  infer_with_let ?@{|let id = \x. x in id|};
  infer_with_let ?@{|let id = \x. x in let a = id 0 in id true|};
  infer_with_let ?@{|let double = \f. \x. f (f x) in double|};
  infer_with_let
    ?@{|let b = true in
let f0 = \x. x + 1 in
let f = \x. if b then f0 else \y. x y in
let f = \x. if b then f else \y. x y in
f |}