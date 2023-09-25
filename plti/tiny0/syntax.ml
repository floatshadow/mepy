
module Tiny = struct
  type expr = 
    | Const of int
    | Add of expr * expr
    | Mul of expr * expr

  (** Interpreter, semantic evaluation rules
      e => v, big step operational semantics *)
  let rec eval expr = 
    match expr with
    | Const x -> x
    | Add (x, y) -> eval x + eval y
    | Mul (x, y) -> eval x * eval y
end

module Stack = struct
  exception IllegalInstSeq

  type instr = 
    | Const of int
    | Add
    | Mul
  
  (** Transition of the stack machine 
      [e] -> v, small step *)
  let rec eval instrs stk = 
    match instrs, stk with
    | Const x :: instrs', _ -> eval instrs' (x :: stk)
    | Add :: instrs', a :: b :: stk' -> eval instrs' ((a + b) :: stk')
    | Mul :: instrs', a :: b :: stk' -> eval instrs' ((a * b) :: stk')
    | [], x :: _ -> x
    | _ -> raise IllegalInstSeq
end

(** Formalization, compilation corresponds to Expr to an instruction sequence.
    Invariant: stack balance property (proof by induction).
    The correctness of compilation: big step <=> small step *)
let rec compile (expr: Tiny.expr) : Stack.instr list =
  match expr with
  | Const x -> [Stack.Const x]
  | Add (x, y) -> (compile x) @ (compile y) @ [Stack.Add]
  | Mul (x, y) -> (compile x) @ (compile y) @ [Stack.Mul]
