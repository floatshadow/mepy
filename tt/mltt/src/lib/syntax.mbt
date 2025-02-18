///|
pub(all) enum Syntax {
  Var(String)
  Universe(Int) // Set i
  TyFun(String, Syntax, Syntax) // Π (x : A). B[x]
  Lam(String, Syntax, Syntax) // λ (x : A). t
  App(Syntax, Syntax) // t1 t2
} derive(Show, Eq)
