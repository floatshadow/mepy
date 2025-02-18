///|
fn pi(param : (String, Syntax), return_ty : Syntax) -> Syntax {
  TyFun(param.0, param.1, return_ty)
}

///|
fn lam(param : (String, Syntax), body : Syntax) -> Syntax {
  Lam(param.0, param.1, body)
}

///|
fn app(f : String, args : Array[Syntax]) -> Syntax {
  args.iter().fold(init=Var(f), fn(f, a) { App(f, a) })
}

///|
let predef : Array[(String, Syntax)] = [
  ("Nat", Universe(0)),
  ("zero", Var("Nat")),
  ("succ", pi(("n", Var("Nat")), Var("Nat"))),
  ("Bool", Universe(0)),
  ("tt", Var("Bool")),
  ("ff", Var("Bool")),
  (
    "if",
    pi(
      ("A", Universe(0)),
      pi(
        ("cond", Var("Bool")),
        pi(("condseq", Var("A")), pi(("alter", Var("A")), Var("A"))),
      ),
    ),
  ),
  ("List", pi(("A", Universe(0)), pi(("n", Var("Nat")), Universe(0)))),
  ("nil", pi(("A", Universe(0)), app("List", [Var("A"), Var("zero")]))),
  (
    "cons",
    pi(
      ("A", Universe(0)),
      pi(
        ("n", Var("Nat")),
        pi(
          ("hd", Var("A")),
          pi(
            ("tl", app("List", [Var("A"), Var("n")])),
            app("List", [Var("A"), app("succ", [Var("n")])]),
          ),
        ),
      ),
    ),
  ),
  (
    "eq",
    pi(
      ("A", Universe(0)),
      pi(("lhs", Var("A")), pi(("rhs", Var("A")), Universe(0))),
    ),
  ),
  (
    "refl",
    pi(
      ("A", Universe(0)),
      pi(("a", Var("A")), app("eq", [Var("A"), Var("a"), Var("a")])),
    ),
  ),
]

// (Boolean and) λ x. λ y. if x y ff
///|
let ex1 : Syntax = lam(
  ("x", Var("Bool")),
  lam(
    ("y", Var("Bool")),
    app("if", [Var("Bool"), Var("x"), Var("y"), Var("ff")]),
  ),
)

// (function application) {A : Set} {B : Π (x : A). Set}λ (f : Π (x : A). B(x)). λ (a : A). f a
///|
let ex2 : Syntax = lam(
  ("A", Universe(0)),
  lam(
    ("B", pi(("x", Var("A")), Universe(0))),
    lam(
      ("f", pi(("x", Var("A")), app("B", [Var("x")]))),
      lam(("a", Var("A")), app("f", [Var("a")])),
    ),
  ),
)

///|
fn appE(f : Syntax, args : Array[Syntax]) -> Syntax {
  args.iter().fold(init=f, fn(f, a) { App(f, a) })
}

///|
fn check_expr_has_type(typ : Syntax, expr : Syntax) -> Syntax {
  let f = lam(("x", typ), Var("x"))
  App(f, expr)
}

// λ (x : Nat). x
///|
let id : Syntax = lam(("x", Var("Nat")), Var("x"))

// (expression equality) : (id n = n) =? (n=n)
///|
let ex3 : Syntax = lam(
  ("n", Var("Nat")),
  check_expr_has_type(
    app("eq", [Var("Nat"), appE(id, [Var("n")]), Var("n")]),
    app("refl", [Var("Nat"), Var("n")]),
  ),
)

// {A : Set} Π (a : A). A
///|
let typ : Syntax = pi(("a", Var("A")), Var("A"))

// {A : Set} |- λ (x : A). x : Π (a : A). A
///|
let idA : Syntax = lam(("x", Var("A")), Var("x"))

///|
let ex4 : Syntax = lam(
  ("A", Universe(0)),
  check_expr_has_type(
    // {A : Set} |- λ (x : A). x = (λ (a : A). A) (λ (x : A). x)
    app("eq", [
      typ,
      idA,
      appE(ex2, [Var("A"), lam(("a", Var("A")), Var("A")), idA]),
    ]),
    // {A: Set} |- Π (a : A). A
    app("refl", [typ, idA]),
  ),
)

///|
fn test_infer_subst!(expr : Syntax) -> Syntax!Failure {
  let env = @immut/hashmap.from_array(predef)
  normalize!(infer_subst!(env, expr))
}

///|
test "ex1" {
  let std = pi(("x", Var("Bool")), pi(("y", Var("Bool")), Var("Bool")))
  let typ_subst = test_infer_subst!(ex1)
  assert_eq!(typ_subst, std)
}

///|
test "ex2" {
  let std = pi(
    ("A", Universe(0)),
    pi(
      ("B", pi(("x", Var("A")), Universe(0))),
      pi(
        ("f", pi(("x", Var("A")), app("B", [Var("x")]))),
        pi(("a", Var("A")), app("B", [Var("a")])),
      ),
    ),
  )
  let typ_subst = test_infer_subst!(ex2)
  assert_eq!(typ_subst, std)
}

///|
test "ex3" {
  let std = pi(("n", Var("Nat")), app("eq", [Var("Nat"), Var("n"), Var("n")]))
  let typ_subst = test_infer_subst!(ex3)
  assert_eq!(typ_subst, std)
}

///|
test "ex4" {
  let std = pi(
    ("A", Universe(0)),
    app("eq", [typ, idA, lam(("a", Var("A")), Var("a"))]),
  )
  let typ_subst = test_infer_subst!(ex4)
  assert_eq!(typ_subst, std)
}
