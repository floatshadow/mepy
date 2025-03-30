pub typealias ScDefs = List[ScDef[String]]
pub enum RawExpr[T] {
  Var(T)
  Num(Int)
  Ctor(tag~:Int, arity~:Int)
  App(RawExpr[T], RawExpr[T])
  Let(isrec~: Bool, defs~: List[(T, RawExpr[T])], body~: RawExpr[T])
  Case(RawExpr[T], List[(Int, List[T], RawExpr[T])])
} derive(Show)


// Super combinator definition.
// A super combinator without parameters is referred to Constant Applicative From (CAF).
pub struct ScDef[T] {
  name: String
  args: List[T]
  body: RawExpr[T]
} derive(Show)

pub fn ScDef::new[T](name: String, args: List[T], body: RawExpr[T]) -> ScDef[T] {
  ScDef:: { name, args, body }
}

pub let preludes : List[ScDef[String]] = {
  let args : (FixedArray[String]) -> List[String] = @immut/list.of
  let id = ScDef::new("id", args(["x"]), Var("x"))
  let k =
    ScDef::new("K", args(["x", "y"]), Var("x")) // K x y = x
  let k1 = ScDef::new("K1", args(["x", "y"]), Var("y")) // K1 x y = y
  let s =
    ScDef::new("S", args(["f", "g", "x"]), App(App(Var("f"), Var("x")), App(Var("g"), Var("x")))) // S f g x = f x (g x)
  let compose =
    ScDef::new("compose", args(["f", "g", "x"]), App(Var("f"), App(Var("g"), Var("x"))) ) // compose f g x = f (g x)
  let twice =
    ScDef::new("twice", args(["f"]), App(App(Var("compose"), Var("f")), Var("f")) ) // twice f = compose f f
  @immut/list.of([id, k, k1, s, compose, twice])
}