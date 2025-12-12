using @list { type List }

// A example of lazy List.
enum Stream[T] {
  Empty
  Cons(T, () -> Stream[T])
}

fn[T] Stream::from_list(l : List[T]) -> Stream[T] {
  match l {
    Empty => Stream::Empty
    More(x, tail=xs) => Stream::Cons(x, fn () { Stream::from_list(xs) } )
  }
}

fn[A, B] Stream::map(self: Stream[A], f: (A) -> B) -> Stream[B] {
  match self {
    Empty => Empty
    Cons(x, xs) => Cons(f(x), fn () { xs().map(f) })
  }
}

fn[T] Stream::take(self: Stream[T], n: Int) -> List[T] {
  if n == 0 {
    @list.empty()
  } else {
    match self {
      Empty => @list.empty()
      Cons(x, xs) => @list.cons(x, xs().take(n - 1))
    }
  }
}


// Runtime representation in lazy evaluation,
// reduction on the nodes of the graph.
enum LazyData[T] {
  Waiting(() -> T)
  Done(T)
}

struct LazyRef[T] {
  mut data : LazyData[T]
}

fn[T] LazyRef::extract(self: LazyRef[T]) -> T {
  match self.data {
    Waiting(thunk) => {
      let value = thunk()
      self.data = Done(value)
      value
    }
    Done(x) => x
  }
}

// We assume `mul` is pre-defined operation,
// `square` is a user-defined super combinator.
// `(square 3)` is a reducible expression (redex).
// `(mul 3 3) -> 9` cannot be reduced further, `9` is a "Normal Form".
// We assume "Normal Order Reduction", where outermost redex is reduced first.
//
// e.g., (add 33 (square 3)) -> App(App(add, 33), App(square, 3))
// "Weak Head Normal Form" (WHNF): a redex has fewer arguments than
// required by the super combinator, even if its sub-expression contains
// redexes, no action is needed. Fromally:
//   - a constructor (eventually applied to arguments), like `True`, `Just (square 42)` or `(:) 1`
//   - a built-in function applied to few arguments, e.g., `(+) 2` or `sqrt`.
//   - a lambda abstraction, e.g., `\x -> expression`
// 
fn LazyRef::square(x: LazyRef[Int]) -> Int {
  x.extract() * x.extract()
}