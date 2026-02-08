datatype List<T> = Nil | Cons(e: T, l: List<T>)

function Length<T>(l: List<T>): nat
{
  match l
  case Nil => 0
  case Cons(_, l) => 1 + Length(l)
}

// postcondition

function Append<T>(l1: List<T>, l2: List<T>): List<T>
  ensures Length(Append(l1, l2)) == Length(l1) + Length(l2)
{
  match l1 {
    case Nil => l2
    case Cons(e, l) => Cons(e, Append(l, l2))
  }
}

// Method body serves as both proof and code.
// Consider the case that the post-condition of Append is stronger than the body.

lemma {:axiom} SomeProperty()
  ensures forall n: nat :: n % 2 == 0 ==> exists m: nat :: n == 2 * m

function AppendWithLemma<T>(l1: List<T>, l2: List<T>): List<T>
  ensures Length(AppendWithLemma(l1, l2)) == Length(l1) + Length(l2)
  ensures forall n: nat :: n % 2 == 0 ==> exists m: nat :: n == 2 * m
{
  SomeProperty();
  match l1 {
    case Nil => l2
    case Cons(e, l) => Cons(e, AppendWithLemma(l, l2))
  }
}

function AppendInlineLemma<T>(l1: List<T>, l2: List<T>): List<T>
  ensures Length(AppendInlineLemma(l1, l2)) == Length(l1) + Length(l2)
  ensures forall n: nat :: n % 2 == 0 ==> exists m: nat :: n == 2 * m
{
  assert forall n: nat :: n % 2 == 0 ==> exists m: nat :: n == 2 * m by {
    forall n: nat
      ensures n % 2 == 0 ==> exists m: nat :: n == 2 * m
    {
      if n % 2 == 0 {
        assert n == 2 * (n/2);
      }
    }
  }
  match l1 {
    case Nil => l2
    case Cons(e, l) => Cons(e, AppendInlineLemma(l, l2))
  }
}



function LengthTr'<T>(l: List, acc: nat): nat
  ensures acc + Length(l) == LengthTr'(l, acc)
{
  match l
  case Nil => acc
  case Cons(_, tail) => LengthTr'(tail, 1 + acc)
}

function LengthTr<T>(l: List): nat
  ensures Length(l) == LengthTr'(l, 0)
{
  LengthTr'(l, 0)
}


// Should a property be declared (“intrinsically”) as a postcondition or (“extrinsically”) a lemma?
// The benefit of a postcondition is that it is automatically included in the KB (knowledge base): more automation
// However, some properties are really extrinsic
//   Example: associativity
// Quantification would have a high cost on verification
//   In general: having a quantified postcondition is likely to be a problem
// But you can't even do it because of termination
//   function Append<T(!new)>(l1: List, l2: List): List
//   ensures Length(Append(l1, l2)) == Length(l1) + Length(l2)
//   
//   fails: ensures forall l3: List :: Append(Append(l1, l2), l3) == Append(l1, Append(l2, l3))
//   a forall expression involved in a function definition is not allowed to depend on the set of allocated references, but values of 'l3' (of type 'List<T>') may contain references (see documentation for 'older' parameters)


// precondition
// A function with a precondition is a partial function
// In contrast, a function without precondition is total
// Partial and Total functions do not have the same type
// A total function from type A to B is of type A -> B
// A partial function from type A to B is of type A --> B

function Head<T>(l: List<T>): T
  requires l != Nil
{
  match l {
    // case Nil => assert false; // unreachable
    case Cons(e, _) => e
  }
}

function Tail<T>(l: List<T>): List<T>
  requires l != Nil
{
  match l {
    // case Nil => assert false; // unreachable
    case Cons(_, tail) => tail
  }
}

function At<T>(l: List<T>, index: nat): T
  requires index < Length(l)
{
  if index == 0 then Head(l) else At(Tail(l), index - 1)
}

// T is a type that does not contain references to newly allocated heap objects.
lemma AtProp<T(!new)>(l: List, idx: nat)
  requires idx < Length(l)
  ensures exists v: T :: At(l, idx) == v // see quantifer instantiation rules in manual
{
}


// Higher-order functions
// Dafny and F* encode functions into the SMT logic using universally quantified axioms of the form
// forall x y z. f x y z = e, where any higher-order function has been defunctionalized

// f is partial function, `.requires` member is Boolean-valued total ghost function
function Hof<U, V>(f: U --> V, a: U): V
  requires f.requires(a)
{
  f(a)
}


// refinement type
type NonNegativeNat = n: int | 0 <= n witness 0 // ensure nonempty type 

method m(z: nat) {
  var x := z + 3; // int
  var y: nat := z + 3; // nat
}


ghost predicate Associative<T(!new)>(BinOp: (T, T) -> T) {
  forall x: T, y: T, z: T :: BinOp(BinOp(x, y), z) == BinOp(x, BinOp(y, z))
}

ghost predicate Identity<T(!new)>(BinOp: (T, T) -> T, elt: T) {
  forall x: T :: BinOp(x, elt) == x
}

ghost predicate Inverse<T(!new)>(BinOp: (T, T) -> T, elt: T) {
  forall x: T :: exists y: T :: BinOp(x, y) == elt && BinOp(y, x) == elt 
}

type Group<!T(!new)> = S: ((T, T) -> T, T) | 
  && Associative(S.0) 
  && Identity(S.0, S.1)  
  && Inverse(S.0, S.1)
  witness *