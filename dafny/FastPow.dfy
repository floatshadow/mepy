function Power(a: int, b: nat): int {
  if b == 0 then 1 else a * Power(a, b - 1)
}


lemma Square(a: int, b: nat)
  requires b % 2 == 0
  ensures Power(a * a, b / 2) == Power(a, b)
  decreases b
 {
   if (b == 0) {
     assert Power(a * a, 0) == Power(a, 0);
   } else {
     Square(a, b - 2);
   }
 }

method FastPow(a: int, b: nat) returns (result: int)
  ensures result == Power(a, b)
{
  var x := a;
  var y := b;
  result := 1;
  while y > 0
    invariant result * Power(x, y) == Power(a, b)
    invariant y >= 0
    decreases y
  {
    if y % 2 == 1 {
      result := result * x;
      y := y - 1;
    }
    Square(x, y);
    x := x * x;
    y := y / 2;
  }
}
