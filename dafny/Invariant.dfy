method LinearSearch(a: array<int>, key: int) returns (ret: int) 
    requires a.Length > 0; // pre-condition
    ensures ret >= 0 ==> 0 <= ret < a.Length && a[ret] == key; // post-condition, find
    ensures ret < 0 ==> forall j :: 0 <= j < a.Length ==> a[j] != key; // post-condition, not find
{
  ret := -1;
  var i := 0;
  while (ret == -1 && i < a.Length) 
    // Dafny can verifiy first post-condition is a loop-invariant.
    invariant ret >= 0 ==> 0 <= ret < a.Length && a[ret] == key;
    // For sencond post-condition, it does not hold,
    // as ret's initial value is -1.
    // The loop check the array index from 0 to i - 1, thus we have:
    //  invariant ret < 0 ==> forall j ::  0 <= j < i ==> a[j] != key;
    // But Dafny cannot deduce i's range, so we introduce i's constraint.
    invariant ret < 0 ==> 0 <= i <= a.Length && forall j ::  0 <= j < i ==> a[j] != key;
    // Dafny also automatically generate property and deduce numerical invariants,
    // thus proves no 'out of index'.
  {
    if (a[i] == key) { ret := i; }
    else { i := i + 1; }
  } 
  return ret;
}


/* Three path to verify invariant:
    1. beginning of method to loop
    2. loop iteration
    3. loop end to end of the method
   Written in Hoare:
    1. {a.Length > 0} ret := -1; var i: = 0; {LoopInvariant}
    2. {LoopInvariant} assume (ret == -1 /\ i < a.Length); if (a[i] == key) { ret := i; } else { i := i + 1;} {LoopInvariant}
    3. {LoopInvariant} assume (not (ret == -1 /\ i < a.Length)); return ret; {PostConditions}

    From Zhihu @FRONTIERS: https://zhuanlan.zhihu.com/p/312501103 */
