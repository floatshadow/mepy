predicate sorted(a: array<int>)
  reads a;
{
   forall j, k :: 0 <= j < k < a.Length ==> a[j] <= a[k]
}

method BinarySearch(a: array<int>, key: int) returns (index: int)
    requires sorted(a); // pre-condition
    requires a.Length > 0;
    ensures index >= 0 ==> 0 <= index < a.Length && a[index] == key; // post-condition, functional correctness.
    ensures index < 0 ==> forall j :: 0 <= j < a.Length ==> a[j] != key;

{
  var low := 0;
  var high := a.Length;
  while (low < high)
    invariant 0 <= low <= high <= a.Length;
    invariant forall j :: 0 <= j < low ==> a[j] < key;
    invariant forall j :: high <= j < a.Length ==> a[j] > key;
  {
    var mid := (low + high) / 2;
    if (a[mid] < key) { low := mid + 1; }
    else if (key < a[mid]) { high := mid; } 
    else { return mid; }
  }
  return -1;
}