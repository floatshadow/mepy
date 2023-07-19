method LinearSearch(a: array<int>, key: int) returns (ret: int) 
    requires a.Length > 0; // pre-condition
    ensures ret >= 0 ==> 0 <= ret < a.Length && a[ret] == key; // post-condition, find
    ensures ret < 0 ==> forall j :: 0 <= j < a.Length ==> a[j] != key; // post-condition, not find
{
  ret := -1;
  var i := 0;
  while (ret == -1 && i < a.Length) 
  {
    if (a[i] == key) { ret := i; }
    else { i := i + 1; }
  } 
  return ret;
}

/*  We does not handle loop invariant
 *  Conditions.dfy(13,2): Error: a postcondition could not be proved on this return path
 *  Conditions.dfy(4,24): Related location: this is the postcondition that could not be proved
 *  Conditions.dfy(4,54): Related location
 *  Conditions.dfy(4,63): Related location
 *  Conditions.dfy(13,2): Error: a postcondition could not be proved on this return path
 *  Conditions.dfy(3,55): Related location: this is the postcondition that could not be proved
 *  Conditions.dfy(13,2): Error: a postcondition could not be proved on this return path
 *  Conditions.dfy(3,34): Related location: this is the postcondition that could not be proved
 */

/* From Zhihu @FRONTIERS: https://zhuanlan.zhihu.com/p/312501103 */