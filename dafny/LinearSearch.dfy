/* Dafny program verifier finished with 1 verified, 0 errors */
method LinearSearch(a: array<int>, key: int) returns (ret: int) 
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

/* Error: index out of range */
method LinearSearchOutOfIndex(a: array<int>, key: int) returns (ret: int) 
{
  ret := -1;
  var i := 0;
  while (ret == -1 && i < a.Length) 
  {
    if (a[i + 1] == key) { ret := i; }
    else { i := i + 1; }
  } 
  return ret;
}

/* From Zhihu @FRONTIERS: https://zhuanlan.zhihu.com/p/312501103 */