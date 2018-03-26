/** find first occurrence of key in a */
method Find(a: array<int>, key: int) returns (index: int)
  requires a != null;
  ensures 0 <= index < a.Length ==> a[index] == key;
  ensures index == -1 ==> forall z :: 0 <= z < a.Length ==> a[z] != key;
{
  var i := 0;
  while (i < a.Length)
    invariant i <= a.Length;
    invariant forall k :: 0 <= k < i ==> a[k] != key;
  {
    if (a[i] == key) { return i;}
    i := i + 1;
  }
  return -1;
}
