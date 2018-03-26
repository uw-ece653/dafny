method Find(a: array<int>, key: int) returns (index: int)
   requires a != null
   ensures 0 <= index ==> index < a.Length && a[index] == key
   ensures index < 0 ==> forall k :: 0 <= k < a.Length ==> a[k] != key
{
  var i := 0;

  while (i < a.Length)
    invariant 0 <= i <= a.Length
    invariant forall j :: 0 <= j < i ==> a[j] != key;
  {
    if (a[i] == key) { return i; }
    i := i + 1;
  }
  return -1;
}
