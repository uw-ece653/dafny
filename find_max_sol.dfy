method FindMax(a: array<int>) returns (idx: int)
  requires a != null && a.Length > 0;
  ensures 0 <= idx < a.Length;
  ensures forall k :: 0 <= k < a.Length ==> a[k] <= a[idx];
{
  var i := 0;
  idx := 0;

  while (i < a.Length)
    invariant 0 <= i <= a.Length;
    invariant 0 <= idx <= i;
    invariant 0 <= idx < a.Length;
    invariant forall k :: 0 <= k < i ==> a[k] <= a[idx];
  {
    if (a[i] > a[idx])
    {
      idx := i;
    }
    i := i + 1;
  }

  return idx;
}
