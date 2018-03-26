/** return an index of the largest element in the array */
method FindMax(a: array<int>) returns (max: int)
  requires a != null && a.Length > 0;
  ensures 0 <= max < a.Length;
  ensures forall k :: 0 <= k < a.Length ==> a[k] <= a[max];
{
  var i := 0;
  max := 0;
  while ( i < a.Length )
    invariant i <= a.Length;
    invariant max < a.Length;
    invariant forall k :: 0 <= k < i ==> a[k] <= a[max];
  {
    if (a [i] > a[max]) { max := i; }
    i := i + 1;
  }

  return max;
}
