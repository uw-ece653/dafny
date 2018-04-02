predicate sorted_range(a: array<int>, l:nat, u:nat)
  requires a != null;
  requires 0 <= l <= u <= a.Length;
  reads a;
{
  forall i, j :: l <= i < j < u ==> a[i] <= a[j]
}
predicate pivot(a:array<int>, pv:nat, l:nat, up:nat)
  requires a != null;
  requires 0 <= l <= pv <= up <= a.Length;
  reads a;
{
  forall u , v :: l <= u < pv < v < up ==> a[u] <= a[v]
}

/* see visualgo for an animation of Bubble sort */
method bubbleSort (a: array<int>)
  requires a != null && a.Length > 1;
  ensures sorted_range(a, 0, a.Length);
  ensures multiset(a[..]) == multiset(old(a[..]));
  modifies a;
{
  var i:nat := 1;
  while (i < a.Length)
    invariant i <= a.Length;
    invariant sorted_range (a, 0, i);
    invariant multiset(a[..]) == multiset(old(a[..]));
  {
    var j:nat := i;
    while (j > 0)
      invariant 0 <= j <= i;
      invariant sorted_range (a, 0, j)
      invariant sorted_range (a, j, i+1);
      invariant pivot(a, j, 0, i+1);
      invariant multiset(a[..]) == multiset(old(a[..]));
    {
      if (a[j-1] > a[j]) {
        var temp:int := a[j-1];
        a[j-1] := a[j];
        a[j] := temp;

      }
      j := j - 1;
    }
    i := i+1;
  }
}
