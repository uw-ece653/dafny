/* see visualgo for an animation of Bubble sort */
method bubbleSort (a: array<int>)
  requires a != null && a.Length > 1;
  ensures forall u, v :: 0 <= u < v < a.Length ==> a[u] <= a[v];
  modifies a;
{
  var i:nat := 1;
  while (i < a.Length)
    invariant i <= a.Length;
    invariant forall u, v:: 0 <= u < v < i ==> a[u] <= a[v];
  {
    var j:nat := i;
    while (j > 0)
      invariant 0 <= j <= i;
      invariant forall u, v :: 0 <= u < v < j ==> a[u] <= a[v];
      invariant forall u, v :: j <= u < v < i+1 ==> a[u] <= a[v];
      invariant forall u , v :: 0 <= u < j < v < i+1 ==> a[u] <= a[v]
    {
      if (a[j-1] > a[j]) {
        var temp:int := a[j-1];
        a[j] := temp;
        a[j-1] := a[j];
      }
      j := j - 1;
    }
    i := i+1;
  }
}
