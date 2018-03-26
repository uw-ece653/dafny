/* find value in a sorted array using binary search */
method BinarySearch(a: array<int>, value: int) returns (index: int)
  requires a != null && a.Length > 0;
  requires forall i, j :: 0 <= i < j < a.Length ==> a[i] <= a[j];
  ensures -1 <= index < a.Length;
  ensures 0 <= index < a.Length ==> a[index] == value;
  ensures index == -1 ==> forall k :: 0 <= k < a.Length ==> a[k] != value;
{
  var low, high := 0, a.Length;
  while low < high
    invariant 0 <= low <= high <= a.Length;
    invariant forall k :: 0 <= k < a.Length && !(low <= k < high) ==> a[k] != value;
  {
    var mid:int := (low + high) / 2;
    if a[mid] < value
    {
      low := mid + 1;
    }
    else if value < a[mid]
    {
      high := mid;
    }
    else
    {
      return mid;
    }
  }
  return -1;
}






































/* method BinarySearch(a: array<int>, value: int) returns (index: int)
{
   var low, high := 0, a.Length;
   while low < high
   {
      var mid := (low + high) / 2;
      if a[mid] < value
      {
         low := mid + 1;
      }
      else if value < a[mid]
      {
         high := mid;
      }
      else
      {
         return mid;
      }
   }
   return -1;
}
*/
