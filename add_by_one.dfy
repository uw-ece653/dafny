method add_by_one(x:int, y:int) returns (r:int)
  ensures r == x + y;
{
  var i := 0;
  r := x;
  while (i < y)
  {
    r := r + 1;
  }

  return r;
}
