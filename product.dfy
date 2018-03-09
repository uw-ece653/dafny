method CalcProduct(m: nat, n: nat) returns (res: nat)
  ensures res == m*n;
{
  var m1: nat := m;
  res := 0;

  while (m1!=0)
  {
    var n1: nat := n;
    ghost var old_res := res;
    while (n1!=0)
     {
       res := res+1;
       n1 := n1-1;
     }
    m1 := m1-1;
  }
}

































/*
method CalcThreeProduct(m: nat, n: nat, p: nat) returns (res: nat)
  ensures res == m*n*p;
{
  var m1: nat := 0;
  res := 0;

  while (m1!=m)
  {
    var n1: nat := 0;
    while (n1!=n)
    {
      var p1: nat := 0;
      while (p1!=p)
      {
        res := res+1;
        p1 := p1+1;
      }
      n1 := n1+1;
    }
    m1:= m1+1;
  }
}

*/
