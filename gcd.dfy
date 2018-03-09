function gcd(m: nat, n: nat): nat
{
  if (n==m) then n
  else if (m>n) then gcd(m-n, n)
  else gcd(m, n-m)
}



















/*
method GcdCal(m: nat, n: nat) returns (res: nat)
  ensures res == gcd(m, n);
{
  var m1: nat, n1: nat := m, n;

  while (m1!=n1)
  {
    if (m1>n1) {
      m1 := m1-n1;
    }
    else {
      n1 := n1-m1;
    }
 }
 return m1;
}
 */









/* gcd lemma: use gcd(m, n) = gcd(n1, m1) */
