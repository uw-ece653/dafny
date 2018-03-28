function gcd(m: nat, n: nat) : nat
  requires m >= 1;
  requires n >= 1;
{
  if (m == n) then m
  else if (m < n) then gcd(m, n-m)
  else gcd(m-n, n)
}

lemma gcd_lemma(m: nat, n: nat)
  requires m >= 1 && n >= 1;
  ensures gcd(m,n) == gcd(n,m);
{
}
/*
 * Implement a method to compute
 * greatest common divisor of two numbers m and n.
 *
 * A number r is a divisor of a number m iff m == r * k for some number k.
 *
 * If r is a divisor of m and n and m is greater than n,
*  then r is a divisor of m-n
 */
method GcdCal(m: nat, n: nat) returns (res: nat)
  requires m >= 1 && n >= 1;
  ensures res == gcd(m, n);
{
  var m1: nat, n1: nat := m, n;

  gcd_lemma(m, n);
  while (m1!=n1)
    invariant m1 >= 1;
    invariant n1 >= 1;
    decreases m1+n1;
    invariant gcd(m1, n1) == gcd(n, m)
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




/*
   function gcd(m: nat, n: nat): nat
{
  if (n==m) then n
  else if (m>n) then gcd(m-n, n)
  else gcd(m, n-m)
}
*/




/* gcd lemma: use gcd(m, n) = gcd(n1, m1) */
