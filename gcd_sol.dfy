function gcd(m: nat, n: nat): nat
  requires m>=1;
  requires n>=1;
  decreases m+n;
{ 
  if (n==m) then n 
  else if (m>n) then gcd(m-n, n) 
  else gcd(m, n-m) 
}

method GcdCal(m: nat, n: nat) returns (res: nat)
  requires m>=1;
  requires n>=1;
  ensures res == gcd(m, n);
{ 
  var m1: nat, n1: nat := m, n;
  while (m1!=n1) 
    invariant m1 >= 1;
    invariant n1 >= 1;
    invariant gcd(m1, n1) == gcd (m, n)
    decreases m1+n1
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

