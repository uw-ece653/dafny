// Fibonacci numbers: 0, 1, 1, 2, 3, ...
// fib(0) == 0, fib (1) == 1, fib(i) == fib(i-1) + fib(i-2)

function fib (n: nat) : nat
{
  if n == 0 then 0
  else if n == 1 then 1
  else fib (n-1) + fib (n-2)
}

method Fib (n: nat) returns (b: nat)
  ensures b == fib(n);
{
  if (n == 0) { return 0; }
  var a := 0;
  b := 1;
  
  var i := 1;
  while (i < n)
    invariant i <= n
    invariant a == fib(i-1);
    invariant b == fib(i);
  {
    a, b := b, a + b;
    i := i + 1;
  }
}
