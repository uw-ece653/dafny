function add (x: nat, y: nat): nat
  decreases y
{
  if (y == 0) then x
  else add (x, y-1) + 1
}

lemma add_zero_lemma (x: nat)
  ensures add (x, 0) == x
{
  calc
  {
    add (x, 0);
    x;
  }
}

lemma zero_add_lemma (x: nat)
  ensures add (0, x) == x
{
  if (x == 0) { }
  else
  {
    calc
    {
      add (0, x);
      add (0, x-1) + 1;
      { zero_add_lemma (x-1); }
      x -1 + 1;
      x;
    }
  }
}

lemma add_plus_one (x: nat, y: nat)
  ensures add(x, y) + 1 == add(x, y+1);
{
  calc
  {
    add (x, y) + 1;
    add (x, y + 1);
  }
}

lemma one_plus_add (x: nat, y: nat)
  ensures add(x, y) + 1 == add (x+1, y)
{
  if (y == 0) { }
  else
  {
    calc
    {
      add (x, y) + 1;
      add (x, y-1) + 1 + 1;
      { one_plus_add (x, y-1); }
      add (x+1, y-1) + 1;
      { add_plus_one (x+1, y-1); }
      add (x+1, y);
    }
  }
}

lemma add_comm_lemma (x: nat, y: nat)
  ensures add (x, y) == add (y, x);
{
  if (y == 0) { }
  else
  {
    calc
    {
      add (x, y);
      add (x, y-1) + 1;      
      add (y-1, x) + 1;
      add (y, x);
    }
    
  }
}

