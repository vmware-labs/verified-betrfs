module Mathematics {

	function min(a: int, b: int) : int
	{
		if a < b
			then a
		else
			b
	}

	function max(a: int, b: int) : int
	{
		if a < b
			then b
		else
			a
	}

  function Set<T>(ms: multiset<T>) : set<T>
  {
    set x : T | x in ms
  }

  function ISet<T>(ms: set<T>) : iset<T>
  {
    iset x : T | x in ms
  }

  lemma PosMulPosIsPos(x: int, y: int)
    requires 0 < x
    requires 0 < y
    ensures 0 < x * y
  {
  }
  
  lemma DivCeilLT(x: int, d: int)
    requires 1 < d
    requires 1 < x
    ensures (x + d - 1) / d < x
  {
    PosMulPosIsPos(d-1, x-1);
    calc <= {
      0; <
      (d-1) * (x-1);
    }
  }

  lemma PosMulPreservesOrder(x: nat, y: nat, m: nat)
    requires x <= y
    ensures x * m <= y * m
  {
  }

  lemma DivPreservesOrder(num1: nat, num2: nat, denom: nat)
    requires num1 <= num2
    requires 0 < denom
    ensures num1 / denom <= num2 / denom
  {
    if num2 / denom < num1 / denom {
      assert (num2 / denom + 1) * denom <= (num1 / denom) * denom;
    }
  }

  lemma DivMulOrder(a: nat, b: nat)
    requires 0 < b
    ensures (a / b) * b <= a
  {
  }
}
