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


}
