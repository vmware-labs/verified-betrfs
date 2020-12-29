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

  lemma DivMulOrder(a: nat, b: nat)
    requires 0 < b
    ensures (a / b) * b <= a
  {
  }

  lemma DivisionAlgorithm(x: nat, q: nat, d: nat, r: nat) 
    requires 0 < d
    requires x == q * d + r
    requires 0 <= r < d
    ensures q == x / d
    ensures r == x % d
  {
    if q < x / d {
      calc <= {
        q * d + r;
        (x / d - 1) * d + r;
        x / d * d - d + r;
        x - d + r;
        < x;
      }
    } else if x / d < q {
      calc <= {
        x;
        (x/d + 1) * d + r;
        q * d + r;
      }
    }
  }
  
  lemma MulDivCancel(x: nat, d: nat)
    requires 0 < d
    ensures (x * d) / d == x
  {
    DivisionAlgorithm(x * d, x, d, 0);
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

  lemma InequalityMoveDivisor(a: nat, b: nat, d: nat)
    requires 0 < d
    ensures a <= b / d <==> a * d <= b
  {
    MulDivCancel(a, d);
    MulDivCancel(b, d);
    if a * d <= b {
      DivPreservesOrder(a * d, b, d);
    }
  }
}
