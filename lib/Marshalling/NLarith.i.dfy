module NLarith {
  lemma DivLe(a: nat, b: nat)
    requires 0 < b
    ensures 0 <= a / b <= a
  {
  }

  lemma MulPreservesLe(a: nat, b: nat, c: nat)
    requires a <= b
    ensures a * c <= b * c
  {
  }

  lemma DistributeLeft(a: int, b: int, c: int)
    ensures (a + b) * c == a * c + b * c
  {
  }
}
  
