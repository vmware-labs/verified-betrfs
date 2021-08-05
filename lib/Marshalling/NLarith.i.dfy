include "../Lang/NativeTypes.s.dfy"

module NLarith {
  import opened NativeTypes

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

  method Uint64Mult(a: uint64, b: uint64) returns (c: uint64)
    requires a as nat * b as nat < Uint64UpperBound()
    ensures c as nat == a as nat * b as nat
  {
    c := a * b;
  }
}
  
