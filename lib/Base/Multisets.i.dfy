module Multisets {
  function {:opaque} Choose<A>(s: multiset<A>) : (result: A)
    requires 0 < |s|
    ensures result in s
  {
    var a :| a in s;
    a
  }

  function {:opaque} Apply<A, B>(fn: A ~> B, s: multiset<A>) : (result: multiset<B>)
    requires forall x | x in s :: fn.requires(x)
    ensures |s| == 0 ==> |result| == 0
    reads set x, o | x in s && o in fn.reads(x) :: o
  {
    if |s| == 0 then
      multiset{}
    else
      var x := Choose(s);
      multiset{fn(x)} + Apply(fn, s - multiset{x})
  }

  lemma ApplySingleton<A, B>(fn: A ~> B, x: A)
    requires fn.requires(x)
    ensures Apply(fn, multiset{x}) == multiset{fn(x)}
  {
    reveal_Apply();
  }
  
  lemma ApplyAdditive<A,B>(fn: A ~> B, s1: multiset<A>, s2: multiset<A>)
    requires forall x | x in s1 :: fn.requires(x)
    requires forall x | x in s2 :: fn.requires(x)
    ensures Apply(fn, s1+s2) == Apply(fn, s1) + Apply(fn, s2)
    decreases |s1| + |s2|
  {
    if |s1| == 0 {
      assert s1 + s2 == s2;
    } else if |s2| == 0 {
      assert s1 + s2 == s1;
    } else {
      var x := Choose(s1 + s2);
      if x in s1 {
        calc {
          Apply(fn, s1+s2);
          { reveal_Apply(); }
          multiset{fn(x)} + Apply(fn, (s1+s2) - multiset{x});
          { assert (s1+s2) - multiset{x} == (s1 - multiset{x}) + s2; }
          multiset{fn(x)} + Apply(fn, (s1 - multiset{x}) + s2);
          { ApplyAdditive(fn, s1 - multiset{x}, s2); }
          multiset{fn(x)} + Apply(fn, s1 - multiset{x}) + Apply(fn, s2);
          { reveal_Apply(); }
          Apply(fn, multiset{x}) + Apply(fn, s1 - multiset{x}) + Apply(fn, s2);
          { ApplyAdditive(fn, multiset{x}, s1 - multiset{x}); }
          Apply(fn, multiset{x} + (s1 - multiset{x})) + Apply(fn, s2);
          { assert multiset{x} + (s1 - multiset{x}) == s1; }
          Apply(fn, s1) + Apply(fn, s2);
        }
      } else {
        calc {
          Apply(fn, s1+s2);
          { reveal_Apply(); }
          multiset{fn(x)} + Apply(fn, (s1+s2) - multiset{x});
          { assert (s1+s2) - multiset{x} == s1 + (s2 - multiset{x}); }
          multiset{fn(x)} + Apply(fn, s1 + (s2 - multiset{x}));
          { ApplyAdditive(fn, s1, s2 - multiset{x}); }
          multiset{fn(x)} + Apply(fn, s1) + Apply(fn, s2 - multiset{x});
          { reveal_Apply(); }
          Apply(fn, multiset{x}) + Apply(fn, s1) + Apply(fn, s2 - multiset{x});
          { ApplyAdditive(fn, multiset{x}, s2 - multiset{x}); }
          Apply(fn, multiset{x} + (s2 - multiset{x})) + Apply(fn, s1);
          { assert multiset{x} + (s2 - multiset{x}) == s2; }
          Apply(fn, s1) + Apply(fn, s2);
        }
      }
    }
  }
  
  function {:opaque} Fold<A>(zero: A, add: (A, A) -> A, s: multiset<A>) : (result: A)
    ensures |s| == 0 ==> result == zero
  {
    if |s| == 0 then
      zero
    else
      var a := Choose(s);
      add(a, Fold(zero, add, s - multiset{a}))
  }

  lemma FoldSingleton<A>(zero: A, add: (A, A) -> A, x: A)
    ensures Fold(zero, add, multiset{x}) == add(x, zero)
  {
    reveal_Fold();
  }
  
  predicate {:opaque} IsIdentity<A(!new)>(add: (A, A) -> A, zero: A) {
    && forall a :: add(zero, a) == add(a, zero) == a
  }

  predicate {:opaque} IsCommutative<A(!new)>(add: (A, A) -> A) {
    forall a, b :: add(a, b) == add(b, a)
  }

  predicate {:opaque} IsAssociative<A(!new)>(add: (A, A) -> A) {
    forall a, b, c :: add(add(a, b), c) == add(a, add(b, c))
  }

  lemma FoldAdditive<A>(zero: A, add: (A, A) -> A, s1: multiset<A>, s2: multiset<A>)
    requires IsCommutative(add)
    requires IsAssociative(add)
    requires IsIdentity(add, zero)
    ensures Fold(zero, add, s1 + s2) == add(Fold(zero, add, s1), Fold(zero, add, s2))
    decreases |s1| + |s2|
  {
    var f1 := Fold(zero, add, s1);
    var f2 := Fold(zero, add, s2);
    var fs := Fold(zero, add, s1 + s2);
    if |s1| == 0 {
      assert s1 + s2 == s2;
      assert add(f1, f2) == Fold(zero, add, s2) by {
        reveal_IsIdentity();
        reveal_Fold();
      }
    } else if |s2| == 0 {
      assert s1 + s2 == s1;
      assert add(f1, f2) == Fold(zero, add, s1) by {
        reveal_IsIdentity();
        reveal_Fold();
      }
    } else {
      var x := Choose(s1 + s2);
      assert x in s1 || x in s2;
      if x in s1 {
        calc {
          fs;
          { reveal_Fold(); }
          add(x, Fold(zero, add, (s1 + s2) - multiset{x}));
          { assert (s1 + s2) - multiset{x} == (s1 - multiset{x}) + s2; }
          add(x, Fold(zero, add, (s1 - multiset{x}) + s2));
          { FoldAdditive(zero, add, s1 - multiset{x}, s2); }
          add(x, add(Fold(zero, add, s1 - multiset{x}), Fold(zero, add, s2)));
          { reveal_IsAssociative(); }
          add(add(x, Fold(zero, add, s1 - multiset{x})), Fold(zero, add, s2));
          { reveal_IsIdentity(); reveal_Fold(); }
          add(add(Fold(zero, add, multiset{x}), Fold(zero, add, s1 - multiset{x})), Fold(zero, add, s2));
          { FoldAdditive(zero, add, multiset{x}, s1 - multiset{x}); }
          add(Fold(zero, add, multiset{x} + (s1 - multiset{x})), Fold(zero, add, s2));
          { assert multiset{x} + (s1 - multiset{x}) == s1; }
          add(Fold(zero, add, s1), Fold(zero, add, s2));
        }
      } else {
        calc {
          fs;
          { reveal_Fold(); }
          add(x, Fold(zero, add, (s1 + s2) - multiset{x}));
          { assert (s1 + s2) - multiset{x} == s1 + (s2 - multiset{x}); }
          add(x, Fold(zero, add, s1 + (s2 - multiset{x})));
          { FoldAdditive(zero, add, s1, s2 - multiset{x}); }
          add(x, add(Fold(zero, add, s1), Fold(zero, add, s2 - multiset{x})));
          { reveal_IsAssociative(); }
          add(add(x, Fold(zero, add, s1)), Fold(zero, add, s2 - multiset{x}));
          { reveal_IsCommutative(); }
          add(add(Fold(zero, add, s1), x), Fold(zero, add, s2 - multiset{x}));
          { reveal_IsAssociative(); }
          add(Fold(zero, add, s1), add(x, Fold(zero, add, s2 - multiset{x})));
          { reveal_IsIdentity(); reveal_Fold(); }
          add(Fold(zero, add, s1), add(Fold(zero, add, multiset{x}), Fold(zero, add, s2 - multiset{x})));
          { FoldAdditive(zero, add, multiset{x}, s2 - multiset{x}); }
          add(Fold(zero, add, s1), Fold(zero, add, multiset{x} + (s2 - multiset{x})));
          assert multiset{x} + (s2 - multiset{x}) == s2;
          add(Fold(zero, add, s1), Fold(zero, add, s2));
        }
      }
    }
  }
}
