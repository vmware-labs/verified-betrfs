include "Maps.s.dfy"

module Multisets {

  lemma SingletonSet<A>(a: A)
    ensures multiset{a} == multiset({a})
  {
  }

  function {:opaque} Choose<A>(s: multiset<A>) : (result: A)
    requires 0 < |s|
    ensures result in s
  {
    var a :| a in s;
    a
  }

  function {:opaque} Apply<A, B>(fn: A ~> B, s: multiset<A>) : (result: multiset<B>)
    requires forall x | x in s :: fn.requires(x)
    ensures |result| == |s|
    reads set x, o | x in s && o in fn.reads(x) :: o
  {
    if |s| == 0 then
      multiset{}
    else
      var x := Choose(s);
      multiset{fn(x)} + Apply(fn, s - multiset{x})
  }

  lemma ApplyEquivalentFns<A,B>(fn1: A ~> B, fn2: A ~> B, s: multiset<A>)
    requires forall x | x in s :: fn1.requires(x)
    requires forall x | x in s :: fn2.requires(x)
    requires forall x | x in s :: fn1(x) == fn2(x)
    ensures Apply(fn1, s) == Apply(fn2, s)
  {
    reveal_Apply();
    if |s| == 0 {
    } else {
      var x := Choose(s);
      ApplyEquivalentFns(fn1, fn2, s - multiset{x});
    }
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

  lemma ApplyMonotonic<A, B>(fn: A ~> B, s1: multiset<A>, s2: multiset<A>) 
    requires s1 <= s2
    requires forall x | x in s2 :: fn.requires(x)
    ensures Apply(fn, s1) <= Apply(fn, s2)
    ensures s1 < s2 ==> Apply(fn, s1) < Apply(fn, s2)
  {
    var rest := s2 - s1;
    ApplyAdditive(fn, s1, rest);
    assert s2 == s1 + rest;
  }
  
  predicate Foldable<A(!new)>(zero: A, add: (A, A) ~> A, inv: A -> bool)
    reads set x, y, o | inv(x) && inv(y) && o in add.reads(x, y) :: o
  {
    && inv(zero)
    && forall x, y | inv(x) && inv(y) :: add.requires(x, y) && inv(add(x, y))
  }
  
  function {:opaque} Fold<A(!new)>(zero: A, add: (A, A) ~> A, inv: A -> bool, s: multiset<A>) : (result: A)
    requires Foldable(zero, add, inv)
    requires forall x | x in s :: inv(x)
    ensures |s| == 0 ==> result == zero
    ensures inv(result)
    reads set x, y, o | inv(x) && inv(y) && o in add.reads(x, y) :: o
  {
    if |s| == 0 then
      zero
    else
      var a := Choose(s);
      add(a, Fold(zero, add, inv, s - multiset{a}))
  }

  function FoldSimple<A>(zero: A, add: (A, A) -> A, s: multiset<A>) : (result: A)
    ensures |s| == 0 ==> result == zero
  {
    Fold(zero, add, x => true, s)
  }

  lemma FoldSingleton<A>(zero: A, add: (A, A) ~> A, inv: A -> bool, x: A)
    requires Foldable(zero, add, inv)
    requires inv(x)
    ensures Fold(zero, add, inv, multiset{x}) == add(x, zero)
  {
    reveal_Fold();
  }
  
  lemma FoldSimpleSingleton<A>(zero: A, add: (A, A) -> A, x: A)
    ensures FoldSimple(zero, add, multiset{x}) == add(x, zero)
  {
    reveal_Fold();
  }
  
  predicate {:opaque} IsIdentity<A(!new)>(add: (A, A) ~> A, inv: A -> bool, zero: A)
    reads set x, y, o | inv(x) && inv(y) && o in add.reads(x, y) :: o
  {
    && Foldable(zero, add, inv)
    && forall a | inv(a) :: add(zero, a) == add(a, zero) == a
  }

  predicate {:opaque} IsCommutative<A(!new)>(add: (A, A) ~> A, inv: A -> bool)
    requires forall x, y | inv(x) && inv(y) :: add.requires(x, y)
    reads set x, y, o | inv(x) && inv(y) && o in add.reads(x, y) :: o
  {
    forall a, b | inv(a) && inv(b) :: add(a, b) == add(b, a)
  }

  predicate {:opaque} IsAssociative<A(!new)>(add: (A, A) ~> A, inv: A -> bool)
    requires forall x, y | inv(x) && inv(y) :: add.requires(x, y) && inv(add(x, y))
    reads set x, y, o | inv(x) && inv(y) && o in add.reads(x, y) :: o
  {
    forall a, b, c | inv(a) && inv(b) && inv(c) :: add(add(a, b), c) == add(a, add(b, c))
  }

  
  predicate IsIdentitySimple<A(!new)>(add: (A, A) -> A, zero: A)
  {
    IsIdentity(add, x => true, zero)
  }

  predicate IsCommutativeSimple<A(!new)>(add: (A, A) -> A)
  {
    IsCommutative(add, x => true)
  }

  predicate IsAssociativeSimple<A(!new)>(add: (A, A) -> A) {
    IsAssociative(add, x => true)
  }

  lemma FoldAdditive<A>(zero: A, add: (A, A) ~> A, inv: A -> bool, s1: multiset<A>, s2: multiset<A>)
    requires Foldable(zero, add, inv)
    requires forall x | x in s1 :: inv(x)
    requires forall x | x in s2 :: inv(x)
    requires IsCommutative(add, inv)
    requires IsAssociative(add, inv)
    requires IsIdentity(add, inv, zero)
    ensures Fold(zero, add, inv, s1 + s2) == add(Fold(zero, add, inv, s1), Fold(zero, add, inv, s2))
    decreases |s1| + |s2|
  {
    var f1 := Fold(zero, add, inv, s1);
    var f2 := Fold(zero, add, inv, s2);
    var fs := Fold(zero, add, inv, s1 + s2);
    if |s1| == 0 {
      assert s1 + s2 == s2;
      assert add(f1, f2) == Fold(zero, add, inv, s2) by {
        reveal_IsIdentity();
        reveal_Fold();
      }
    } else if |s2| == 0 {
      assert s1 + s2 == s1;
      assert add(f1, f2) == Fold(zero, add, inv, s1) by {
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
          add(x, Fold(zero, add, inv, (s1 + s2) - multiset{x}));
          { assert (s1 + s2) - multiset{x} == (s1 - multiset{x}) + s2; }
          add(x, Fold(zero, add, inv, (s1 - multiset{x}) + s2));
          { FoldAdditive(zero, add, inv, s1 - multiset{x}, s2); }
          add(x, add(Fold(zero, add, inv, s1 - multiset{x}), Fold(zero, add, inv, s2)));
          { reveal_IsAssociative(); }
          add(add(x, Fold(zero, add, inv, s1 - multiset{x})), Fold(zero, add, inv, s2));
          { reveal_IsIdentity(); reveal_Fold(); }
          add(add(Fold(zero, add, inv, multiset{x}), Fold(zero, add, inv, s1 - multiset{x})), Fold(zero, add, inv, s2));
          { FoldAdditive(zero, add, inv, multiset{x}, s1 - multiset{x}); }
          add(Fold(zero, add, inv, multiset{x} + (s1 - multiset{x})), Fold(zero, add, inv, s2));
          { assert multiset{x} + (s1 - multiset{x}) == s1; }
          add(Fold(zero, add, inv, s1), Fold(zero, add, inv, s2));
        }
      } else {
        calc {
          fs;
          { reveal_Fold(); }
          add(x, Fold(zero, add, inv, (s1 + s2) - multiset{x}));
          { assert (s1 + s2) - multiset{x} == s1 + (s2 - multiset{x}); }
          add(x, Fold(zero, add, inv, s1 + (s2 - multiset{x})));
          { FoldAdditive(zero, add, inv, s1, s2 - multiset{x}); }
          add(x, add(Fold(zero, add, inv, s1), Fold(zero, add, inv, s2 - multiset{x})));
          { reveal_IsAssociative(); }
          add(add(x, Fold(zero, add, inv, s1)), Fold(zero, add, inv, s2 - multiset{x}));
          { reveal_IsCommutative(); }
          add(add(Fold(zero, add, inv, s1), x), Fold(zero, add, inv, s2 - multiset{x}));
          { reveal_IsAssociative(); }
          add(Fold(zero, add, inv, s1), add(x, Fold(zero, add, inv, s2 - multiset{x})));
          { reveal_IsIdentity(); reveal_Fold(); }
          add(Fold(zero, add, inv, s1), add(Fold(zero, add, inv, multiset{x}), Fold(zero, add, inv, s2 - multiset{x})));
          { FoldAdditive(zero, add, inv, multiset{x}, s2 - multiset{x}); }
          add(Fold(zero, add, inv, s1), Fold(zero, add, inv, multiset{x} + (s2 - multiset{x})));
          { assert multiset{x} + (s2 - multiset{x}) == s2; }
          add(Fold(zero, add, inv, s1), Fold(zero, add, inv, s2));
        }
      }
    }
  }

  lemma FoldSimpleAdditive<A>(zero: A, add: (A, A) -> A, s1: multiset<A>, s2: multiset<A>)
    requires IsCommutativeSimple(add)
    requires IsAssociativeSimple(add)
    requires IsIdentitySimple(add, zero)
    ensures FoldSimple(zero, add, s1 + s2) == add(FoldSimple(zero, add, s1), FoldSimple(zero, add, s2))
  {
    FoldAdditive(zero, add, x => true, s1, s2);
  }  

  lemma natsumProperties()
    ensures IsCommutativeSimple<nat>((x, y) => x + y)
    ensures IsAssociativeSimple<nat>((x, y) => x + y)
    ensures IsIdentitySimple<nat>((x, y) => x + y, 0)
  {
    reveal_IsCommutative();
    reveal_IsAssociative();
    reveal_IsIdentity();
  }

  
  // TODO(rob): not really the right place for this, but can't put it
  // in Maps, since that's trusted, which precludes including this
  // file in Maps.s.dfy.
  function ValueMultisetFn<A,B>(m: map<A,B>) : (result: A ~> B)
  {
    x requires x in m => m[x]
  }
  function ValueMultiset<A,B>(m: map<A,B>) : (result: multiset<B>)
  {
    Apply(ValueMultisetFn(m), multiset(m.Keys))
  }
}
