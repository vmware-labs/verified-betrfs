include "Maps.s.dfy"
include "sequences.i.dfy"

module Multisets {
  import Sequences

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
  
  lemma ApplySeq<A, B>(fn: A ~> B, s: seq<A>)
    requires forall i | 0 <= i < |s| :: fn.requires(s[i])
    ensures Apply(fn, multiset(s)) == multiset(Sequences.ApplyOpaque(fn, s))
    decreases s
  {
    if |s| == 0 {
      reveal_Apply();
    } else {
      var m := multiset(s);
      var x := Choose(m);
      var m' := m - multiset{x};
      var i :| 0 <= i < |s| && s[i] == x;
      var s' := s[.. i] + s[i + 1 ..];
      calc {
        Apply(fn, m);
        { reveal_Apply(); }
        multiset{fn(x)} + Apply(fn, m');
        { assert s == s[.. i] + [s[i]] + s[i + 1 ..]; }
        { assert m' == multiset(s'); }
        multiset{fn(x)} + Apply(fn, multiset(s'));
        { ApplySeq(fn, s'); }
        multiset{fn(x)} + multiset(Sequences.ApplyOpaque(fn, s'));
        { assert Sequences.ApplyOpaque(fn, s') == Sequences.ApplyOpaque(fn, s'[.. i]) + Sequences.ApplyOpaque(fn, s'[i ..]); }
        multiset(Sequences.ApplyOpaque(fn, s[.. i]) + [fn(x)] + Sequences.ApplyOpaque(fn, s[i + 1 ..]));
        { assert Sequences.ApplyOpaque(fn, s) == Sequences.ApplyOpaque(fn, s[.. i]) + [fn(x)] + Sequences.ApplyOpaque(fn, s[i + 1 ..]); }
        multiset(Sequences.ApplyOpaque(fn, s));
      }
    }
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

  lemma FoldSeqRemove<A>(zero: A, add: (A, A) -> A, s: seq<A>, i: int)
    requires 0 <= i < |s|
    requires IsIdentitySimple(add, zero);
    requires IsCommutativeSimple(add);
    requires IsAssociativeSimple(add);
    ensures Sequences.FoldFromRight(add, zero, s) ==
      add(Sequences.FoldFromRight(add, zero, s[.. i] + s[i + 1 ..]), s[i])
  {
    if |s| - 1 == i {
      assert s[.. i] + s[i + 1 ..] == s[.. i];
    } else {
      var a := s[i];
      var b := Sequences.Last(s);
      var s' := Sequences.DropLast(s);
      calc {
        Sequences.FoldFromRight(add, zero, s);
        add(Sequences.FoldFromRight(add, zero, s'), b);
        { FoldSeqRemove(zero, add, s', i); }
        add(add(Sequences.FoldFromRight(add, zero, s'[.. i] + s'[i + 1 ..]), a), b);
        { reveal_IsIdentity(); }
        { reveal_IsCommutative(); }
        { reveal_IsAssociative(); }
        add(add(Sequences.FoldFromRight(add, zero, s'[.. i] + s'[i + 1 ..]), b), a);
        { assert s[.. i] + s[i + 1 ..] == s'[.. i] + s'[i + 1 ..] + [b]; }
        add(Sequences.FoldFromRight(add, zero, s[.. i] + s[i + 1 ..]), a);
      }
    }
  }

  lemma FoldSeq<A>(zero: A, add: (A, A) -> A, s: seq<A>)
    requires IsIdentitySimple(add, zero);
    requires IsCommutativeSimple(add);
    requires IsAssociativeSimple(add);
    ensures FoldSimple(zero, add, multiset(s)) == Sequences.FoldFromRight(add, zero, s)
  {
    if |s| == 0 {
      reveal_Fold();
    } else {
      var m := multiset(s);
      var a := Choose(m);
      var m' := m - multiset{a};
      var i :| 0 <= i < |s| && s[i] == a;
      var s' := s[.. i] + s[i + 1 ..];
      calc {
        FoldSimple(zero, add, m);
        { reveal_Fold(); }
        add(a, FoldSimple(zero, add, m'));
        { reveal_IsCommutative(); }
        add(FoldSimple(zero, add, m'), a);
        { assert s == s[.. i] + [s[i]] + s[i + 1 ..]; }
        { assert m' == multiset(s'); }
        add(FoldSimple(zero, add, multiset(s')), a);
        { FoldSeq(zero, add, s'); }
        add(Sequences.FoldFromRight(add, zero, s'), a);
        { FoldSeqRemove(zero, add, s, i); }
        Sequences.FoldFromRight(add, zero, s);
      }
    }
  }

  function AddNat(x:nat, y:nat):nat { x + y }

  lemma natsumProperties()
    ensures IsCommutativeSimple<nat>(AddNat)
    ensures IsAssociativeSimple<nat>(AddNat)
    ensures IsIdentitySimple<nat>(AddNat, 0)
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
