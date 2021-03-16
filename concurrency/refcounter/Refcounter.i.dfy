// Copyright 2018-2021 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, and University of Washington
// SPDX-License-Identifier: BSD-2-Clause

include "ResourceBuilderSpec.s.dfy"
include "Multisets.i.dfy"

module Refcounter refines ResourceBuilderSpec {
  import opened Multisets

  datatype Q = Refcount(v: V, count: int)

  predicate from_exc(a: multiset<R>, b: multiset<R>, v: V)
  {
    && a == multiset{Exc(v)}
    && b == multiset{Internal(Refcount(v, 0))}
  }

  predicate to_exc(a: multiset<R>, b: multiset<R>, v: V)
  {
    && a == multiset{Internal(Refcount(v, 0))}
    && b == multiset{Exc(v)}
  }

  predicate to_const(a: multiset<R>, b: multiset<R>, v: V, r: int)
  {
    && a == multiset{Internal(Refcount(v, r))}
    && b == multiset{Internal(Refcount(v, r+1)), Const(v)}
  }

  predicate from_const(a: multiset<R>, b: multiset<R>, v: V, r: int)
  {
    && a == multiset{Internal(Refcount(v, r)), Const(v)}
    && b == multiset{Internal(Refcount(v, r-1))}
  }

  predicate transform(a: multiset<R>, b: multiset<R>)
  {
    || (exists v :: from_exc(a, b, v))
    || (exists v :: to_exc(a, b, v))
    || (exists v, r :: from_const(a, b, v, r))
    || (exists v, r :: to_const(a, b, v, r))
  }

  predicate is_exc_or_refcount(r: R, v: V)
  {
    r == Exc(v) || (r.Internal? && r.q.v == v)
  }

  predicate is_const(r: R, v: V)
  {
    r == Const(v)
  }

  function refcount_of(r: R, v: V) : int
  {
    if r.Internal? && r.q.v == v then r.q.count else 0
  }

  predicate InvV(s: Variables, v: V)
  {
    var savedCount := Count((v0: V) => v0 == v, s.saved);
    var qCount := Count((r) => is_exc_or_refcount(r, v), s.m);
    var refSum := Sum((r) => refcount_of(r, v), s.m);
    var constCount := Count((r) => is_const(r, v), s.m);

    && savedCount == qCount
    && refSum == constCount
  }

  predicate Inv(s: Variables)
  {
    forall v: V :: InvV(s, v)
  }

  lemma forall_CountReduce<A>()
  ensures forall fn: A->bool, a, b {:trigger Count<A>(fn, a + b) }
    :: Count<A>(fn, a + b) == Count<A>(fn, a) + Count<A>(fn, b)
  ensures forall fn: A->bool, a {:trigger Count<A>(fn, multiset{a}) }
    :: Count<A>(fn, multiset{a}) == (if fn(a) then 1 else 0)
  ensures forall fn: A->bool, a, b {:trigger Count<A>(fn, multiset{a,b}) }
    :: Count<A>(fn, multiset{a,b}) ==
        (if fn(a) then 1 else 0) + (if fn(b) then 1 else 0)

  lemma forall_SumReduce<A>()
  ensures forall fn: A->int, a, b {:trigger Sum<A>(fn, a + b) }
    :: Sum<A>(fn, a + b) == Sum<A>(fn, a) + Sum<A>(fn, b)
  ensures forall fn: A->int, a {:trigger Sum<A>(fn, multiset{a}) }
    :: Sum<A>(fn, multiset{a}) == fn(a)
  ensures forall fn: A->int, a, b {:trigger Sum<A>(fn, multiset{a,b}) }
    :: Sum<A>(fn, multiset{a,b}) == fn(a) + fn(b)

  lemma NewExcPreservesInvV(s: Variables, s': Variables, v: V)
  requires NewExc(s, s')
  ensures
    var savedCount := Count((v0: V) => v0 == v, s.saved);
    var qCount := Count((r) => is_exc_or_refcount(r, v), s.m);
    var refSum := Sum((r) => refcount_of(r, v), s.m);
    var constCount := Count((r) => is_const(r, v), s.m);

    var savedCount' := Count((v0: V) => v0 == v, s'.saved);
    var qCount' := Count((r) => is_exc_or_refcount(r, v), s'.m);
    var refSum' := Sum((r) => refcount_of(r, v), s'.m);
    var constCount' := Count((r) => is_const(r, v), s'.m);

    && refSum == refSum'
    && constCount == constCount'
    && savedCount + qCount' == savedCount' + qCount
  {
    forall_SumReduce<R>();
    forall_CountReduce<R>();
    forall_CountReduce<V>();
  }
  /*{
    var savedCount := Count((v0: V) => v0 == v, s.saved);
    var qCount := Count((r) => is_exc_or_refcount(r, v), s.m);
    var refSum := Sum((r) => refcount_of(r, v), s.m);
    var constCount := Count((r) => is_const(r, v), s.m);

    var savedCount' := Count((v0: V) => v0 == v, s'.saved);
    var qCount' := Count((r) => is_exc_or_refcount(r, v), s'.m);
    var refSum' := Sum((r) => refcount_of(r, v), s'.m);
    var constCount' := Count((r) => is_const(r, v), s'.m);

    var v1 :|
      && s'.saved == s.saved + multiset{v1}
      && s'.m == s.m + multiset{Exc(v1)};

    calc {
      refSum;
      {
        SumMultiset1((r) => refcount_of(r, v), Exc(v1));
        assert Sum((r) => refcount_of(r, v), multiset{Exc(v1)}) == 0;
      }
      Sum((r) => refcount_of(r, v), s.m)
          + Sum((r) => refcount_of(r, v), multiset{Exc(v1)});
      {
        SumAdditive((r) => refcount_of(r, v), s.m, multiset{Exc(v1)});
      }
      Sum((r) => refcount_of(r, v), s.m + multiset{Exc(v1)});
      Sum((r) => refcount_of(r, v), s'.m);
      refSum';
    }
    calc {
      constCount;
      Count((r) => is_const(r, v), s.m);
      {
        CountMultiset1((r) => is_const(r, v), Exc(v1));
        assert Count((r) => is_const(r, v), multiset{Exc(v1)}) == 0;
      }
      Count((r) => is_const(r, v), s.m) +
           Count((r) => is_const(r, v), multiset{Exc(v1)});
      {
        CountAdditive((r) => is_const(r, v), s.m, multiset{Exc(v1)});
      }
      Count((r) => is_const(r, v), s.m + multiset{Exc(v1)});
      Count((r) => is_const(r, v), s'.m);
      constCount';
    }
    calc {
      savedCount + qCount';
      Count((v0: V) => v0 == v, s.saved)
          + Count((r) => is_exc_or_refcount(r, v), s'.m);

      {
        CountAdditive((r) => is_exc_or_refcount(r, v), s.m,
            multiset{Exc(v1)});
      }

      Count((v0: V) => v0 == v, s.saved)
          + Count((r) => is_exc_or_refcount(r, v), s.m)
          + Count((r) => is_exc_or_refcount(r, v), multiset{Exc(v1)});

      {
        CountMultiset1((r) => is_exc_or_refcount(r, v), Exc(v1));
        CountMultiset1((v0: V) => v0 == v, v1);
        assert Count((r) => is_exc_or_refcount(r, v), multiset{Exc(v1)})
            == Count((v0: V) => v0 == v, multiset{v1});
      }

      Count((v0: V) => v0 == v, s.saved)
          + Count((v0: V) => v0 == v, multiset{v1})
          + Count((r) => is_exc_or_refcount(r, v), s.m);

      {
        CountAdditive((v0: V) => v0 == v, s.saved,
            multiset{v1});
      }

      Count((v0: V) => v0 == v, s'.saved)
          + Count((r) => is_exc_or_refcount(r, v), s.m);
      savedCount' + qCount;
    }
  }*/

  lemma NewExcPreservesInv(s: Variables, s': Variables)
  requires Inv(s)
  requires NewExc(s, s')
  ensures Inv(s')
  {
    forall v
    ensures InvV(s', v)
    {
      assert InvV(s, v);
      NewExcPreservesInvV(s, s', v);
    }
  }

  lemma NewExcPreservesInvReverse(s: Variables, s': Variables)
  requires Inv(s)
  requires NewExc(s', s)
  ensures Inv(s')
  {
    forall v
    ensures InvV(s', v)
    {
      assert InvV(s, v);
      NewExcPreservesInvV(s', s, v);
    }

  }

  lemma InternalStepPreservesInv(s: Variables, s': Variables)
  requires Inv(s)
  requires InternalStep(s, s')
  ensures Inv(s')
  {
    forall v
    ensures InvV(s', v)
    {
      assert InvV(s, v);
      forall_SumReduce<R>();
      forall_CountReduce<R>();
      forall_CountReduce<V>();
    }
  }

  lemma NextPreservesInv(s: Variables, s': Variables)
  //requires Inv(s)
  //requires Next(s, s')
  //ensures Inv(s')
  {
    if NewExc(s, s') {
      NewExcPreservesInv(s, s');
    }
    else if NewExc(s', s) {
      NewExcPreservesInvReverse(s, s');
    }
    else if InternalStep(s, s') {
      InternalStepPreservesInv(s, s');
    }
  }

  lemma InvWorksConst(s: Variables, v: V)
  //requires Inv(s)
  //requires Const(v) in s.m
  //ensures v in s.saved
  {
    var savedCount := Count((v0: V) => v0 == v, s.saved);
    var qCount := Count((r) => is_exc_or_refcount(r, v), s.m);
    var refSum := Sum((r) => refcount_of(r, v), s.m);
    var constCount := Count((r) => is_const(r, v), s.m);

    assert InvV(s, v);

    assert constCount >= 1 by { Count_ge_1((r) => is_const(r, v), s.m, Const(v)); }
    assert refSum >= 1;

    var rc_obj := get_nonzero_elem((r) => refcount_of(r, v), s.m);

    assert qCount >= 1 by {
      Count_ge_1((r) => is_exc_or_refcount(r, v), s.m, rc_obj);
    }
    assert savedCount >= 1;

    assert v in s.saved by {
      var v1 := get_true_elem((v0: V) => v0 == v, s.saved);
      assert v == v1;
    }
  }

  lemma InvWorksExc(s: Variables, v: V)
  //requires Inv(s)
  //requires Exc(v) in s.m
  //ensures v in s.saved
  {
    var savedCount := Count((v0: V) => v0 == v, s.saved);
    var qCount := Count((r) => is_exc_or_refcount(r, v), s.m);
    var refSum := Sum((r) => refcount_of(r, v), s.m);
    var constCount := Count((r) => is_const(r, v), s.m);

    assert InvV(s, v);

    assert qCount >= 1 by {
      Count_ge_1((r) => is_exc_or_refcount(r, v), s.m, Exc(v));
    }
    assert savedCount >= 1;

    assert v in s.saved by {
      var v1 := get_true_elem((v0: V) => v0 == v, s.saved);
      assert v == v1;
    }
  }

/*
  // EVERYTHING IS GHOST
  method client_method(linear v: V)
  returns (linear read_only_v: Reader<V>)
  {
    // m = {} , saved = {}

    linear var exc := new_exc(v);

    // m = {Exc(v)} , saved = {v}

    // transform exc into Internal(Refcount(v, 0))
    linear var rc := transform(exc, Refcount(v, 0));

    // m = {Refcount(v, 0)} , saved = {v}

    // transform Internal(Refcount(v, 0)) into
    // Internal(Refcount(v, 1)) and Const(v)
    linear var rc', readOnlyRef := transform(rc, ...)

    // m = {Refcount(v, 1), Const(v)} , saved = {v}

    transform(...)

    // m = {Refcount(v, 0)} , saved = {v}

    transform(...)

    // m = {Exc(v)} , saved = {v}



  }

*/
}
