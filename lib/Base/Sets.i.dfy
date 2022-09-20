// Copyright 2018-2021 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, and University of Washington
// SPDX-License-Identifier: BSD-2-Clause

module Sets {

  lemma ProperSubsetImpliesSmallerCardinality<T>(a: set<T>, b: set<T>)
    requires a < b
    ensures |a| < |b|
  {
    assert |b| == |a| + |b-a|;
  }

  lemma SetInclusionImpliesSmallerCardinality<T>(a: set<T>, b: set<T>)
    requires a <= b
    ensures |a| <= |b|
  {
    assert b == a + (b - a);
  }

  lemma SetInclusionImpliesStrictlySmallerCardinality<T>(a: set<T>, b: set<T>)
    requires a < b
    ensures |a| < |b|
  {
    assert b == a + (b - a);
  }

  lemma SetInclusionAndEqualCardinalityImpliesSetEquality<T>(a: set<T>, b: set<T>)
    requires a <= b
    requires |a| == |b|
    ensures a == b
  {
    assert b == a + (b - a);
  }

  function SetRange(n: int) : set<int>
  {
    set i | 0 <= i < n
  }

  lemma CardinalitySetRange(n: int)
  requires n >= 0
  ensures |SetRange(n)| == n
  {
    if n == 0 {
    } else {
      CardinalitySetRange(n-1);
      assert SetRange(n)
          == SetRange(n-1) + {n-1};
    }
  }

  lemma SubSetExtensionality<T>(a: set<T>, b: set<T>)
    requires forall x | x in a :: x in b
    ensures a <= b
  {

  }

  function SetMax(a:set<int>) : (out: int) 
    requires 0 < |a|
    ensures forall e | e in a :: e <= out
    ensures out in a
  {
    var e :| e in a;
    if |a| == 1 then 
      assert forall x | x in a :: x <= e by
      {
        forall y | y in a ensures y == e 
        {
          if y != e {
            SetInclusionImpliesSmallerCardinality({y, e}, a);
            assert false;
          }
        }
      }
      e 
    else
      var rest := SetMax(a-{e});
      var out := if e < rest then rest else e;
      assert forall x | x in a :: x <= out by
      {
        forall x | x in a ensures x <= out
        {
          if x != e {
            assert x in a - {e};  // trigger
          }
        }
      }
      out
  }

  function UnionSeqOfSets<T>(s : seq<set<T>>) : (out: set<T>)
    ensures forall i | 0 <= i < |s| :: s[i] <= out
  {
    if |s| == 0 then {}
    else s[0] + UnionSeqOfSets(s[1..])
  }

  lemma UnionSeqOfSetsSoundness<T>(s : seq<set<T>>)
    ensures forall e | e in UnionSeqOfSets(s) ::
      exists i :: 0 <= i < |s| && e in s[i]
    decreases |s|
  {
    if 0 < |s| {
      UnionSeqOfSetsSoundness(s[1..]);
    }
  }

  lemma SetSeqMath<T>(s: seq<set<T>>, s': seq<set<T>>, idx: nat, add:set<T>, sub:set<T>)
    requires 0 < |s|
    requires |s| == |s'|
    requires 0 <= idx < |s|
    requires forall i | 
                && 0 <= i < |s| 
                && i != idx 
              :: s[i] == s'[i]
                && s[i] !! sub
    requires s'[idx] == s[idx] + add - sub
    // Framing
    requires sub !! add
    ensures UnionSeqOfSets(s') == UnionSeqOfSets(s) + add - sub
  {
    UnionSeqOfSetsSoundness(s);
    UnionSeqOfSetsSoundness(s');
  }

  lemma SetSeqMath2<T>(s: seq<set<T>>, s': seq<set<T>>, pivot: nat, add:set<T>, sub:set<T>)
    requires 0 < |s|
    requires |s| + 1 == |s'|
    requires 0 <= pivot < |s|
    requires forall i | 0 <= i < pivot
              :: && s[i] == s'[i]
                 && s[i] !! sub
    requires forall i | pivot + 1 < i < |s'|
              :: && s[i-1] == s'[i]
                 && s[i-1] !! sub
    requires s'[pivot] + s'[pivot+1] == s[pivot] + add - sub
    // Framing
    requires sub !! add
    ensures UnionSeqOfSets(s') == UnionSeqOfSets(s) + add - sub
  {
    UnionSeqOfSetsSoundness(s);
    UnionSeqOfSetsSoundness(s');
    forall x | x in UnionSeqOfSets(s) + add - sub
    ensures x in UnionSeqOfSets(s') 
    {
      if x in add {
        assert x in s'[pivot] + s'[pivot+1];  // trigger
      } else {
        var idx :| 0 <= idx < |s| && x in s[idx];
        if idx < pivot {
          assert x in UnionSeqOfSets(s');
        } else if idx == pivot {
          assert x in s'[pivot] + s'[pivot+1];  // trigger
        } else {
          assert x in s'[idx+1];  // trigger
        }
      }
    }
  }
}
