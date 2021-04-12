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
}
