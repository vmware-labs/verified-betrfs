include "NativeTypes.dfy"

module Sets {
  import opened NativeTypes 

  lemma {:opaque} SetInclusionImpliesSmallerCardinality(a: set<uint64>, b: set<uint64>)
    requires a <= b
    ensures |a| <= |b|
  {
    assert b == a + (b - a);
  }

  // NOTE: these are horribly slow

  method minimum(s: set<uint64>) returns (o: uint64)
  requires |s| >= 1
  ensures forall t : uint64 :: t in s ==> o <= t
  {
    var y :| y in s;
    if (|s| > 1) {
      var m := minimum(s - {y});

      assert forall t : uint64 :: t in (s - {y}) ==> m <= t;
      o := (if y < m then y else m);
      assert forall t : uint64 :: t in (s - {y}) ==> o <= t;
      assert o <= y;
    } else {
      assert |s| == 1;
      assert y in s;
      assert |s - {y}| == 0;
      assert s - {y} == {};
      assert s == {y};
      return y;
    }
  }

  method maximum(s: set<uint64>) returns (o: uint64)
  requires |s| >= 1
  ensures forall t : uint64 :: t in s ==> o >= t
  {
    var y :| y in s;
    if (|s| > 1) {
      var m := maximum(s - {y});

      assert forall t : uint64 :: t in (s - {y}) ==> m >= t;
      o := (if y > m then y else m);
      assert forall t : uint64 :: t in (s - {y}) ==> o >= t;
      assert o >= y;
    } else {
      assert |s| == 1;
      assert y in s;
      assert |s - {y}| == 0;
      assert s - {y} == {};
      assert s == {y};
      return y;
    }
  }
}
