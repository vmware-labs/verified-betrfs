include "NativeTypes.s.dfy"

module Sets {
  import opened NativeTypes 

  lemma {:opaque} SetInclusionImpliesSmallerCardinality(a: set<uint64>, b: set<uint64>)
    requires a <= b
    ensures |a| <= |b|
  {
    assert b == a + (b - a);
  }

  lemma {:opaque} SetInclusionAndEqualCardinalityImpliesSetEquality(a: set<uint64>, b: set<uint64>)
    requires a <= b
    requires |a| == |b|
    ensures a == b
  {
    assert b == a + (b - a);
  }

  // NOTE: these are horribly slow

  method SetToSeq<T(==)>(s: set<T>) returns (run: seq<T>)
  ensures |run| == |s|
  ensures (set e | e in run) == s
  {
    if |s| == 0 {
      return [];
    } else {
      var x :| x in s;
      var lset := set t | t in s && t != x;
      var l := SetToSeq(lset);
      run := l + [x];

      assert lset !! {x};
      assert lset + {x} == s;

      assert |run| == |l| + 1
        == |lset| + |{x}|
        == |lset + {x}|
        == |s|;
    }
  }

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

  method maximumInt(s: set<int>) returns (o: int)
  requires |s| >= 1
  ensures forall t : int :: t in s ==> o >= t
  {
    var y :| y in s;
    if (|s| > 1) {
      var m := maximumInt(s - {y});

      assert forall t : int :: t in (s - {y}) ==> m >= t;
      o := (if y > m then y else m);
      assert forall t : int :: t in (s - {y}) ==> o >= t;
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
