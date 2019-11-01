include "NativeTypes.s.dfy"

module Sets {
  import opened NativeTypes 

  lemma {:opaque} SetInclusionImpliesSmallerCardinality<T>(a: set<T>, b: set<T>)
    requires a <= b
    ensures |a| <= |b|
  {
    assert b == a + (b - a);
  }

  lemma {:opaque} SetInclusionAndEqualCardinalityImpliesSetEquality<T>(a: set<T>, b: set<T>)
    requires a <= b
    requires |a| == |b|
    ensures a == b
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

  function {:opaque} maximumInt(s: set<uint64>) : (o: uint64)
  requires |s| >= 1
  {
    var y :| y in s;
    if (|s| > 1) then (
      var m := maximumInt(s - {y});
      var o := (if y > m then y else m);
      o
    ) else (
      y
    )
  }

  lemma maximumIntCorrect(s: set<uint64>)
  requires |s| >= 1
  ensures forall t : uint64 :: t in s ==> maximumInt(s) >= t

  method MaximumInt(s: set<uint64>) returns (o: uint64)
  requires |s| >= 1
  ensures o == maximumInt(s)
  {
    var y :| y in s;
    if (|s| > 1) {
      var m := MaximumInt(s - {y});
      maximumIntCorrect(s - {y});

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

      assume y == maximumInt(s);
      o := y;
    }
    assume o == maximumInt(s);
  }
}
