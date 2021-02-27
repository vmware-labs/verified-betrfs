// Copyright 2018-2021 VMware, Inc.
// SPDX-License-Identifier: MIT

include "map.i.dfy"
include "total_order.i.dfy"
  
abstract module Ordered_Map refines Map {
  import Key_Space : Total_Order
  type Key = Key_Space.Element

  // Return a map containing just the entries with keys in the interval [begin, end].
  // If you don't want begin or end in the result, just Undefine them from the result.
  method Subrange(m: Map, begin: Key, end: Key) returns (submap: Map)
    ensures Interpretation(submap).Keys ==
      set k | k in Interpretation(m).Keys && Key_Space.lte(begin, k) && Key_Space.lte(k, end);
    ensures forall k :: k in Interpretation(submap) ==> Interpretation(submap)[k] == Interpretation(m)[k];
    
  method FirstKey(m: Map) returns (key: Key)
    requires !IsEmpty(m);
    ensures key in Interpretation(m);
    ensures forall k :: k in Interpretation(m) ==> Key_Space.lte(key, k);

  method LastKey(m: Map) returns (key: Key)
    requires !IsEmpty(m);
    ensures key in Interpretation(m);
    ensures forall k :: k in Interpretation(m) ==> Key_Space.lte(k, key);
}

// Here's a model of the above abstraction, just to show it can be done.
abstract module Sorted_Sequence_Map refines Ordered_Map {
  datatype KVPair = KVPair(key: Key, value: Value)
  type Map = s : seq<KVPair> | forall i, j :: 0 <= i < j <= |s|-1 ==> Key_Space.lt(s[i].key, s[j].key)

  function method {:opaque} Interpretation(m: Map) : map<Key, Value>
    ensures forall k :: k in Interpretation(m) <==> exists i :: 0 <= i < |m| && k == m[i].key;
    ensures forall i :: 0 <= i < |m| ==> Interpretation(m)[m[i].key] == m[i].value;
    ensures Interpretation(m) == map[] <==> m == [];
  {
    if |m| == 0 then map[]
    else
      var s := Interpretation(m[1..]);
      assert forall i :: 0 < i < |m| ==> Key_Space.lt(m[0].key, m[i].key); // Observe
      var t := s[m[0].key := m[0].value];
      t
  }

  method EmptyMap() returns (empty_map: Map) {
    empty_map := [];
  }

  method Define(m: Map, key: Key, value: Value) returns (new_map: Map) {
    reveal_Interpretation();
    if |m| == 0 {
      new_map := [KVPair(key, value)];
    } else if Key_Space.lt(key, m[0].key) {
      new_map := [KVPair(key, value)] + m;
    } else if key == m[0].key {
      new_map := [KVPair(key, value)] + m[1..];
    } else {
      var tail := Define(m[1..], key, value);
      new_map := [m[0]] + tail;
    }
  }

  method Undefine(m: Map, key: Key) returns (new_map: Map) {
    reveal_Interpretation();
    if |m| == 0 {
      new_map := m;
    } else if Key_Space.lt(key, m[0].key) {
      assert forall i :: 0 < i < |m| ==> Key_Space.lt(m[0].key, m[i].key); // Observe
      new_map := m;
    } else if key == m[0].key {
      new_map := m[1..];
    } else {
      var tail := Undefine(m[1..], key);
      new_map := [m[0]] + tail;
    }
  }

  method Defines(m: Map, key: Key) returns (result: bool) {
    if |m| == 0 {
      result := false;
    } else if key == m[0].key {
      result := true;
    } else {
      result := Defines(m[1..], key);
    }
  }
  
  predicate method IsEmpty(m: Map) {
    m == []
  }
  
  method Query(m: Map, key: Key) returns (result: QueryResult) {
    if |m| == 0 {
      result := DNE;
    } else if key == m[0].key {
      result := QueryResult(m[0].value);
    } else {
      result := Query(m[1..], key);
    }
  }

  method Evaluate(m: Map, key: Key) returns (value: Value) {
    var t := Query(m, key);
    value := t.value;
  }

  method Subrange(m: Map, begin: Key, end: Key) returns (submap: Map) {
    reveal_Interpretation();
    if |m| == 0 {
      submap := m;
    } else if Key_Space.lt(m[0].key, begin) {
      submap := Subrange(m[1..], begin, end);
    } else if Key_Space.lt(end, m[|m|-1].key) {
      assert forall i :: 0 <= i < |m|-1 ==> Key_Space.lt(m[i].key, m[|m|-1].key); // Observe
      submap := Subrange(m[..|m|-1], begin, end);
    } else {
      assert forall i :: 0 < i < |m| ==> Key_Space.lt(m[0].key, m[i].key); // Observe
      assert forall i :: 0 <= i < |m|-1 ==> Key_Space.lt(m[i].key, m[|m|-1].key); // Observe
      submap := m;
    }
  }
  
  method AKey(m: Map) returns (key: Key) {
    key := m[0].key;
  }

  method FirstKey(m: Map) returns (key: Key) {
    assert forall i :: 0 < i < |m| ==> Key_Space.lt(m[0].key, m[i].key); // Observe
    key := m[0].key;
  }

  method LastKey(m: Map) returns (key: Key) {
    assert forall i :: 0 <= i < |m|-1 ==> Key_Space.lt(m[i].key, m[|m|-1].key); // Observe
    key := m[|m|-1].key;
  }

}

// Example instantiation
module Sorted_Sequence_Integer_Integer_Map refines Sorted_Sequence_Map {
  import Key_Space = Integer_Order
  type Value = int
}

method Main() {
  var m := Sorted_Sequence_Integer_Integer_Map.EmptyMap();
  m := Sorted_Sequence_Integer_Integer_Map.Define(m, 7, 49);
  m := Sorted_Sequence_Integer_Integer_Map.Define(m, 3, 9);
  m := Sorted_Sequence_Integer_Integer_Map.Define(m, 12, 144);
  m := Sorted_Sequence_Integer_Integer_Map.Define(m, -6, 36);

  var iter := Sorted_Sequence_Integer_Integer_Map.Subrange(m, 0, 12);
  while !Sorted_Sequence_Integer_Integer_Map.IsEmpty(iter)
    decreases |Sorted_Sequence_Integer_Integer_Map.Interpretation(iter).Keys|
  {
    var k := Sorted_Sequence_Integer_Integer_Map.FirstKey(iter);
    var v := Sorted_Sequence_Integer_Integer_Map.Evaluate(iter, k);
    print k, " ", v, "\n";
    iter := Sorted_Sequence_Integer_Integer_Map.Undefine(iter, k);
  }
}
