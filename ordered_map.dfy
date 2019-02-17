include "map.dfy"
include "total_order.dfy"
  
abstract module Ordered_Map refines Map {
  import Key_Space : Total_Order
  type Key = Key_Space.Element

  datatype OrderedQueryResult = NoMoreElements | OrderedQueryResult(key: Key)
    
  method Successor(m: Map, key: Key) returns (result: OrderedQueryResult)
    ensures result.NoMoreElements?
      ==> (forall k :: k in Interpretation(m) ==> Key_Space.lte(k, key));
    ensures result.OrderedQueryResult?
      ==> (result.key in Interpretation(m) &&
           Key_Space.lt(key, result.key) &&
           (forall k :: Key_Space.lt(key, k) && Key_Space.lt(k, result.key) ==> k !in Interpretation(m)));

  method Predecessor(m: Map, key: Key) returns (result: OrderedQueryResult)
    ensures result.NoMoreElements?
      ==> (forall k :: k in Interpretation(m) ==> Key_Space.lte(key, k));
    ensures result.OrderedQueryResult?
      ==> (result.key in Interpretation(m) &&
           Key_Space.lt(result.key, key) &&
           (forall k :: Key_Space.lt(result.key, k) && Key_Space.lt(k, key) ==> k !in Interpretation(m)));
}

// Here's a model of the above abstraction, just to show it can be done.
abstract module Sorted_Sequence_Map refines Ordered_Map {
  datatype KVPair = KVPair(key: Key, value: Value)
  type Map = s : seq<KVPair> | forall i, j :: 0 <= i < j <= |s|-1 ==> Key_Space.lt(s[i].key, s[j].key)

  function method {:opaque} Interpretation(m: Map) : map<Key, Value>
    ensures forall k :: k in Interpretation(m) <==> exists i :: 0 <= i < |m| && k == m[i].key;
  {
    if |m| == 0 then map[]
    else Interpretation(m[1..])[m[0].key := m[0].value]
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

  method Query(m: Map, key: Key) returns (result: QueryResult) {
    reveal_Interpretation();
    if |m| == 0 {
      result := DNE;
    } else if key == m[0].key {
      result := QueryResult(m[0].value);
    } else {
      result := Query(m[1..], key);
    }
  }

  method Successor(m: Map, key: Key) returns (result: OrderedQueryResult) {
    if |m| == 0 {
      result := NoMoreElements;
    } else if Key_Space.lt(key, m[0].key) {
      assert forall i :: 0 < i < |m| ==> Key_Space.lt(m[0].key, m[i].key); // Observe
      result := OrderedQueryResult(m[0].key);
    } else {
      result := Successor(m[1..], key);
    }
  }

  method Predecessor(m: Map, key: Key) returns (result: OrderedQueryResult) {
    if |m| == 0 {
      result := NoMoreElements;
    } else if Key_Space.lt(m[|m|-1].key, key) {
      assert forall i :: 0 <= i < |m|-1 ==> Key_Space.lt(m[i].key, m[|m|-1].key); // Observe
      result := OrderedQueryResult(m[|m|-1].key);
    } else {
      result := Predecessor(m[..|m|-1], key);
    }
  }
}

// Example instantiation
module Sorted_Sequence_Integer_Integer_Map refines Sorted_Sequence_Map {
  import Key_Space = Integer_Order
  type Value = int
}
