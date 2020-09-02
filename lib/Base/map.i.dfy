// A Map that you can query, but you can't insert/remove elements
// Iterators will be read-only maps from int -> kvpair
// This abstract module doesn't define a constructor, since the
// input to construct a Readonly_Map will naturally be
// implementation-specific.
abstract module ReadonlyMap {
  type Key(!new,==)
  type Value
  type Map

  datatype QueryResult = NotDefined | Defined(value: Value)

  function Interpretation(m: Map) : map<Key, Value>

  method IsEmpty(m: Map) returns (result: bool)
    ensures result <==> Interpretation(m) == map[];

  method Defines(m: Map, key: Key) returns (result: bool)
    ensures result == (key in Interpretation(m));
      
  method Query(m: Map, key: Key) returns (result: QueryResult)
    ensures key in Interpretation(m) ==> result == Defined(Interpretation(m)[key]);
    ensures key !in Interpretation(m) ==> result == NotDefined;

  method Evaluate(m: Map, key: Key) returns (value: Value)
    requires key in Interpretation(m);
    ensures value == Interpretation(m)[key];
}

// Just add methods for creating modified versions of the given Map
abstract module Map refines ReadonlyMap {

  method EmptyMap() returns (empty_map: Map)
    ensures Interpretation(empty_map) == map[];
    
  method Define(m: Map, key: Key, value: Value) returns (new_map: Map)
    ensures Interpretation(new_map) == Interpretation(m)[key := value];

  method Undefine(m: Map, key: Key) returns (new_map: Map)
    ensures Interpretation(new_map).Keys == Interpretation(m).Keys - {key};
    ensures forall key' :: key' in Interpretation(new_map)
      ==> Interpretation(new_map)[key'] == Interpretation(m)[key'];
}

// An iterator is a Readonly_Map from [0, 1, ...] to kvpairs of its underlying map
abstract module Iterator refines ReadonlyMap {
  import UnderlyingMap : ReadonlyMap
  datatype KVPair = KVPair(key: UnderlyingMap.Key, value: UnderlyingMap.Value)

  type Key = int
  type Value = KVPair
  type Iterator = Map

  method Construct(m: UnderlyingMap.Map) returns (iter: Iterator)
    ensures forall i :: i in Interpretation(iter).Keys <==> 0 <= i < |UnderlyingMap.Interpretation(m)|;
    ensures forall k, v :: k in UnderlyingMap.Interpretation(m) && UnderlyingMap.Interpretation(m)[k] == v ==>
            exists i :: i in Interpretation(iter).Keys && Interpretation(iter)[i] == KVPair(k, v);
}


// Let's see if we can build one of these monsters from the builtin map

abstract module BuiltinMap refines Map {
  type Map = map<Key, Value>

  function Interpretation(m: Map) : map<Key, Value> {
    m
  }

  method Is_Empty(m: Map) returns (result: bool) {
    result := |m| == 0;
  }

  method Defines(m: Map, key: Key) returns (result: bool) {
    result := key in m;
  }

  method Query(m: Map, key: Key) returns (result: QueryResult) {
    if key in m {
      result := Defined(m[key]);
    } else {
      result := NotDefined;
    }
  }

  method Evaluate(m: Map, key: Key) returns (value: Value) {
    value := m[key];
  }

  method Empty_Map() returns (empty_map: Map) {
    empty_map := map[];
  }

  method Define(m: Map, key: Key, value: Value) returns (new_map: Map) {
    new_map := m[key := value];
  }

  method Undefine(m: Map, key: Key) returns (new_map: Map) {
    new_map := map k | k in m.Keys && k != key :: m[k];
  }

}

abstract module Builtin_Map_Sequence_Iterator refines Iterator {
  import UnderlyingMap = BuiltinMap
  type Map = seq<KVPair>

  function Interpretation(m: Map) : map<Key, Value> {
    map i: int | 0 <= i < |m| :: m[i]
  }

  method IsEmpty(m: Map) returns (result: bool) {
    assert |m| > 0 ==> 0 in Interpretation(m).Keys; // Observe
    result := |m| == 0;
  }

  method Defines(m: Map, key: Key) returns (result: bool) {
    result := 0 <= key < |m|;
  }

  method Query(m: Map, key: Key) returns (result: QueryResult) {
    if 0 <= key < |m| {
      result := Defined(m[key]);
    } else {
      result := NotDefined;
    }
  }

  method Evaluate(m: Map, key: Key) returns (value: Value) {
    value := m[key];
  }

  function method id(x: int) : int
  { x }
  
  method Construct(m: UnderlyingMap.Map) returns (iter: Iterator)
    ensures |iter| == |m|;
    // ensures forall k, v :: k in m && m[k] == v ==> exists i :: 0 <= i < |iter| && iter[i] == KVPair(k, v);
  {
    if |m| == 0 {
      iter := [];
    } else {
      var key :| key in m;
      var value := m[key];
      var m_without_key := map x | x in m && x != key :: m[x];
      var tail := Construct(m_without_key);
      iter := tail + [KVPair(key, value)];

      forall k | k in UnderlyingMap.Interpretation(m)
        ensures forall k, v :: k in UnderlyingMap.Interpretation(m) && UnderlyingMap.Interpretation(m)[k] == v ==>
        exists i :: i in Interpretation(iter).Keys && Interpretation(iter)[i] == KVPair(k, v);

      {
        var v := UnderlyingMap.Interpretation(m);
      }
      
      assert m_without_key.Keys == m.Keys - {key}; // Observe?
      assert |m_without_key.Keys| == |m.Keys|-1; // Observe?
    }
  }
}
