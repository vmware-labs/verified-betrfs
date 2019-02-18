// A Map that you can query, but you can't insert/remove elements
// Iterators will be read-only maps from int -> kvpair
// This abstract module doesn't define a constructor, since the
// input to construct a Readonly_Map will naturally be
// implementation-specific.
abstract module Readonly_Map {
  type Key(!new,==)
  type Value
  type Map

  datatype Query_Result = DNE | Query_Result(value: Value)

  function Interpretation(m: Map) : map<Key, Value>

  method Is_Empty(m: Map) returns (result: bool)
    ensures result <==> Interpretation(m) == map[];

  method Defines(m: Map, key: Key) returns (result: bool)
    ensures result == (key in Interpretation(m));
      
  method Query(m: Map, key: Key) returns (result: Query_Result)
    ensures key in Interpretation(m) ==> result == Query_Result(Interpretation(m)[key]);
    ensures key !in Interpretation(m) ==> result == DNE;

  method Evaluate(m: Map, key: Key) returns (value: Value)
    requires key in Interpretation(m);
    ensures value == Interpretation(m)[key];
}

// Just add methods for creating modified versions of the given Map
abstract module Map refines Readonly_Map {

  method Empty_Map() returns (empty_map: Map)
    ensures Interpretation(empty_map) == map[];
    
  method Define(m: Map, key: Key, value: Value) returns (new_map: Map)
    ensures Interpretation(new_map) == Interpretation(m)[key := value];

  method Undefine(m: Map, key: Key) returns (new_map: Map)
    ensures Interpretation(new_map).Keys == Interpretation(m).Keys - {key};
    ensures forall key' :: key' in Interpretation(new_map)
      ==> Interpretation(new_map)[key'] == Interpretation(m)[key'];
}

// An iterator is a Readonly_Map from [0, 1, ...] to kvpairs of its underlying map
abstract module Iterator refines Readonly_Map {
  import Underlying_Map : Readonly_Map
  datatype KVPair = KVPair(key: Underlying_Map.Key, value: Underlying_Map.Value)

  type Key = int
  type Value = KVPair
  type Iterator = Map

  method Construct(m: Underlying_Map.Map) returns (iter: Iterator)
    ensures forall i :: i in Interpretation(iter).Keys <==> 0 <= i < |Underlying_Map.Interpretation(m)|;
    ensures forall k, v :: k in Underlying_Map.Interpretation(m) && Underlying_Map.Interpretation(m)[k] == v ==>
            exists i :: i in Interpretation(iter).Keys && Interpretation(iter)[i] == KVPair(k, v);
}


// Let's see if we can build one of these mofos from the builtin map

abstract module Builtin_Map refines Map {
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

  method Query(m: Map, key: Key) returns (result: Query_Result) {
    if key in m {
      result := Query_Result(m[key]);
    } else {
      result := DNE;
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
  import Underlying_Map = Builtin_Map
  type Map = seq<KVPair>

  function Interpretation(m: Map) : map<Key, Value> {
    map i: int | 0 <= i < |m| :: m[i]
  }

  method Is_Empty(m: Map) returns (result: bool) {
    assert |m| > 0 ==> 0 in Interpretation(m).Keys; // Observe
    result := |m| == 0;
  }

  method Defines(m: Map, key: Key) returns (result: bool) {
    result := 0 <= key < |m|;
  }

  method Query(m: Map, key: Key) returns (result: Query_Result) {
    if 0 <= key < |m| {
      result := Query_Result(m[key]);
    } else {
      result := DNE;
    }
  }

  method Evaluate(m: Map, key: Key) returns (value: Value) {
    value := m[key];
  }

  function method id(x: int) : int
  { x }
  
  method Construct(m: Underlying_Map.Map) returns (iter: Iterator)
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

      forall k | k in Underlying_Map.Interpretation(m)
        ensures forall k, v :: k in Underlying_Map.Interpretation(m) && Underlying_Map.Interpretation(m)[k] == v ==>
        exists i :: i in Interpretation(iter).Keys && Interpretation(iter)[i] == KVPair(k, v);

      {
        var v := Underlying_Map.Interpretation(m);
      }
      
      // assert m == Underlying_Map.Interpretation(m);
      //assert forall i :: i in Interpretation(iter).Keys <==> 0 <= i < |iter|;
      // assert forall i :: i in Interpretation(iter) ==> Interpretation(iter)[i] == iter[i];
      
      // assert Interpretation(iter) == Interpretation(tail)[|tail| := KVPair(k, v)];
      // assert |tail| !in Interpretation(tail);
      // assert iter[|iter|-1] == KVPair(k, v);
      
      assert m_without_key.Keys == m.Keys - {key}; // Observe?
      assert |m_without_key.Keys| == |m.Keys|-1; // Observe?
    }
  }
}
















// abstract module Mutable_Map {

//   type Key(==)
//   type Value

//   datatype QueryResult = DNE | QueryResult(Value)
  
//   trait Map {
//     function method Interpretation() : map<Key, Value>
//       reads this;

//     method Define(key: Key, value: Value)
//       ensures Interpretation() == old(this.Interpretation())[key := value];
//       modifies this;
        
//     method Undefine(key: Key)
//       ensures Interpretation().Keys == old(this.Interpretation().Keys) - {key};
//       ensures forall key' :: key' in Interpretation() ==> Interpretation()[key'] == old(this.Interpretation())[key'];
//       modifies this;
          
//      method Query(key: Key)
//       returns (result: QueryResult)
//       ensures key in Interpretation() ==> result == QueryResult(Interpretation()[key]);
//       ensures key !in Interpretation() ==> result == DNE;
//   }

//   class BuiltinMap extends Map {
//     var contents: map<Key, Value>

//     function method Interpretation() : map<Key, Value>
//       reads this;
//     {
//       contents
//     }

//     method Define(key: Key, value: Value)
//       ensures Interpretation() == old(this.Interpretation())[key := value];
//       modifies this;
//     {
//       contents := contents[key := value];
//     }
    
//     method Undefine(key: Key)
//       ensures Interpretation().Keys == old(this.Interpretation().Keys) - {key};
//       ensures forall key' :: key' in Interpretation() ==> Interpretation()[key'] == old(this.Interpretation())[key'];
//       modifies this;
//     {
//       contents := map key' : Key | key' in contents && key' != key :: contents[key'];
//     }

//     // I don't know why this won't compile.  Seems like a dafny bug to me...
//     method Query(key: Key)
//       returns (result: QueryResult)
//       ensures key in Interpretation() ==> result == QueryResult(Interpretation()[key]);
//       ensures key !in Interpretation() ==> result == DNE;
//     {
//       if key in contents {
//         result := QueryResult(contents[key]);
//       } else {
//         result := DNE;
//       }
//     }
//   }
// }
