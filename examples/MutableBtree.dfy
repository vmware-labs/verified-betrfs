include "../lib/NativeTypes.dfy"
include "../lib/total_order.dfy"
include "../lib/sequences.dfy"
include "../lib/Arrays.dfy"
include "../lib/Maps.dfy"

abstract module MutableBtree {
  import opened NativeTypes
  import opened Sequences
  import opened Maps
  import Arrays
  import Keys : Total_Order

  type Key = Keys.Element
  type Value

  function method MaxKeysPerLeaf() : uint64
  function method MinKeysPerLeaf() : uint64

  function method MaxChildren() : uint64
  function method MinChildren() : uint64

  function method DefaultValue<Value>() : Value
  function method DefaultKey() : Key

  trait Node {
    ghost var myFields: set<object>

    predicate WF()
      reads this, myFields

    function Interpretation() : map<Key, Value>
      requires WF()
      reads this, myFields
  }
    
  class Leaf extends Node {
    var nkeys : uint64
    var keys: array<Key>
    var values: array<Value>

    predicate WF()
      reads this, myFields
    {
      && keys in myFields
      && values in myFields
      && keys != values
      && keys.Length == MaxKeysPerLeaf() as int
      && values.Length == MaxKeysPerLeaf() as int
      && 0 <= nkeys <= keys.Length as uint64
      && Keys.IsStrictlySorted(keys[..nkeys])
    }
    
    function Interpretation() : map<Key, Value>
      requires WF()
      reads this, myFields
    {
      map k | (k in multiset(keys[..nkeys])) :: values[IndexOf(keys[..nkeys], k)]
    }
    
    method Query(needle: Key) returns (value: Value)
      requires WF()
      ensures WF()
      ensures needle in Interpretation() ==> value == Interpretation()[needle]
      ensures needle !in Interpretation() ==> value == DefaultValue()
    {
      Keys.reveal_IsStrictlySorted();
      var pos: int := Keys.InsertionPoint(keys[..nkeys], needle);
      if pos as uint64 < nkeys && keys[pos] == needle {
        value := values[pos];
      } else {
        value := DefaultValue();
      }
    }

    method Insert(key: Key, value: Value)
      requires WF()
      requires nkeys < MaxKeysPerLeaf()
      ensures WF()
      ensures Interpretation() == old(Interpretation())[key := value]
      modifies this, myFields
    {
      Keys.reveal_IsStrictlySorted();
      var pos': int := Keys.InsertionPoint(keys[..nkeys], key);
      var pos := pos' as uint64;
      assert 0 <= pos <= nkeys;

      if pos < nkeys && keys[pos] == key {
        values[pos] := value;
      } else {
        Arrays.Insert(keys, nkeys as int, key, pos');
        Arrays.Insert(values, nkeys as int, value, pos');
        nkeys := nkeys + 1;
      }
    }

    method Split() returns (right: Leaf)
      requires WF()
      ensures WF()
      ensures right.WF()
      ensures MapUnion(Interpretation(), right.Interpretation()) == old(Interpretation())
      modifies this
    {
      Keys.reveal_IsStrictlySorted();
      right := new Leaf();
      Arrays.Memcpy(right.keys, 0, keys[nkeys/2..nkeys]);
      Arrays.Memcpy(right.values, 0, values[nkeys/2..nkeys]);
      right.nkeys := nkeys - nkeys/2;
      nkeys := nkeys/2;
      assert forall key1, key2 :: key1 in Interpretation() && key2 in right.Interpretation() ==> Keys.lt(key1, key2); // OBSERVE
    }
      
    constructor ()
      ensures WF()
      ensures Interpretation() == map[]
      ensures fresh(keys)
      ensures fresh(values)
    {
      nkeys := 0;
      keys := new Key[MaxKeysPerLeaf()](_ => DefaultKey());
      values := new Value[MaxKeysPerLeaf()](_ => DefaultValue());
      myFields := {keys, values};
    }
  }
}
