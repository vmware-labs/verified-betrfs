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
    ghost var subtreeObjects: set<object>
      
    predicate WF()
      reads this, subtreeObjects
      decreases subtreeObjects
      
    function Interpretation() : map<Key, Value>
      requires WF()
      reads this, subtreeObjects
      decreases subtreeObjects

    method Query(needle: Key) returns (value: Value)
      requires WF()
      ensures WF()
      ensures Interpretation() == old(Interpretation())
      ensures needle in Interpretation() ==> value == Interpretation()[needle]
      ensures needle !in Interpretation() ==> value == DefaultValue()
      decreases subtreeObjects
  }
    
  class Leaf extends Node {
    var nkeys : uint64
    var keys: array<Key>
    var values: array<Value>

    predicate WF()
      reads this, subtreeObjects
      decreases subtreeObjects
    {
      && subtreeObjects == {this, keys, values}
      && keys != values
      && keys.Length == MaxKeysPerLeaf() as int
      && values.Length == MaxKeysPerLeaf() as int
      && 0 <= nkeys <= keys.Length as uint64
      && Keys.IsStrictlySorted(keys[..nkeys])
    }
    
    function Interpretation() : map<Key, Value>
      requires WF()
      reads this, subtreeObjects
      decreases subtreeObjects
    {
      map k | (k in multiset(keys[..nkeys])) :: values[IndexOf(keys[..nkeys], k)]
    }
    
    method Query(needle: Key) returns (value: Value)
      requires WF()
      ensures WF()
      ensures Interpretation() == old(Interpretation())
      ensures needle in Interpretation() ==> value == Interpretation()[needle]
      ensures needle !in Interpretation() ==> value == DefaultValue()
      decreases subtreeObjects
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
      modifies this, subtreeObjects
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
      assert Interpretation().Keys + right.Interpretation().Keys <= old(Interpretation().Keys);
      assert Interpretation().Keys + right.Interpretation().Keys >= old(Interpretation().Keys);
      assert forall k :: k in Interpretation() ==> Interpretation()[k] == old(Interpretation()[k]);
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
      subtreeObjects := {this, keys, values};
    }
  }

  class Index extends Node {
    var nchildren: uint64
    var pivots: array<Key>
    var children: array<Node?>

    predicate WF()
      reads this, subtreeObjects
      decreases subtreeObjects
    {
      && {this, pivots, children} <= subtreeObjects
      && pivots != children
      && pivots.Length == (MaxChildren() as int) - 1
      && children.Length == MaxChildren() as int
      && 1 <= nchildren <= MaxChildren()
      && Keys.IsStrictlySorted(pivots[..nchildren-1])
      && (forall i :: 0 <= i < nchildren ==> children[i] != null)
      && (forall i :: 0 <= i < nchildren ==> children[i] in subtreeObjects)
      && (forall i :: 0 <= i < nchildren ==> children[i].subtreeObjects < subtreeObjects)
      && (forall i :: 0 <= i < nchildren ==> children[i].WF())
    }

    function Interpretation'(len: int) : map<Key, Value>
      requires WF()
      requires 0 < len <= nchildren as int
      reads subtreeObjects
      decreases subtreeObjects, len
    {
      if len == 1 then
        children[0].Interpretation()
      else
        MapUnion(MapIRestrict(Interpretation'(len-1),           iset k | Keys.lt(k, pivots[len-2])),
                 MapIRestrict(children[len-1].Interpretation(), iset k | Keys.lte(pivots[len-2], k)))
    }
    
    function Interpretation() : map<Key, Value>
      requires WF()
      reads this, subtreeObjects
    {
      Interpretation'(nchildren as int)
    }

    method Query(needle: Key) returns (value: Value)
      requires WF()
      ensures WF()
      ensures Interpretation() == old(Interpretation())
      ensures needle in Interpretation() ==> value == Interpretation()[needle]
      ensures needle !in Interpretation() ==> value == DefaultValue()
      decreases subtreeObjects
    {
      Keys.reveal_IsStrictlySorted();
      var pos' := Keys.InsertionPoint(pivots[..nchildren-1], needle);
      var pos := pos' as uint64;
      if pos == nchildren-1 {
        value := children[nchildren-1].Query(needle);
      } else if needle == pivots[pos] {
        value := children[pos+1].Query(needle);
      } else {
        value := children[pos].Query(needle);
      }
    }
  }
}
