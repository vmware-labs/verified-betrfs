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
    
  datatype QueryResult =
    | Found(value: Value)
    | NotFound
    
  function method MaxKeysPerLeaf() : uint64
    ensures 1 < MaxKeysPerLeaf()
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

    function QueryDef(needle: Key) : QueryResult
      requires WF()
      reads this, subtreeObjects
      decreases subtreeObjects
      
    function Interpretation() : map<Key, Value>
      requires WF()
      ensures forall key :: QueryDef(key).Found? ==> MapsTo(Interpretation(), key, QueryDef(key).value)
      ensures forall key :: QueryDef(key).NotFound? ==> key !in Interpretation()
      reads this, subtreeObjects
      decreases subtreeObjects

    method Query(needle: Key) returns (result: QueryResult)
      requires WF()
      ensures result == QueryDef(needle)
      //ensures Interpretation() == old(Interpretation())
      //ensures needle in Interpretation() ==> value == Interpretation()[needle]
      //ensures needle !in Interpretation() ==> value == DefaultValue()
      decreases subtreeObjects

    predicate Full()
      requires WF()
      reads this, subtreeObjects
      
    method Insert(key: Key, value: Value)
      requires WF()
      requires !Full()
      ensures WF()
      ensures Interpretation() == old(Interpretation())[key := value]
      modifies this, subtreeObjects

    static function MergeMaps(left: map<Key, Value>, pivot: Key, right: map<Key, Value>) : map<Key, Value> {
      map key |
        && key in left.Keys + right.Keys
        && (|| (Keys.lt(key, pivot) && key in left)
           || (Keys.lte(pivot, key) && key in right))
         ::
         if Keys.lt(key, pivot) && key in left then left[key]
         else right[key]
    }
    
    predicate SplitEnsures(oldint: map<Key, Value>, pivot: Key, rightnode: Node)
      reads this, subtreeObjects
      reads rightnode, rightnode.subtreeObjects
    {
      && WF()
      && !Full()
      && rightnode.WF()
      && !rightnode.Full()
      && MergeMaps(Interpretation(), pivot, rightnode.Interpretation()) == oldint
    }
      
    method Split() returns (pivot: Key, rightnode: Node)
      requires WF()
      requires Full()
      ensures SplitEnsures(old(Interpretation()), pivot, rightnode)
      modifies this
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
    
    function QueryDef(needle: Key) : (result: QueryResult)
      requires WF()
      reads subtreeObjects
    {
      var pos: int := Keys.LargestLt(keys[..nkeys], needle);
      if (pos + 1) as uint64 < nkeys && keys[pos+1] == needle then Found(values[pos+1])
      else NotFound
    }
    
    function Interpretation() : map<Key, Value>
      requires WF()
      ensures forall key :: QueryDef(key).Found? ==> MapsTo(Interpretation(), key, QueryDef(key).value)
      ensures forall key :: QueryDef(key).NotFound? ==> key !in Interpretation()
      reads this, subtreeObjects
      decreases subtreeObjects
    {
      Keys.reveal_IsStrictlySorted();
      map k | (k in multiset(keys[..nkeys])) :: values[IndexOf(keys[..nkeys], k)]
    }


    method Query(needle: Key) returns (result: QueryResult)
      requires WF()
      ensures result == QueryDef(needle)
      // ensures Interpretation() == old(Interpretation())
      // ensures needle in Interpretation() ==> value == Interpretation()[needle]
      // ensures needle !in Interpretation() ==> value == DefaultValue()
      decreases subtreeObjects
    {
      Keys.reveal_IsStrictlySorted();
      var pos: int := Keys.InsertionPoint(keys[..nkeys], needle);
      if pos as uint64 < nkeys && keys[pos] == needle {
        result := Found(values[pos]);
      } else {
        result := NotFound;
      }
    }

    predicate Full()
      requires WF()
      reads this, subtreeObjects
    {
      nkeys >= MaxKeysPerLeaf()
    }
    
    method Insert(key: Key, value: Value)
      requires WF()
      requires !Full()
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

    method Split() returns (pivot: Key, rightnode: Node)
      requires WF()
      ensures SplitEnsures(old(Interpretation()), pivot, rightnode)
      modifies this
    {
      Keys.reveal_IsStrictlySorted();
      var right := new Leaf();
      var boundary := nkeys/2;
      Arrays.Memcpy(right.keys, 0, keys[boundary..nkeys]);
      Arrays.Memcpy(right.values, 0, values[boundary..nkeys]);
      right.nkeys := nkeys - boundary;
      nkeys := boundary;
      pivot := right.keys[0];
      rightnode := right;
    }
      
    constructor ()
      ensures WF()
      ensures Interpretation() == map[]
      ensures !Full()
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

    function QueryDef(needle: Key) : QueryResult
      requires WF()
      reads this, subtreeObjects
      decreases subtreeObjects
    {
      var pos := Keys.LargestLte(pivots[..nchildren-1], needle);
      children[pos + 1].QueryDef(needle)
    }
    
    // function Interpretation'(len: int) : (result: map<Key, Value>)
    //   requires WF()
    //   requires 0 < len <= nchildren as int
    //   reads subtreeObjects
    //   decreases subtreeObjects, len
    // {
    //   if len == 1 then
    //     children[0].Interpretation()
    //   else
    //     MergeMaps(Interpretation'(len-1), pivots[len-2], children[len-1].Interpretation())
    // }
    
    function Interpretation() : (result: map<Key, Value>)
      requires WF()
      ensures forall key :: QueryDef(key).Found? ==> MapsTo(result, key, QueryDef(key).value)
      ensures forall key :: QueryDef(key).NotFound? ==> key !in Interpretation()
      reads this, subtreeObjects
      decreases subtreeObjects
    {
      // This is just to prove finiteness.  Thanks to James Wilcox for the trick:
      // https://stackoverflow.com/a/47585360
      var allkeys := set key, i | 0 <= i < nchildren && key in children[i].Interpretation() :: key;
      var result := map key |
        && key in allkeys
        && key in children[Keys.LargestLte(pivots[..nchildren-1], key) + 1].Interpretation()
        :: children[Keys.LargestLte(pivots[..nchildren-1], key) + 1].Interpretation()[key];
      
      result
      //Interpretation'(nchildren as int)
    }

    method Query(needle: Key) returns (result: QueryResult)
      requires WF()
      ensures result == QueryDef(needle)
      decreases subtreeObjects
    // {
    //   Keys.reveal_IsStrictlySorted();
    //   var pos' := Keys.InsertionPoint(pivots[..nchildren-1], needle);
    //   var pos := pos' as uint64;
    //   if pos == nchildren-1 {
    //     value := children[nchildren-1].Query(needle);
    //     assert needle in Interpretation() <==> needle in children[nchildren-1].Interpretation(); // OBSERVE
    //     assert needle in Interpretation() ==> value == Interpretation()[needle];
    //     assert needle !in Interpretation() ==> value == DefaultValue();
    //   } else if needle == pivots[pos] {
    //     value := children[pos+1].Query(needle);
    //     assert forall i :: 0 <= i < pos ==> Keys.lt(pivots[i], needle);
    //     assert needle in Interpretation() ==> needle in children[pos+1].Interpretation();
    //     assert needle in Interpretation() <== needle in children[pos+1].Interpretation();
    //     assert needle in Interpretation() ==> value == Interpretation()[needle];
    //     assert needle !in Interpretation() ==> value == DefaultValue();
    //   } else {
    //     value := children[pos].Query(needle);
    //     assert needle in Interpretation() ==> needle in children[pos].Interpretation();
    //     assert needle in Interpretation() <== needle in children[pos].Interpretation();
    //     assert needle in Interpretation() ==> value == Interpretation()[needle];
    //     assert needle !in Interpretation() ==> value == DefaultValue();
    //   }
    // }

    predicate Full()
      requires WF()
      reads this, subtreeObjects
    {
      nchildren == MaxChildren()
    }
    
    method Insert(key: Key, value: Value)
      requires WF()
      requires !Full()
      ensures WF()
      ensures Interpretation() == old(Interpretation())[key := value]
      modifies this, subtreeObjects

    method Split() returns (pivot: Key, rightnode: Node)
      requires WF()
      requires Full()
      ensures SplitEnsures(old(Interpretation()), pivot, rightnode)
      modifies this  
  }
}
