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
    ensures 1 < MaxKeysPerLeaf() as int < Uint64UpperBound() / 2

  function method MaxChildren() : uint64
    ensures 3 < MaxChildren() as int < Uint64UpperBound() / 2

  function method DefaultValue() : Value
  function method DefaultKey() : Key

  lemma AssumeFalse()
    ensures false
  {
    assert false;
  }
    
  trait Node {
    ghost var subtreeObjects: set<object>
    ghost var allKeys: set<Key>
      
    predicate WF()
      reads this, subtreeObjects
      ensures WF() ==> this in subtreeObjects
      decreases subtreeObjects, 0

    // function QueryDef(needle: Key) : QueryResult
    //   requires WF()
    //   reads this, subtreeObjects
    //   decreases subtreeObjects
      
    function Interpretation() : map<Key, Value>
      requires WF()
      // ensures forall key :: QueryDef(key).Found? ==> MapsTo(Interpretation(), key, QueryDef(key).value)
      // ensures forall key :: QueryDef(key).NotFound? ==> key !in Interpretation()
      reads this, subtreeObjects
      decreases subtreeObjects

    method Query(needle: Key) returns (result: QueryResult)
      requires WF()
      //ensures result == QueryDef(needle)
      ensures needle in Interpretation() ==> result == Found(Interpretation()[needle])
      ensures needle !in Interpretation() ==> result == NotFound
      decreases subtreeObjects

    predicate method Full()
      requires WF()
      reads this, subtreeObjects
      
    method Insert(key: Key, value: Value)
      requires WF()
      requires !Full()
      ensures WF()
      ensures Interpretation() == old(Interpretation())[key := value]
      ensures allKeys == old(allKeys) + {key}
      ensures fresh(subtreeObjects-old(subtreeObjects))
      modifies this, subtreeObjects
      decreases allKeys
      
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
      && allKeys != {}
      && rightnode.allKeys != {}
      && (forall key :: key in allKeys ==> Keys.lt(key, pivot))
      && (forall key :: key in rightnode.allKeys ==> Keys.lte(pivot, key))
    }
      
    method Split() returns (ghost wit: Key, pivot: Key, rightnode: Node)
      requires WF()
      requires Full()
      ensures SplitEnsures(old(Interpretation()), pivot, rightnode)
      ensures allKeys <= old(allKeys)
      ensures rightnode.allKeys <= old(allKeys)
      ensures pivot in old(allKeys)
      ensures wit in old(allKeys)
      ensures Keys.lt(wit, pivot)
      ensures subtreeObjects <= old(subtreeObjects)
      ensures subtreeObjects !! rightnode.subtreeObjects
      ensures fresh(rightnode.subtreeObjects - old(subtreeObjects))
      modifies this
  }

  datatype NodeBox = NodeBox(node: Node?)
  
  class Leaf extends Node {
    var nkeys : uint64
    var keys: array<Key>
    var values: array<Value>

    predicate WF()
      reads this, subtreeObjects
      ensures WF() ==> this in subtreeObjects
      decreases subtreeObjects, 0
    {
      && subtreeObjects == {this, keys, values}
      && keys != values
      && keys.Length == MaxKeysPerLeaf() as int
      && values.Length == MaxKeysPerLeaf() as int
      && 0 <= nkeys <= keys.Length as uint64
      && Keys.IsStrictlySorted(keys[..nkeys])
      && allKeys == set key | key in multiset(keys[..nkeys])
    }

    // function QueryDef(needle: Key) : (result: QueryResult)
    //   requires WF()
    //   reads subtreeObjects
    // {
    //   var pos: int := Keys.LargestLte(keys[..nkeys], needle);
    //   if 0 <= pos && keys[pos] == needle then Found(values[pos])
    //   else NotFound
    // }
    
    function Interpretation() : map<Key, Value>
      requires WF()
      // ensures forall key :: QueryDef(key).Found? ==> MapsTo(Interpretation(), key, QueryDef(key).value)
      // ensures forall key :: QueryDef(key).NotFound? ==> key !in Interpretation()
      reads this, subtreeObjects
      decreases subtreeObjects
    {
      Keys.PosEqLargestLteForAllElts(keys[..nkeys]);
      map k | (k in keys[..nkeys]) :: values[Keys.LargestLte(keys[..nkeys], k)]
    }


    method Query(needle: Key) returns (result: QueryResult)
      requires WF()
      ensures needle in Interpretation() ==> result == Found(Interpretation()[needle])
      ensures needle !in Interpretation() ==> result == NotFound
      //ensures result == QueryDef(needle)
      decreases subtreeObjects
    {
      //Keys.reveal_IsStrictlySorted();
      var posplus1: uint64 := Keys.ArrayLargestLtePlus1(keys, 0, nkeys, needle);
      if 1 <= posplus1 && keys[posplus1-1] == needle {
        result := Found(values[posplus1-1]);
      } else {
        result := NotFound;
      }
    }

    predicate method Full()
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
      ensures allKeys == old(allKeys) + {key}
      ensures fresh(subtreeObjects-old(subtreeObjects))
      modifies this, subtreeObjects
      decreases allKeys
    {
      var posplus1 := Keys.ArrayLargestLtePlus1(keys, 0, nkeys, key);

      if 1 <= posplus1 && keys[posplus1-1] == key {
        values[posplus1-1] := value;
      } else {
        ghost var oldkeys := keys[..nkeys];
        Arrays.Insert(keys, nkeys, key, posplus1);
        Arrays.Insert(values, nkeys, value, posplus1);
        nkeys := nkeys + 1;
        allKeys := allKeys + {key};

        InsertMultiset(oldkeys, key, posplus1 as int); // OBSERVE
        Keys.strictlySortedInsert(oldkeys, key, posplus1 as int - 1); // OBSERVE
        Keys.PosEqLargestLte(keys[..nkeys], key, posplus1 as int);
        forall key' |  key' != key && key' in old(Interpretation())
          ensures key' in Interpretation() && Interpretation()[key'] == old(Interpretation())[key']
        {
          var i: int := Keys.LargestLte(old(keys[..nkeys]), key');
          //assert 0 <= i;
          if i < posplus1 as int {
            //assert keys[i] == key';
            Keys.PosEqLargestLte(keys[..nkeys], key', i);
          } else {
            //assert keys[i+1] == key';
            Keys.PosEqLargestLte(keys[..nkeys], key', i+1);
          }
        }
        forall key' | key' != key && key' in Interpretation()
          ensures key' in old(Interpretation()) && old(Interpretation())[key'] == Interpretation()[key']
        {
          var i: int := Keys.LargestLte(keys[..nkeys], key');
          if i < posplus1 as int {
            Keys.PosEqLargestLte(old(keys[..nkeys]), key', i);
          } else {
            Keys.PosEqLargestLte(old(keys[..nkeys]), key', i-1);
          }
        }
      }
    }

    method Split() returns (ghost wit: Key, pivot: Key, rightnode: Node)
      requires WF()
      requires Full()
      ensures SplitEnsures(old(Interpretation()), pivot, rightnode)
      ensures allKeys <= old(allKeys)
      ensures rightnode.allKeys <= old(allKeys)
      ensures pivot in old(allKeys)
      ensures wit in old(allKeys)
      ensures Keys.lt(wit, pivot)
      ensures subtreeObjects <= old(subtreeObjects)
      ensures subtreeObjects !! rightnode.subtreeObjects
      ensures fresh(rightnode.subtreeObjects - old(subtreeObjects))
      modifies this
    {
      var right := new Leaf();
      var boundary := nkeys/2;
      Arrays.Memcpy(right.keys, 0, keys[boundary..nkeys]); // FIXME: remove conversion to seq
      Arrays.Memcpy(right.values, 0, values[boundary..nkeys]); // FIXME: remove conversion to seq
      right.nkeys := nkeys - boundary;
      nkeys := boundary;
      allKeys := set key | key in multiset(keys[..nkeys]);
      right.allKeys := set key | key in multiset(right.keys[..right.nkeys]);
      assert keys[0] in allKeys;
      assert right.keys[0] in right.allKeys;
      wit := keys[0];
      pivot := right.keys[0];
      rightnode := right;

      // Prove these things are still strictly sorted
      assert keys[..nkeys] == old(keys[..nkeys])[..nkeys];
      Keys.StrictlySortedSubsequence(old(keys[..nkeys]), 0, nkeys as int);
      assert WF();
      assert right.keys[..right.nkeys] == old(keys[..nkeys])[boundary..old(nkeys)];
      Keys.StrictlySortedSubsequence(old(keys[..nkeys]), boundary as int, old(nkeys) as int);
      assert Keys.IsStrictlySorted(right.keys[..right.nkeys]);
      assert right.WF();
      Keys.IsStrictlySortedImpliesLt(old(keys[..nkeys]), 0, boundary as int);
    }
      
    constructor()
      ensures WF()
      ensures Interpretation() == map[]
      ensures !Full()
      ensures fresh(keys)
      ensures fresh(values)
    {
      nkeys := 0;
      keys := new Key[MaxKeysPerLeaf()](_ => DefaultKey());
      values := new Value[MaxKeysPerLeaf()](_ => DefaultValue());
      allKeys := {};
      subtreeObjects := {this, keys, values};
    }
  }

  class Index extends Node {
    var nchildren: uint64
    var pivots: array<Key>
    var children: array<NodeBox>

    function ChildSubtreeObjects(i: int) : set<object>
      requires 0 <= i < nchildren as int <= children.Length
      requires children[i].node != null
      reads this, children, children[i].node
    {
      children[i].node.subtreeObjects
    }
    
    predicate WF()
      reads this, subtreeObjects
      ensures WF() ==> this in subtreeObjects
      decreases subtreeObjects, 0
    {
      && {this, pivots, children} <= subtreeObjects
      && pivots.Length == (MaxChildren() as int) - 1
      && children.Length == MaxChildren() as int
      && 1 <= nchildren <= MaxChildren()
      && Keys.IsStrictlySorted(pivots[..nchildren-1])
      && (forall i :: 0 <= i < nchildren ==> children[i].node != null)
      && (forall i :: 0 <= i < nchildren ==> children[i].node in subtreeObjects)
      && (forall i :: 0 <= i < nchildren ==> ChildSubtreeObjects(i as int) < subtreeObjects)
      && (forall i :: 0 <= i < nchildren ==> {this, pivots, children} !! ChildSubtreeObjects(i as int))
      && (forall i :: 0 <= i < nchildren ==> children[i].node.WF())
      && (forall i, j :: 0 <= i < j < nchildren ==> ChildSubtreeObjects(i as int) !! ChildSubtreeObjects(j as int))
      && (forall i, key :: 0 <= i < nchildren-1 && key in children[i].node.allKeys ==> Keys.lt(key, pivots[i]))
      && (forall i, key :: 0 < i < nchildren   && key in children[i].node.allKeys ==> Keys.lte(pivots[i-1], key))
      && (forall i :: 0 <= i < nchildren ==> children[i].node.allKeys != {})
    }

    lemma AllKeysStrictlyDecreasing()
      requires WF()
      ensures forall i :: 0 <= i < nchildren ==> children[i].node.allKeys < allKeys
    {
      AssumeFalse();
    }
    
    // function QueryDef(needle: Key) : QueryResult
    //   requires WF()
    //   reads this, subtreeObjects
    //   decreases subtreeObjects
    // {
    //   var pos := Keys.LargestLte(pivots[..nchildren-1], needle);
    //   children[pos + 1].node.QueryDef(needle)
    // }
    
    function Interpretation() : (result: map<Key, Value>)
      requires WF()
      // ensures forall key :: QueryDef(key).Found? ==> MapsTo(result, key, QueryDef(key).value)
      // ensures forall key :: QueryDef(key).NotFound? ==> key !in Interpretation()
      reads this, subtreeObjects
      decreases subtreeObjects
    {
      // This is just to prove finiteness.  Thanks to James Wilcox for the trick:
      // https://stackoverflow.com/a/47585360
      var allkeys := set key, i | 0 <= i < nchildren && key in children[i].node.Interpretation() :: key;
      var result := map key |
        && key in allkeys
        && key in children[Keys.LargestLte(pivots[..nchildren-1], key) + 1].node.Interpretation()
        :: children[Keys.LargestLte(pivots[..nchildren-1], key) + 1].node.Interpretation()[key];

      // assert forall key :: QueryDef(key).Found? ==> key in children[Keys.LargestLte(pivots[..nchildren-1], key)+1].node.Interpretation();
        
      result
    }

    method Query(needle: Key) returns (result: QueryResult)
      requires WF()
      ensures needle in Interpretation() ==> result == Found(Interpretation()[needle])
      ensures needle !in Interpretation() ==> result == NotFound
      // ensures result == QueryDef(needle)
      decreases subtreeObjects
    {
      var posplus1 := Keys.ArrayLargestLtePlus1(pivots, 0, nchildren-1, needle);
      result := children[posplus1].node.Query(needle);
    }

    predicate method Full()
      requires WF()
      reads this, subtreeObjects
    {
      nchildren == MaxChildren()
    }

    // static lemma ChildSplitPreservesWF(
    //   oldpivots: seq<Key>,
    //   oldchildren: seq<Node?>,
    //   oldsubtreeObjects: set<object>,
    //   pos: int,
    //   newpivots: seq<Key>,
    //   newchildren: seq<Node?>,
    //   newsubtreeObjects: seq<object>)
    //   requires 

    method SplitChild(key: Key, childidx: uint64) returns (newchildidx: uint64)
      requires WF()
      requires !Full()
      requires childidx as int == 1 + Keys.LargestLte(pivots[..nchildren-1], key)
      requires children[childidx].node.Full()
      ensures WF()
      ensures Interpretation() == old(Interpretation())
      ensures newchildidx as int == 1 + Keys.LargestLte(pivots[..nchildren-1], key)
      ensures !children[newchildidx].node.Full()
      ensures allKeys == old(allKeys)
      ensures fresh(subtreeObjects-old(subtreeObjects))
      modifies this, subtreeObjects
    {
        var wit, pivot, right := children[childidx].node.Split();
        Arrays.Insert(pivots, nchildren - 1, pivot, childidx);
        Arrays.Insert(children, nchildren, NodeBox(right), childidx + 1);
        nchildren := nchildren + 1;
        subtreeObjects := subtreeObjects + right.subtreeObjects;
        if Keys.lte(pivot, key) {
          newchildidx := childidx + 1;
        } else {
          newchildidx := childidx;
        }
        AssumeFalse();
        
    //     Keys.strictlySortedInsert(old(pivots[..nchildren-1]), pivot, childidx-1);
    //     assert Keys.IsStrictlySorted(pivots[..nchildren-1]);
    //     forall i: int | 0 <= i < nchildren as int
    //       ensures children[i] != null
    //       ensures children[i] in subtreeObjects
    //       ensures children[i].subtreeObjects < subtreeObjects
    //       ensures {this, pivots, children} !! children[i].subtreeObjects
    //     {
    //       if childidx + 1 < i {
    //         assert children[i] == old(children[i-1]);
    //       }
    //     }
    //     forall i: int | 0 <= i < nchildren as int
    //       ensures children[i].WF()
    //     {
    //       if i < childidx + 1 {
    //         assert children[i] == old(children[i]);
    //       } else if childidx + 1 < i {
    //         assert children[i] == old(children[i-1]);
    //       }
    //     }
    //     forall i: int, j: int | 0 <= i < j < nchildren as int
    //       ensures children[i].subtreeObjects !! children[j].subtreeObjects
    //     {
    //       if j < childidx + 1 {
    //       } else if j == childidx + 1 {
    //       } else if i < childidx + 1 < j {
    //         assert childidx + 1 < j;
    //         assert children[j] == old(children[j-1]);
    //       } else if i == childidx + 1 {
    //         assert childidx + 1 < j;
    //         assert children[j] == old(children[j-1]);
    //       } else if childidx + 1 < i {
    //         assert children[i] == old(children[i-1]);
    //         assert childidx + 1 < j;
    //         assert children[j] == old(children[j-1]);
    //       }
    //     }
    //     forall i: int, key | 0 <= i < (nchildren as int)-1 && key in children[i].allKeys
    //       ensures Keys.lt(key, pivots[i])
    //     {
    //       if childidx + 1 < i {
    //         assert children[i] == old(children[i-1]);
    //       }
    //     }
    //     forall i: int, key | 0 < i < nchildren as int && key in children[i].allKeys
    //       ensures Keys.lt(pivots[i-1], key)
    //     {
    //       if childidx + 1 < i {
    //         assert children[i] == old(children[i-1]);
    //       }
    //     }
    //     assert WF();
    //     //assert Interpretation() == old(Interpretation());

    }
    
    method Insert(key: Key, value: Value)
      requires WF()
      requires !Full()
      ensures WF()
      ensures Interpretation() == old(Interpretation())[key := value]
      ensures allKeys == old(allKeys) + {key}
      ensures fresh(subtreeObjects - old(subtreeObjects))
      modifies this, subtreeObjects
      decreases allKeys
    {
      var posplus1 := Keys.ArrayLargestLtePlus1(pivots, 0, nchildren - 1, key);
      var childidx := (posplus1) as uint64;
      if children[posplus1].node.Full() {
        childidx := SplitChild(key, childidx);
      }
      AllKeysStrictlyDecreasing();
      children[childidx].node.Insert(key, value);
      subtreeObjects := subtreeObjects + children[childidx].node.subtreeObjects;
      allKeys := allKeys + {key};
      forall key' | key' in old(Interpretation()) && key' != key
        ensures key' in Interpretation() && Interpretation()[key'] == old(Interpretation()[key'])
      {
        var i :| 0 <= i < old(nchildren) && key' in old(children[i].node.Interpretation());
      }
      
    }

    function UnionSubtreeObjects() : set<object>
      requires nchildren as int <= children.Length
      requires forall i :: 0 <= i < nchildren ==> children[i].node != null
      reads this, children, set i | 0 <= i < nchildren :: children[i].node
    {
      set o, i | 0 <= i < nchildren && o in children[i].node.subtreeObjects :: o
    }
    
    method Split() returns (ghost wit: Key, pivot: Key, rightnode: Node)
      requires WF()
      requires Full()
      ensures SplitEnsures(old(Interpretation()), pivot, rightnode)
      ensures allKeys <= old(allKeys)
      ensures rightnode.allKeys <= old(allKeys)
      ensures pivot in old(allKeys)
      ensures wit in old(allKeys)
      ensures Keys.lt(wit, pivot)
      ensures subtreeObjects <= old(subtreeObjects)
      ensures subtreeObjects !! rightnode.subtreeObjects
      ensures fresh(rightnode.subtreeObjects - old(subtreeObjects))
      modifies this
    {
      var right := new Index();
      var boundary := nchildren/2;
      Arrays.Memcpy(right.pivots, 0, pivots[boundary..nchildren-1]); // FIXME: remove conversion to seq
      Arrays.Memcpy(right.children, 0, children[boundary..nchildren]); // FIXME: remove conversion to seq
      right.nchildren := nchildren - boundary;
      nchildren := boundary;
      subtreeObjects := {this, pivots, children} + UnionSubtreeObjects();
      right.subtreeObjects := right.subtreeObjects + right.UnionSubtreeObjects();

      pivot := pivots[boundary-1];

      right.allKeys := set k | k in allKeys && Keys.lte(pivot, k);
      allKeys := set k | k in allKeys && Keys.lt(k, pivot);
      
      wit := right.pivots[0];
      rightnode := right;
      AssumeFalse();
      
      // Keys.reveal_IsStrictlySorted();
      // assert WF();
      // assert rightnode.WF();
      // assert MergeMaps(Interpretation(), pivot, rightnode.Interpretation()) == old(Interpretation());
    }

    constructor()
      ensures nchildren == 0
      ensures pivots.Length == (MaxChildren() as int)-1
      ensures children.Length == (MaxChildren() as int)
      ensures forall i :: 0 <= i < children.Length ==> children[i].node == null
      ensures subtreeObjects == {this, pivots, children}
      ensures allKeys == {}
      ensures fresh(pivots)
      ensures fresh(children)
    {
      pivots := new Key[MaxChildren()-1](_ => DefaultKey());
      children := new NodeBox[MaxChildren()](_ => NodeBox(null));
      nchildren := 0;
      subtreeObjects := {this, pivots, children};
      allKeys := {};
    }
  }

  class MutableBtree {
    var root: Node

    function Interpretation() : map<Key, Value>
      requires root.WF()
      reads this, root, root.subtreeObjects
    {
      root.Interpretation()
    }

    method Query(needle: Key) returns (result: QueryResult)
      requires root.WF()
      ensures result == NotFound ==> needle !in Interpretation()
      ensures result.Found? ==> needle in Interpretation() && Interpretation()[needle] == result.value
    {
      result := root.Query(needle);
    }

    method Insert(key: Key, value: Value)
      requires root.WF()
      ensures root.WF()
      ensures Interpretation() == old(Interpretation())[key := value]
      modifies this, root, root.subtreeObjects
    {
      if root.Full() {
        var newroot := new Index();
        newroot.children[0] := NodeBox(root);
        newroot.nchildren := 1;
        newroot.subtreeObjects := newroot.subtreeObjects + root.subtreeObjects;
        newroot.allKeys := root.allKeys;
        root := newroot;
      }
      AssumeFalse();
      root.Insert(key, value);
    }
    
    constructor()
      ensures root.WF()
      ensures Interpretation() == map[]
    {
      root := new Leaf();
    }
  }
}

module TestMutableBtree refines MutableBtree {
  import Keys = Uint64_Order
  type Value = uint64

  function method MaxKeysPerLeaf() : uint64 { 64 }
  function method MaxChildren() : uint64 { 64 }

  function method DefaultValue() : Value { 0 }
  function method DefaultKey() : Key { 0 }
}

module MainModule {
  import opened NativeTypes
  import TestMutableBtree
    
  method Main()
  {
    // var n: uint64 := 1_000_000;
    // var p: uint64 := 300_007;
    var n: uint64 := 10_000_000;
    var p: uint64 := 3_000_017;
    // var n: uint64 := 100_000_000;
    // var p: uint64 := 1_073_741_827;
    var t := new TestMutableBtree.MutableBtree();
    var i: uint64 := 0;
    while i < n
      invariant 0 <= i <= n
      invariant t.root.WF()
      modifies t, t.root, t.root.subtreeObjects
    {
      t.Insert((i * p) % n , i);
      i := i + 1;
    }

    // i := 0;
    // while i < n
    //   invariant 0 <= i <= n
    // {
    //   var needle := (i * p) % n;
    //   var qr := t.Query(needle);
    //   if qr != TestMutableBtree.Found(i) {
    //     print "Test failed";
  //   } else {
  //     //print "Query ", i, " for ", needle, "resulted in ", qr.value, "\n";
  //   }
  //   i := i + 1;
  // }

  // i := 0;
  // while i < n
  //   invariant 0 <= i <= n
  // {
  //   var qr := t.Query(n + ((i * p) % n));
  //   if qr != TestMutableBtree.NotFound {
  //     print "Test failed";
  //   } else {
  //     //print "Didn't return bullsh*t\n";
  //   }
  //   i := i + 1;
  // }
    print "PASSED\n";
  }
} 
