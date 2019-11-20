include "../lib/Base/total_order.i.dfy"
include "../lib/Base/sequences.i.dfy"
include "../lib/Base/Arrays.i.dfy"
include "../lib/Base/Option.s.dfy"

abstract module StrictlySortedArray {
  import opened Options
  import opened NativeTypes
  import opened Seq = Sequences
  import Arrays
  import Keys : Total_Order

  type Key = Keys.Element
  
  class StrictlySortedArray {
    var nkeys: uint64
    var arr: array<Key>
    ghost var iterators: set<StrictlySortedArrayIterator>
    
    predicate WF()
      reads this, arr
    {
      && 0 <= nkeys as int <= arr.Length
      && Keys.IsStrictlySorted(arr[..nkeys])
      && arr.Length < Uint64UpperBound() / 2
    }

    predicate AllIteratorsValid()
      reads this
      reads this, arr, iterators
    {
      && (forall iter :: iter in iterators ==> iter.ssa == this)
      && (forall iter :: iter in iterators ==> iter.WF())
    }
    
    function I() : seq<Key>
      requires WF()
      reads this, arr
    {
      arr[..nkeys]
    }

    method Insert(key: Key)
      requires WF()
      requires nkeys as int < arr.Length
      requires key !in arr[..nkeys]
      requires AllIteratorsValid()
      ensures WF()
      ensures AllIteratorsValid()
      ensures I() == Seq.insert(old(I()), key, Keys.LargestLte(old(I()), key) + 1)
      ensures arr == old(arr)
      ensures iterators == old(iterators)
      modifies this, arr
    {
      var pos := Keys.ArrayLargestLtePlus1(arr, 0, nkeys, key);
      Arrays.Insert(arr, nkeys, key, pos);
      nkeys := nkeys + 1;
      Keys.strictlySortedInsert(old(I()), key, pos as int - 1);
      forall iter | iter in iterators
        ensures iter.WF()
      {
        if !iter.Done() {
          if iter.pos < pos {
            assert arr[iter.pos] == old(arr[iter.pos]);
          } else if iter.pos == pos {
            assert Keys.lt(key, old(arr[pos]));
          } else {
            assert arr[iter.pos] == old(arr[iter.pos-1]);
          }
        }
      }
    }

    constructor StrictlySortedArray(capacity: uint64, defaultKey: Key)
      requires capacity as int < Uint64UpperBound() / 2
      ensures WF()
      ensures AllIteratorsValid()
      ensures nkeys == 0
      ensures arr.Length == capacity as int
      ensures fresh(arr)
    {
      nkeys := 0;
      arr := new Key[capacity](_ => defaultKey);
      iterators := {};
    }
  }
  
  class StrictlySortedArrayIterator {
    var ssa: StrictlySortedArray
    var pos: uint64
    var key: Option<Key>

    predicate method Done()
      reads this, this.ssa
    {
      key == None
    }
    
    predicate WF()
      reads this, ssa, ssa.arr
    {
      && ssa.WF()
      && this in ssa.iterators
      && 0 <= pos <= ssa.nkeys
      && (!Done() ==> pos < ssa.nkeys)
      && (!Done() ==> Keys.lte(ssa.arr[pos], key.value))
    }

    method Next()
      requires WF()
      requires !Done()
      requires ssa.AllIteratorsValid()
      ensures WF()
      ensures key == Keys.SeqNext(ssa.I(), old(key.value))
      ensures ssa.AllIteratorsValid()
      ensures ssa == old(ssa)
      modifies this
    {
      pos := pos + 1;
      var t;
      if pos < ssa.nkeys {
        t := Keys.cmp(ssa.arr[pos], key.value);
      }
      while pos < ssa.nkeys && t <= 0
        invariant 0 < pos <= ssa.nkeys
        invariant ssa == old(ssa)
        invariant key == old(key)
        invariant pos < ssa.nkeys ==> (t <= 0 <==> Keys.lte(ssa.arr[pos], key.value))
        invariant Keys.lte(ssa.arr[pos-1], key.value)
      {
        pos := pos + 1;
        if pos < ssa.nkeys {
          t := Keys.cmp(ssa.arr[pos], key.value);
        }
      }
      if pos < ssa.nkeys {
        assert Keys.lte(ssa.arr[pos-1], key.value);
        assert Keys.lt(key.value, ssa.arr[pos]);
        Keys.StrictlySortedSeqNext(ssa.I(), key.value, pos as int);
        key := Some(ssa.arr[pos]);
      } else {
        forall next | next in ssa.I()
          ensures Keys.lte(next, key.value)
        {
          var nextpos := Seq.IndexOf(ssa.I(), next);
          Keys.IsStrictlySortedImpliesLte(ssa.I(), nextpos, pos as int - 1);
        }
        key := None;
      }
    }
   
    constructor StrictlySortedArrayIterator(ssa: StrictlySortedArray)
      requires ssa.WF()
      requires ssa.AllIteratorsValid()
      ensures WF()
      ensures ssa.nkeys == old(ssa.nkeys)
      ensures ssa.arr == old(ssa.arr)
      ensures ssa.arr[..] == old(ssa.arr[..])
      ensures ssa.WF()
      ensures ssa.AllIteratorsValid()
      ensures ssa.iterators == old(ssa.iterators) + {this}
      ensures 0 < ssa.nkeys as int ==> key == Some(ssa.arr[0])
      modifies ssa
    {
      this.ssa := ssa;
      pos := 0;
      new;
      if pos < ssa.nkeys {
        key := Some(ssa.arr[0]);
      } else {
        key := None;
      }
      ssa.iterators := ssa.iterators + {this};
    }
  }
}

module TestStrictlySortedArray refines StrictlySortedArray {
  import Keys = Uint64_Order
}
  
module Test {
  import opened TestStrictlySortedArray
  import opened Options
    
  method Main()
  {
    var ssa := new StrictlySortedArray.StrictlySortedArray(1000, 0);
    ssa.Insert(10);
    ssa.Insert(5);
    var iter := new StrictlySortedArrayIterator.StrictlySortedArrayIterator(ssa);
    ssa.Insert(15);
    assert iter.key == Some(5);
    iter.Next();
    if !iter.Done() {
      print iter.key.value;
      print "\n";
    }
    ssa.Insert(20);
    iter.Next();
    if !iter.Done() {
      print iter.key.value;
      print "\n";
    }
    
  }
}
