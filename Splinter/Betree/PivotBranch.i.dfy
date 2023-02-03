// Copyright 2018-2021 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, and University of Washington
// SPDX-License-Identifier: BSD-2-Clause
 
include "../../lib/Base/KeyType.s.dfy"
include "../../Spec/Message.s.dfy"
include "../../lib/Base/Option.s.dfy"
include "../../lib/Base/Maps.i.dfy"
include "../../lib/Base/Sequences.i.dfy"
include "../../lib/Base/total_order_impl.i.dfy"
include "Buffers.i.dfy"
include "Domain.i.dfy"

// Jumping straight to PivotBranch (instead of PagedBranch) since branch is immutable 
// have its operations are simple enough, no need for a pure algebraic layer

module PivotBranchMod {
  import opened Maps
  import opened Options
  import opened KeyType
  import opened ValueMessage
  import opened Sequences
  import opened DomainMod
  import opened Buffers
  import KeysImpl = Lexicographic_Byte_Order_Impl
  import Keys = KeysImpl.Ord

  // Flattened branch for iterators (sequential and merge)
  datatype FlattenedBranch = FlattenedBranch(keys: seq<Key>, msgs: seq<Message>)
  {
    predicate WF()
    {
      && |keys| == |msgs|
      && Keys.IsStrictlySorted(keys)
    }

    function Concat(other: FlattenedBranch) : (result: FlattenedBranch)
      requires WF()
      requires other.WF()
      requires |keys| > 0 && |other.keys| > 0 ==> Keys.lt(Last(keys), other.keys[0])
      ensures result.WF()
    {
      Keys.reveal_IsStrictlySorted();
      Keys.lteTransitiveForall();
      
      FlattenedBranch(keys + other.keys, msgs + other.msgs)
    }
  }

  // Bounded pivots are not necessary here, bounds are required for the B-epsilon node as clone
  // requires knowing the exact bound for prefix extraction. Any key transformation should be done
  // before querying key value in the data store (pivot branch).
  datatype Node = Index(pivots: seq<Key>, children: seq<Node>) | Leaf(keys: seq<Key>, msgs: seq<Message>)
  {
    function AllKeys() : set<Key>
      ensures Leaf? && 0 < |keys| ==> AllKeys() != {}
      ensures Index? && 0 < |pivots| ==> AllKeys() != {}
    {
      if Leaf? then 
        var result := set k | k in keys;
        assert 0 < |keys| ==> keys[0] in result;
        result
      else
        var pivotKeys := (set k | k in pivots);
        var indexKeys := (set i, k | 0 <= i < |children| && k in children[i].AllKeys() :: k);
        var result := pivotKeys + indexKeys;
        assert 0 < |pivots| ==> pivots[0] in result;
        result
    }

    predicate AllKeysBelowBound(i: int)
      requires Index?
      requires 0 <= i < |children|-1
      requires 0 <= i < |pivots|
    {
      forall key :: key in children[i].AllKeys() ==> Keys.lt(key, pivots[i])
    }

    predicate AllKeysAboveBound(i: int)
      requires Index?
      requires 0 <= i < |children|
      requires 0 <= i-1 < |pivots|
    {
      forall key :: key in children[i].AllKeys() ==> Keys.lte(pivots[i-1], key)
    }

    predicate WF()
    {
      if Leaf? then 
        && |keys| == |msgs|
        && Keys.IsStrictlySorted(keys)
      else
        && |pivots| == |children| - 1
        && Keys.IsStrictlySorted(pivots)
        && (forall i :: 0 <= i < |children| ==> children[i].WF())
        && (forall i :: 0 <= i < |children|-1 ==> AllKeysBelowBound(i))
        && (forall i :: 0 < i < |children|   ==> AllKeysAboveBound(i))
        // && (forall i :: 0 <= i < |children| ==> children[i].AllKeys() != {})
    }

    function Route(key: Key) : int
      requires WF()
    {
      var s := if Leaf? then keys else pivots;
      Keys.LargestLte(s, key)
    }

    // Takes in a btree node and returns the buffer abstraction
    function I() : Buffer
      requires WF()
    {
      if Leaf? then
        Keys.PosEqLargestLteForAllElts(keys);
        Buffer(map k | (k in keys) :: msgs[Route(k)])
      else 
        Buffer(map key |
        && key in AllKeys()
        && key in children[Route(key) + 1].I().mapp
        :: children[Route(key) + 1].I().mapp[key])
    }

    lemma AllKeysIsConsistentWithI(key: Key)
      requires WF()
      requires key in I().mapp
      ensures key in AllKeys()
      ensures Index? ==> WF() && key in children[Route(key) + 1].AllKeys()
    {
    }
  
    function Query(key: Key) : (result: Option<Message>)
      requires WF()
      ensures result.Some? <==> key in I().mapp
      ensures result.Some? ==> I().Query(key) == result.value
      ensures result.None? ==> I().Query(key) == Update(NopDelta())
    {
      var r := Route(key);
      if Leaf? then (
        if Route(key) >= 0 && keys[r] == key
        then Some(msgs[Route(key)]) else None
      ) else (
        var result := children[Route(key)+1].Query(key);
        assert result.Some? ==> key in children[Route(key)+1].AllKeys() by {
          if result.Some? {
            children[Route(key)+1].AllKeysIsConsistentWithI(key);
          } 
        }
        result
      )
    }

    function FlattenChildren(count: nat) : (result: FlattenedBranch)
    requires WF()
    requires Index?
    requires count <= |children|
    ensures result.WF()
    ensures forall k | k in result.keys :: k in AllKeys()
    ensures (0 < count < |children|) && (|result.keys| > 0) ==> Keys.lt(Last(result.keys), pivots[count-1])
    decreases this, count
    {
      if count == 0 then FlattenedBranch([], [])
      else (
        var left := FlattenChildren(count-1);
        var right := children[count-1].Flatten();
        // condition for Concat
        assert |left.keys| > 0 && |right.keys| > 0 ==> Keys.lt(Last(left.keys), right.keys[0]) by {
          if |left.keys| > 0 && |right.keys| > 0 {
            assert right.keys[0] in children[count-1].AllKeys();
            assert AllKeysAboveBound(count-1);
            Keys.lteTransitiveForall();
          }
        }

        var result := left.Concat(right);
        // post condition
        assert (0 < count < |children|) && (|result.keys| > 0) ==> Keys.lt(Last(result.keys), pivots[count-1]) by {
          if (0 < count < |children|) && (|result.keys| > 0) {
            if |right.keys| > 0 {
              assert AllKeysBelowBound(count-1); 
            }
            Keys.lteTransitiveForall();
          }
        }
        result
      )
    }

    // filter = keys to remove
    predicate IsFiltered(og: Node, filter: Domain)
      requires WF()
      requires og.WF()
      requires !filter.EmptyDomain?
    {
      && (forall k :: Query(k).Some? <==> (!filter.Contains(k) && og.Query(k).Some?))  // define this's domain
      && (forall k | Query(k).Some? :: Query(k) == og.Query(k)) // value matches og
    }

    lemma FilteredEquivApplyFilter(og: Node, filter: Domain)
      requires IsFiltered.requires(og, filter)
      requires IsFiltered(og, filter)
      ensures I() == og.I().ApplyFilter(Buffers.AllKeys() - filter.KeySet())
    {
      var actual := I();
      var expected := og.I().ApplyFilter(Buffers.AllKeys() - filter.KeySet());

      assert (forall k :: k in actual.mapp <==> (!filter.Contains(k) && og.Query(k).Some?));
      assert (forall k :: k in expected.mapp <==> (!filter.Contains(k) && og.Query(k).Some?));
      assert (forall k :: k in actual.mapp <==> k in expected.mapp);

      assert IsSubMap(actual.mapp, expected.mapp);
      assert IsSubMap(expected.mapp, actual.mapp);
      MapEquality(actual.mapp, expected.mapp);
    }
  
    // predicate IsFiltered(og: Node, filter: Domain)
    //   requires WF()
    //   requires og.WF()
    //   requires !filter.EmptyDomain?
    // {
    //   && (forall k :: Query(k).Some? <==> (filter.Contains(k) && og.Query(k).Some?))  // define this's domain
    //   && (forall k | Query(k).Some? :: Query(k) == og.Query(k)) // value matches og
    // }

    // lemma FilteredEquivApplyFilter(og: Node, filter: Domain)
    //   requires IsFiltered.requires(og, filter)
    //   requires IsFiltered(og, filter)
    //   ensures I() == og.I().ApplyFilter(filter.KeySet())
    // {
    //   var actual := I();
    //   var expected := og.I().ApplyFilter(filter.KeySet());

    //   assert (forall k :: k in actual.mapp <==> (filter.Contains(k) && og.Query(k).Some?));
    //   assert (forall k :: k in expected.mapp <==> (filter.Contains(k) && og.Query(k).Some?));
    //   assert (forall k :: k in actual.mapp <==> k in expected.mapp);

    //   assert IsSubMap(actual.mapp, expected.mapp);
    //   assert IsSubMap(expected.mapp, actual.mapp);
    //   MapEquality(actual.mapp, expected.mapp);
    // }

    // Note: intended for iterator which we currently don't have
    function Flatten() : (result: FlattenedBranch)
    requires WF()
    ensures result.WF()
    ensures forall k | k in result.keys :: k in AllKeys()
    {
      if Leaf? then FlattenedBranch(keys, msgs)
      else FlattenChildren(|children|)
    }

    // sorted list, then through filter for flattened list
    // merge iterator: FlattenedBranch
    // Condition for pack
    predicate FlattenEquivalent(b: FlattenedBranch)
      requires WF()
      requires b.WF()
    {
      && Flatten() == b
    }
  }

  // What can we show if we don't bother with it
  // we show function is the same as the other function
  // so as long as we can refine to a valid version of the prior 

  // PivotBranch SM:

  // datatype Variables = Variables(root: Node) {
  //   predicate WF() {
  //     && root.WF()
  //   }
  // }

  // predicate Query(v: Variables, v': Variables, lbl: TransitionLabel)
  // {
  //   && v.WF()
  //   && lbl.QueryLabel?
  //   && v.root.Query(lbl.key) == Some(lbl.msg)
  //   && v' == v
  // }

  // predicate Filter(v: Variables, v': Variables, lbl: TransitionLabel)
  // {
  //   && v.WF()
  //   && lbl.FilterLabel?
  //   && lbl.newroot.WF()
  //   && !lbl.domain.EmptyDomain?
  //   && lbl.newroot.IsFiltered(v.root, lbl.domain)
  //   && v'.root == lbl.newroot
  //   && v'.WF()
  // }

  // predicate Flatten(v: Variables, v': Variables, lbl: TransitionLabel)
  // {
  //   && v.WF()
  //   && lbl.FlattenLabel?
  //   && lbl.flattened.WF()
  //   && v.root.FlattenEquivalent(lbl.flattened)
  //   && v' == v
  // }

  // // public: 

  // predicate Init(v: Variables)
  // {
  //   && v.WF()
  // }

  // datatype Step = QueryStep | FilterStep | FlattenStep

  // datatype TransitionLabel =
  //   QueryLabel(key: Key, msg: Message)
  // | FilterLabel(newroot: Node, domain: Domain)
  // | FlattenLabel(flattened: FlattenedBranch)

  // predicate NextStep(v: Variables, v': Variables, lbl: TransitionLabel, step: Step)
  // {
  //   match step {
  //     case QueryStep() => Query(v, v', lbl)
  //     case FilterStep() => Filter(v, v', lbl)
  //     case FlattenStep() => Flatten(v, v', lbl)
  //   }
  // }
}