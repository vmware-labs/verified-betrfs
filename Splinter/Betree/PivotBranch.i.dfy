// Copyright 2018-2021 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, and University of Washington
// SPDX-License-Identifier: BSD-2-Clause
 
include "../../lib/Base/KeyType.s.dfy"
include "../../Spec/Message.s.dfy"
include "../../lib/Base/Option.s.dfy"
include "../../lib/Base/Maps.i.dfy"
include "../../lib/Base/Sequences.i.dfy"
include "../../lib/Base/total_order_impl.i.dfy"
include "Buffer.i.dfy"
include "Domain.i.dfy"

// Jumping straight to PivotBranch (instead of PagedBranch) since operations are simple enough
// no need for a pure algebraic layer

module PivotBranchMod {
  import opened Maps
  import opened Options
  import opened KeyType
  import opened ValueMessage
  import opened Sequences
  import opened DomainMod
  import opened BufferMod
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
  // before querying key msg in the data store (pivot branch).
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

    function Query(key: Key) : (result: Message)
      requires WF()
      ensures key !in AllKeys() ==> result == Update(NopDelta())
      ensures result == I().Query(key)
    {
      var r := Route(key);
      if Leaf? then (
        if Route(key) >= 0 && keys[r] == key
        then msgs[Route(key)] else Update(NopDelta())
      ) else (
        children[Route(key)+1].Query(key)
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

    // Mutable operations 

    // Grow
    function Grow() : (out: Node)
    {
      Index([], [this])
    }

    lemma GrowPreservesWF()
      requires WF()
      requires AllKeys() != {}
      ensures Grow().WF()
    {
      assert Keys.IsStrictlySorted([]) by {
        Keys.reveal_IsStrictlySorted();
      }
    }

    lemma GrowPreservesAllKeys()
      requires WF()
      ensures Grow().AllKeys() == AllKeys()
    {
      assert forall key :: key in AllKeys() ==> key in Grow().children[0].AllKeys();
    }

    lemma InterpretationDelegation(key: Key)
      requires WF()
      requires Index?
      requires key in children[Keys.LargestLte(pivots, key)+1].I().mapp
      ensures MapsTo(I().mapp, key, children[Keys.LargestLte(pivots, key)+1].I().mapp[key])
    {
      var interp := I().mapp;
      assert key in children[Keys.LargestLte(pivots, key)+1].AllKeys();
      assert key in AllKeys();
      assert key in interp;
    }

    lemma GrowPreservesI()
      requires WF()
      requires AllKeys() != {}
      ensures Grow().WF()
      ensures Grow().I() == I()
    {
      var interp := I().mapp;
      GrowPreservesWF();
      var ginterp := Grow().I().mapp;
      
      forall key | key in interp
        ensures key in ginterp && ginterp[key] == interp[key]
      {
        Grow().InterpretationDelegation(key);
      }
    }

    // Insert 
    function InsertLeaf(key: Key, msg: Message) : (result: Node)
    requires Leaf?
    requires WF()
    ensures result.Leaf?
    ensures result.WF()
    {
      var llte := Keys.LargestLte(keys, key);
      if 0 <= llte && keys[llte] == key then
        Leaf(keys, msgs[llte := msg])
      else
        Keys.strictlySortedInsert(keys, key, llte);
        // TODO: ensures from this lemma can't be asserted?
        Leaf(insert(keys, key, llte+1), insert(msgs, msg, llte+1))
    }

    lemma {:timeLimitMultiplier 2} InsertLeafIsCorrect(key: Key, msg: Message)
    requires Leaf?
    requires WF()
    ensures InsertLeaf(key, msg).I() == Buffer(I().mapp[key := msg])
    ensures InsertLeaf(key, msg).AllKeys() == AllKeys() + {key}
    {
      var result := InsertLeaf(key, msg);
      var llte := Keys.LargestLte(keys, key);
      if 0 <= llte && keys[llte] == key {
        assert result.I() == Buffer(I().mapp[key := msg]);
      } else {
        Keys.reveal_IsStrictlySorted();
        forall k | k in result.I().mapp.Keys
          ensures k in I().mapp.Keys + {key}
        {
          var kpos := IndexOf(result.keys, k);
          if llte + 1 < kpos {
            assert k == keys[kpos-1];
          }
        }
        forall k | k in result.AllKeys()
          ensures k in AllKeys() + {key}
        {
          var i :| 0 <= i < |result.keys| && result.keys[i] == k;
          if i < llte+1 {
          } else if i == llte+1 {
          } else {
            assert k == keys[i-1];
          }
        }
      }
    }

    // Split 

    predicate SplitLeaf(leftleaf: Node, rightleaf: Node, pivot: Key)
    {
      && Leaf?
      && leftleaf.Leaf?
      && rightleaf.Leaf?
      && 0 < |leftleaf.keys| == |leftleaf.msgs|
      && 0 < |rightleaf.keys| == |rightleaf.msgs|
      && keys == leftleaf.keys + rightleaf.keys
      && msgs == leftleaf.msgs + rightleaf.msgs
      && Keys.lt(Last(leftleaf.keys), pivot)
      && Keys.lte(pivot, rightleaf.keys[0])
    }

    lemma SplitLeafPreservesWF(leftleaf: Node, rightleaf: Node, pivot: Key)
      requires WF()
      requires SplitLeaf(leftleaf, rightleaf, pivot)
      ensures leftleaf.WF()
      ensures rightleaf.WF()
    {
      Keys.StrictlySortedSubsequence(keys, 0, |leftleaf.keys|);
      Keys.StrictlySortedSubsequence(keys, |leftleaf.keys|, |keys|);
      assert Keys.IsStrictlySorted(keys[|leftleaf.keys|..|keys|]);
      assert rightleaf.keys == keys[|leftleaf.keys|..|keys|];
    }

    function SubIndex(from: int, to: int) : (result : Node)
    requires Index?
    requires |children| == |pivots| + 1
    requires 0 <= from < to <= |children|
    {
      Index(pivots[from..to-1], children[from..to])
    }

    lemma SubIndexPreservesWF(from: int, to: int)
      requires WF()
      requires Index?
      requires 0 <= from < to <= |children|
      ensures SubIndex(from, to).WF()
    {
      Keys.StrictlySortedSubsequence(pivots, from, to-1);
      var subindex := SubIndex(from, to);
      forall i | 0 <= i < to - from - 1
        ensures subindex.AllKeysBelowBound(i)
      {
        assert AllKeysBelowBound(from + i);
      }
      forall i | 0 < i < to - from
        ensures subindex.AllKeysAboveBound(i)
      {
        assert AllKeysAboveBound(from + i);
      }
      assert |subindex.pivots| == |subindex.children| - 1;
      assert subindex.WF();
    }

    predicate SplitIndex(leftindex: Node, rightindex: Node, pivot: Key)
    {
      && Index?
      && leftindex.Index?
      && rightindex.Index?
      && 0 < |leftindex.children| < |children|
      && |children| == |pivots| + 1

      && leftindex == SubIndex(0, |leftindex.children|)
      && rightindex == SubIndex(|leftindex.children|, |children|)
      && (forall key :: key in Last(leftindex.children).AllKeys() ==> Keys.lt(key, pivot))
      && (forall key :: key in rightindex.children[0].AllKeys() ==> Keys.lte(pivot, key))
      && pivot == pivots[|leftindex.pivots|]
    }

    lemma SplitIndexPreservesWF(leftindex: Node, rightindex: Node, pivot: Key)
      requires WF()
      requires SplitIndex(leftindex, rightindex, pivot)
      ensures leftindex.WF()
      ensures rightindex.WF()
    {
      SubIndexPreservesWF(0, |leftindex.children|);
      SubIndexPreservesWF(|leftindex.children|, |children|);
    }

    predicate SplitNode(leftnode: Node, rightnode: Node, pivot: Key)
    {
      || SplitLeaf(leftnode, rightnode, pivot)
      || SplitIndex(leftnode, rightnode, pivot)
    }

    // TODO: add in SplitIndexInterpretation, SplitNodeInterpretation
  }
}
