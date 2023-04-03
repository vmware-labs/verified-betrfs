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

  datatype TransitionLabel = 
    | QueryLabel(key: Key, msg: Message)
    | InsertLabel(key: Key, msg: Message)
    | InternalLabel()

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

    // We need to measure the height of Nodes to manage termination in the mutual
    // recursion between InsertNode and InsertIndex. You'd think that we wouldn't
    // need to, since datatypes are well-founded. But when we SplitChildOfIndex,
    // we replace some children with other children. The new children are of no
    // greater height, but they don't order in Dafny's internal datatype lattice.
    // Hence this machinery for explicitly measuring height.
    function IndexHeights(): seq<int>
      requires WF()
      requires Index?
      decreases this, 0
    {
        seq(|children|, i requires 0<=i<|children| => children[i].Height())
    }

    function {:opaque} Height(): nat
      requires WF()
      ensures Leaf? ==> Height() == 0
      decreases this, 1
    {
      if Leaf?
      then 0
      else
        var heights := IndexHeights(); seqMax(heights) + 1
    }

    lemma ChildrenAreShorter(childIdx: nat)
      requires WF()
      requires Index?
      requires 0 <= childIdx < |children|
      ensures children[childIdx].Height() < Height()
    {
      var child := children[childIdx];
      assert IndexHeights()[childIdx] == child.Height(); // trigger
      assert child.Height() in IndexHeights();  // trigger *harder*
      reveal_Height();
    }

    // Mutable operations 

    // Grow
    function Grow() : (out: Node)
    {
      Index([], [this])
    }

    // Insert 
    function InsertLeaf(key: Key, msg: Message) : (result: Node)
    requires Leaf?
    requires WF()
    ensures result.WF()
    ensures result.Height() == Height()
    ensures result.AllKeys() == AllKeys() + {key}
    {
      var llte := Keys.LargestLte(keys, key);
      var result := 
        if 0 <= llte && keys[llte] == key  then 
          Leaf(keys, msgs[llte := msg])
        else (
          assert Keys.IsStrictlySorted(insert(keys, key, llte+1)) by {
            reveal_insert();
            Keys.reveal_IsStrictlySorted();
          }
          Leaf(insert(keys, key, llte+1), insert(msgs, msg, llte+1))
        );

      assert result.Height() == Height() by { reveal_Height(); }
      assert result.AllKeys() == AllKeys() + {key} by {
        if !(0 <= llte && keys[llte] == key) {
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
  
      result   
    }

    function InsertIndex(key: Key, msg: Message) : (result: Node)
      requires Index?
      requires WF()
      ensures result.Index?
      ensures result.WF()
      ensures result.Height() == Height()
      ensures result.AllKeys() == AllKeys() + {key}
      decreases Height(), 1
    {
      var r := Route(key)+1;
      ChildrenAreShorter(r);
      var newChild := children[r].Insert(key, msg);
      var result := Index(pivots, children[r := newChild]);

      assert result.AllKeys() == AllKeys() + {key} by {
        var indexKeys := (set i, k | 0 <= i < |children| && k in children[i].AllKeys() :: k);
        var indexKeys' := (set i, k | 0 <= i < |result.children| && k in result.children[i].AllKeys() :: k);

        forall k 
          ensures k in indexKeys + {key} <==> k in indexKeys'
        {
          if k == key {
            assert k in result.children[r].AllKeys();
          } else if k in indexKeys {
            var i :| 0 <= i < |children| && k in children[i].AllKeys();
            assert k in result.children[i].AllKeys();
          } else if k in indexKeys' {
            var i :| 0 <= i < |result.children| && k in result.children[i].AllKeys();
            assert k in children[i].AllKeys();
          }
        }
      }

      assert result.WF() by {
        forall i | 0 <= i < |result.children|-1 
          ensures result.AllKeysBelowBound(i)
        {
          if i == r {
            forall key' | key' in newChild.AllKeys()
              ensures Keys.lt(key', pivots[i])
            {
              if key' != key {
                assert AllKeysBelowBound(i);
              }
            }
          } else {
            assert AllKeysBelowBound(i);
          }
        }

        forall i | 0 < i < |result.children|
          ensures result.AllKeysAboveBound(i)
        {
          if i == r {
            forall key' | key' in newChild.AllKeys()
              ensures Keys.lte(pivots[i-1], key')
            {
              if key' != key {
                assert AllKeysAboveBound(i);
              }
            }
          } else {
            assert AllKeysAboveBound(i);
          }
        }
      }

      assert result.Height() == Height() by {
        assert result.IndexHeights() == IndexHeights(); // trigger
        reveal_Height();
      }
      result
    }

    function Insert(key: Key, msg: Message) : (result: Node)
      requires WF()
      ensures result.WF()
      ensures result.Height() == Height()
      ensures result.AllKeys() == AllKeys() + {key}
      decreases Height(), 2
    {
      if Leaf? 
      then (
        InsertLeaf(key, msg)
      ) else (
        InsertIndex(key, msg)
      )
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

    function SubIndex(from: int, to: int) : (result : Node)
    requires Index?
    requires |children| == |pivots| + 1
    requires 0 <= from < to <= |children|
    {
      Index(pivots[from..to-1], children[from..to])
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

    predicate SplitNode(leftnode: Node, rightnode: Node, pivot: Key)
    {
      || SplitLeaf(leftnode, rightnode, pivot)
      || SplitIndex(leftnode, rightnode, pivot)
    }

    predicate SplitChildOfIndex(newIndex: Node, pivot: Key, childIdx: nat)
    {
      && Index?
      && newIndex.Index?
      && 0 <= childIdx < |children|
      && |children| == |pivots| + 1
      && |newIndex.children| == |children| + 1
      && newIndex.pivots == insert(pivots, pivot, childIdx)
      && newIndex.children == replace1with2(children, newIndex.children[childIdx], newIndex.children[childIdx+1], childIdx)
      && children[childIdx].SplitNode(newIndex.children[childIdx], newIndex.children[childIdx+1], pivot)
    }
  }

  // path 
  datatype Path = Path(node: Node, key: Key, depth: nat)
  {
    function Subpath() : (out: Path)
      requires 0 < depth
      requires node.WF()
      requires node.Index?
    {
      Path(node.children[node.Route(key)+1], key, depth-1)
    }

    predicate Valid()
      decreases depth
    {
      && node.WF()
      && (0 < depth ==> node.Index?)
      && (0 < depth ==> Subpath().Valid())
    }

    function Target() : (out: Node)
      requires Valid()
      ensures out.WF()
      decreases depth
    {
      if 0 == depth
      then node
      else Subpath().Target()
    }
  }

  // SM
  datatype Variables = Variables(root: Node)
  {
    predicate WF()
    {
      root.WF()
    }
  }

  predicate Query(v: Variables, v': Variables, lbl: TransitionLabel)
  {
    && lbl.QueryLabel?
    && v.WF()
    && v.root.Query(lbl.key) == lbl.msg
    && v' == v
  }

  predicate Insert(v: Variables, v': Variables, lbl: TransitionLabel)
  {
    && lbl.InsertLabel?
    && v.WF()
    && v'.root == v.root.Insert(lbl.key, lbl.msg)
  }

  predicate Grow(v: Variables, v': Variables, lbl: TransitionLabel)
  {
    && lbl.InternalLabel?
    && v.WF()
    && v'.root == v.root.Grow()
  }

  predicate ValidSplit(path: Path, newNode: Node)
    decreases path.depth
  {
    && path.Valid()
    && var r := path.node.Route(path.key)+1;
    && (path.depth > 0 ==> 
      && newNode.Index?
      && path.node.pivots == newNode.pivots
      && |path.node.children| == |newNode.children|
      && (forall i:nat | i < |path.node.children| && i != r
       :: path.node.children[i] == newNode.children[i])
      && ValidSplit(path.Subpath(), newNode.children[r]))
    && (path.depth == 0 ==>
      && path.node.SplitChildOfIndex(newNode, path.key, r))
  }

  predicate Split(v: Variables, v': Variables, lbl: TransitionLabel, path: Path)
  {
    && lbl.InternalLabel?
    && v.WF()
    && path.node == v.root // start from root
    && ValidSplit(path, v'.root)
  }

  // public:

  predicate Init(v: Variables)
  {
    && v.root == Leaf([], [])
  }

  datatype Step =
    | QueryStep()
    | InsertStep()
    | GrowStep()
    | SplitStep(path: Path)

  predicate NextStep(v: Variables, v': Variables, lbl: TransitionLabel, step: Step)
  {
    && match step {
        case QueryStep() => Query(v, v', lbl)
        case InsertStep() => Insert(v, v', lbl)
        case GrowStep() => Grow(v, v', lbl)
        case SplitStep(path) => Split(v, v', lbl, path)
      }
  }

  predicate Next(v: Variables, v': Variables, lbl: TransitionLabel) {
    exists step: Step :: NextStep(v, v', lbl, step)
  }
}
