// Copyright 2018-2021 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, and University of Washington
// SPDX-License-Identifier: BSD-2-Clause

include "../../lib/Base/Option.s.dfy"
include "../../lib/Base/KeyType.s.dfy"
include "../../Spec/Message.s.dfy"
include "../../lib/Buckets/BoundedPivotsLib.i.dfy"

module PagedBranchTree {
  import opened Options
  import opened ValueMessage
  import opened KeyType
  import BoundedPivotsLib
  import opened Sequences

  datatype Node =
      Index(pivots: BoundedPivotsLib.PivotTable, children: seq<Node>)
    | Leaf(entries: map<Key, Message>)
  {
    predicate WF()
    {
      && Index? ==> (
          && |children| == |pivots| + 1
          && (forall i | 0 <= i < |children| :: children[i].WF())
        )
    }

    function Grow() : Node
    {
      Index([], [this])
    }

    function RightHeight() : nat
      requires WF()
    {
      if Leaf? then
        0
      else
        1 + Last(children).RightHeight()
    }

    predicate CanGraft(height: nat)
      requires WF()
    {
      0 < height <= RightHeight()
    }

    function Graft(stalk: Node, newpivot: Key, height: nat) : Node
      requires WF()
      requires CanGraft(height)
    {
      assert this.Index?;
      if height == RightHeight() then
        this.(pivots := pivots + [BoundedPivotsLib.Keyspace.Element(newpivot)], children := children + [stalk])
      else
        this.(children := children[|children| - 1 := Last(children).Graft(stalk, newpivot, height)])
    }
  }

  predicate Keylt(a: Key, b: Key)
  {
    BoundedPivotsLib.Keyspace.lt(
      BoundedPivotsLib.Keyspace.Element(a),
      BoundedPivotsLib.Keyspace.Element(b))
  }

  const EmptyTree := Leaf(map[])

  datatype Variables = Variables(root: Node, stalk: Option<Node>, largestKey: Option<Key>)
  {
    predicate WF()
    {
      && (largestKey == None <==> root == EmptyTree)
      && root.WF()
      && (stalk.Some? ==> stalk.value.WF())
    }
  }

  predicate Init(v:Variables)
  {
    v == Variables(EmptyTree, None, None)
  }

  function TreeAppend(node: Node, k: Key, m: Message) : Node
    requires node.WF()
  {
    if node.Leaf? then
      Leaf(node.entries[k := m])
    else
      Index(node.pivots, node.children[ |node.children| -1  := TreeAppend(Last(node.children), k, m)])
  }

  predicate Append(v:Variables, v': Variables, k: Key, m: Message)
  {
    && v.WF()
    && (v.largestKey.None? || Keylt(v.largestKey.value, k))
    && v' == v.(root := TreeAppend(v.root, k, m), largestKey := Some(k))
  }

  predicate Sprout(v:Variables, v': Variables)
  {
    && v.WF()
    && v.stalk.None?
    && v' == v.(stalk := Some(EmptyTree))
  }

  predicate GrowStalk(v:Variables, v': Variables)
  {
    && v.WF()
    && v.stalk.Some?
    && v' == v.(stalk := Some(v.stalk.value.Grow()))
  }

  predicate GrowTree(v:Variables, v': Variables)
  {
    && v.WF()
    && v' == v.(root := v.root.Grow())
  }

  predicate Graft(v:Variables, v': Variables, newpivot: Key, height: nat)
  {
    && v.WF()
    && v.root.CanGraft(height)
    && v.stalk.Some?
    && v' == v.(root := v.root.Graft(v.stalk.value, newpivot, height), stalk := None)
  }

  predicate Query(v:Variables, v': Variables, k: Key, m: Option<Message>)
  {
    false
  }
}
