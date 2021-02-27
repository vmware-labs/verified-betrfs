// Copyright 2018-2021 VMware, Inc.
// SPDX-License-Identifier: MIT

  // method SplitChildOfIndex(linear node: Node, childidx: uint64)
  //   returns (linear splitNode: Node)
  //   requires WF(node)
  //   requires node.Index?
  //   requires !Full(node)
  //   requires 0 <= childidx as nat < |node.children|
  //   requires Full(node.children[childidx as nat]);
  //   ensures splitNode.Index?
  //   ensures Model.SplitChildOfIndex(node, splitNode, childidx as int)
  //   ensures WF(splitNode)
  //   ensures !Full(splitNode.children[childidx as nat])
  //   ensures !Full(splitNode.children[childidx as nat + 1])
  //   ensures splitNode.pivots[childidx] in Model.AllKeys(node.children[childidx as nat])
  //   ensures Height(splitNode) <= Height(node)
  // {
  //   linear var Index(pivots, children) := node;

  //   linear var origChild;
  //   children, origChild := lseq_take(children, childidx);

  //   linear var left, right;
  //   var pivot;
  //   left, right, pivot := SplitNode(origChild);
  //   pivots := InsertSeq(pivots, pivot, childidx);
  //   children := lseq_give(children, childidx, left);
  //   children := InsertLSeq(children, right, childidx + 1);
  //   splitNode := Model.Index(pivots, children);
  //   Model.SplitChildOfIndexPreservesWF(node, splitNode, childidx as int);

  //   // Every new child is shorter than some old child.
  //   ghost var wit := seq(|splitNode.children|, i requires 0<=i<|splitNode.children| =>
  //     if i <= childidx as nat then i else i-1);
  //   SeqMaxCorrespondence(IndexHeights(node), IndexHeights(splitNode), wit);
  //   assert Height(splitNode) <= Height(node) by { reveal_Height(); }
  // }

  method SplitChildOfIndex(write node: Node, childidx: uint64)
    requires WF(node)
    requires node.Index?
    requires !Full(node)
    requires 0 <= childidx as nat < |node.children|
    requires Full(node.children[childidx as nat]);
    ensures node.Index?
    ensures Model.SplitChildOfIndex(old(node), node, childidx as int)
    ensures WF(node)
    ensures !Full(node.children[childidx as nat])
    ensures !Full(node.children[childidx as nat + 1])
    ensures node.pivots[childidx] in Model.AllKeys(old(node).children[childidx as nat])
    ensures Height(node) <= Height(old(node))
  {
    linear var origChild := lseq_take(write node.children, childidx);

    linear var left, right;
    var pivot;
    left, right, pivot := SplitNode(write origChild);
    InsertSeq(write node.pivots, pivot, childidx);
    lseq_give(write node.children, childidx, left);
    InsertLSeq(write node.children, right, childidx + 1);

    Model.SplitChildOfIndexPreservesWF(old(node), node, childidx as int);

    // Every new child is shorter than some old child.
    ghost var wit := seq(|node.children|, i requires 0<=i<|node.children| =>
      if i <= childidx as nat then i else i-1);
    SeqMaxCorrespondence(IndexHeights(old(node)), IndexHeights(node), wit);
    assert Height(node) <= Height(old(splitNode)) by { reveal_Height(); }
  }

  method InsertIndex(write node: Node, key: Key, value: Value)
    returns (oldvalue: Option<Value>)
    requires WF(node)
    requires node.Index?
    requires !Full(node)
    ensures WF(node)
    ensures Model.Interpretation(node) == Model.Interpretation(old(node))[key := value]
    ensures Model.AllKeys(node) <= Model.AllKeys(old(node)) + {key}  // shouldn't this be ==?
    ensures oldvalue == MapLookupOption(Interpretation(old(node)), key)
    decreases Height(node), 1
  {
    var childidx := Route(node.pivots, key);
    if Full(lseq_peek(node.children, childidx)) {
      SplitChildOfIndex(write node, childidx);

      Model.SplitChildOfIndexPreservesWF(old(node), node, childidx as nat);
      Model.SplitChildOfIndexPreservesInterpretation(old(node), node, childidx as nat);
      Model.SplitChildOfIndexPreservesAllKeys(old(node), node, childidx as nat);
      assert node.pivots[childidx] in Model.AllKeys(node) by { Model.reveal_AllKeys(); }

      var t: int32 := Model.KeysImpl.cmp(seq_get(node.pivots, childidx), key);
      if  t <= 0 {
        childidx := childidx + 1;
        forall i | childidx as int - 1 < i < |node.pivots|
          ensures Model.Keys.lt(key, node.pivots[i])
        {
          assert node.pivots[i] == old(node).pivots[i-1];
        }
      }
      Model.Keys.LargestLteIsUnique(node.pivots, key, childidx as int - 1);
      assert Interpretation(node) == Interpretation(old(node));
    }
    ghost var preparedNode := node;
    assert Height(preparedNode) <= Height(node);
    assert Interpretation(preparedNode) == Interpretation(node);

    linear var childNode := lseq_take(write node.children, childidx);
    ghost var childNodeSnapshot := childNode;
    assert Height(childNode) < Height(preparedNode) by { ChildrenAreShorter(preparedNode, childidx as nat); }
    assert Height(childNode) < Height(node);
    oldvalue := InsertNode(write childNode, key, value);
    lseq_give(write node.children, childidx, childNode); // goes away with polonius

    Model.RecursiveInsertIsCorrect(preparedNode, key, value, childidx as int, node, node.children[childidx as int]);
    if oldvalue.Some? {
      Model.InterpretationDelegation(preparedNode, key);
    } else {
      Model.reveal_Interpretation();
    }
  }
