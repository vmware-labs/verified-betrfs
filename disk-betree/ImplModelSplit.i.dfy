include "ImplModelCache.i.dfy"

module ImplModelSplit { 
  import opened ImplModel
  import opened ImplModelIO
  import opened ImplModelCache

  import opened Options
  import opened Maps
  import opened Sequences
  import opened Sets

  import opened BucketsLib
  import PivotsLib

  import opened NativeTypes

  function {:opaque} CutoffNodeAndKeepLeft(node: Node, pivot: Key) : (node': Node)
  requires WFNode(node)
  ensures |node'.buckets| == |node'.pivotTable| + 1
  ensures node'.children.Some? ==> |node'.buckets| == |node'.children.value|
  {
    var cLeft := Pivots.CutoffForLeft(node.pivotTable, pivot);
    var leftPivots := node.pivotTable[.. cLeft];
    var leftChildren := if node.children.Some? then Some(node.children.value[.. cLeft + 1]) else None;
    var splitBucket := KMTable.splitLeft(node.buckets[cLeft], pivot);
    var leftBuckets := node.buckets[.. cLeft] + [splitBucket];
    Node(leftPivots, leftChildren, leftBuckets)
  }

  lemma CutoffNodeAndKeepLeftCorrect(node: Node, pivot: Key)
  requires WFNode(node)
  requires BT.WFNode(INode(node))
  ensures var node' := CutoffNodeAndKeepLeft(node, pivot);
    && WFNode(node')
    && INode(node') == BT.CutoffNodeAndKeepLeft(INode(node), pivot)
  {
    reveal_CutoffNodeAndKeepLeft();
    BT.reveal_CutoffNodeAndKeepLeft();
    var cLeft := Pivots.CutoffForLeft(node.pivotTable, pivot);
    var leftPivots := node.pivotTable[.. cLeft];
    var leftChildren := if node.children.Some? then Some(node.children.value[.. cLeft + 1]) else None;
    var splitBucket := KMTable.splitLeft(node.buckets[cLeft], pivot);
    KMTable.splitLeftCorrect(node.buckets[cLeft], pivot);
    var leftBuckets := node.buckets[.. cLeft] + [splitBucket];
    Pivots.WFSlice(node.pivotTable, 0, cLeft);
    KMTable.Islice(node.buckets, 0, cLeft);
    KMTable.IPopBack(node.buckets[.. cLeft], splitBucket);
    WFSplitBucketListLeft(KMTable.ISeq(node.buckets), node.pivotTable, cLeft, pivot);
  }

  function {:opaque} CutoffNodeAndKeepRight(node: Node, pivot: Key)
  : (node': Node)
  requires WFNode(node)
  ensures |node'.buckets| == |node'.pivotTable| + 1
  ensures node'.children.Some? ==> |node'.buckets| == |node'.children.value|
  {
    var cRight := Pivots.CutoffForRight(node.pivotTable, pivot);
    var rightPivots := node.pivotTable[cRight ..];
    var rightChildren := if node.children.Some? then Some(node.children.value[cRight ..]) else None;
    var splitBucket := KMTable.splitRight(node.buckets[cRight], pivot);
    var rightBuckets := [splitBucket] + node.buckets[cRight + 1 ..];
    Node(rightPivots, rightChildren, rightBuckets)
  }

  lemma CutoffNodeAndKeepRightCorrect(node: Node, pivot: Key)
  requires WFNode(node)
  requires BT.WFNode(INode(node))
  ensures var node' := CutoffNodeAndKeepRight(node, pivot);
    && WFNode(node')
    && INode(node') == BT.CutoffNodeAndKeepRight(INode(node), pivot)
  {
    reveal_CutoffNodeAndKeepRight();
    BT.reveal_CutoffNodeAndKeepRight();
    var cRight := Pivots.CutoffForRight(node.pivotTable, pivot);
    var rightPivots := node.pivotTable[cRight ..];
    var rightChildren := if node.children.Some? then Some(node.children.value[cRight ..]) else None;
    var splitBucket := KMTable.splitRight(node.buckets[cRight], pivot);
    KMTable.splitRightCorrect(node.buckets[cRight], pivot);
    var rightBuckets := [splitBucket] + node.buckets[cRight + 1 ..];
    Pivots.WFSuffix(node.pivotTable, cRight);
    KMTable.Isuffix(node.buckets, cRight + 1);
    KMTable.IPopFront(splitBucket, node.buckets[cRight + 1 ..]);
    WFSplitBucketListRight(KMTable.ISeq(node.buckets), node.pivotTable, cRight, pivot);
  }

  function {:opaque} CutoffNode(node: Node, lbound: Option<Key>, rbound: Option<Key>)
  : (node' : Node)
  requires WFNode(node)
  ensures |node'.buckets| == |node'.pivotTable| + 1
  ensures node'.children.Some? ==> |node'.buckets| == |node'.children.value|
  {
    match lbound {
      case None => (
        match rbound {
          case None => (
            node
          )
          case Some(rbound) => (
            CutoffNodeAndKeepLeft(node, rbound)
          )
        }
      )
      case Some(lbound) => (
        match rbound {
          case None => (
            CutoffNodeAndKeepRight(node, lbound)
          )
          case Some(rbound) => (
            var node1 := CutoffNodeAndKeepLeft(node, rbound);
            CutoffNodeAndKeepLeftCorrect(node, rbound); // we need WFNode(node1)
            CutoffNodeAndKeepRight(node1, lbound)
          )
        }
      )
    }
  }

  lemma CutoffNodeCorrect(node: Node, lbound: Option<Key>, rbound: Option<Key>)
  requires WFNode(node)
  requires BT.WFNode(INode(node))
  ensures var node' := CutoffNode(node, lbound, rbound);
    && WFNode(node')
    && INode(node') == BT.CutoffNode(INode(node), lbound, rbound)
  {
    reveal_CutoffNode();
    BT.reveal_CutoffNode();

    match lbound {
      case None => {
        match rbound {
          case None => {
          }
          case Some(rbound) => {
            CutoffNodeAndKeepLeftCorrect(node, rbound);
          }
        }
      }
      case Some(lbound) => {
        match rbound {
          case None => {
            CutoffNodeAndKeepRightCorrect(node, lbound);
          }
          case Some(rbound) => {
            var node1 := CutoffNodeAndKeepLeft(node, rbound);
            CutoffNodeAndKeepLeftCorrect(node, rbound);
            CutoffNodeAndKeepRightCorrect(node1, lbound);
          }
        }
      }
    }
  }

  function method {:opaque} SplitChildLeft(child: Node, num_children_left: int) : Node
  requires 0 <= num_children_left - 1 <= |child.pivotTable|
  requires child.children.Some? ==> 0 <= num_children_left <= |child.children.value|
  requires 0 <= num_children_left <= |child.buckets|
  {
    Node(
      child.pivotTable[ .. num_children_left - 1 ],
      if child.children.Some? then Some(child.children.value[ .. num_children_left ]) else None,
      child.buckets[ .. num_children_left ]
    )
  }

  function method {:opaque} SplitChildRight(child: Node, num_children_left: int) : Node
  requires 0 <= num_children_left <= |child.pivotTable|
  requires child.children.Some? ==> 0 <= num_children_left <= |child.children.value|
  requires 0 <= num_children_left <= |child.buckets|
  {
    Node(
      child.pivotTable[ num_children_left .. ],
      if child.children.Some? then Some(child.children.value[ num_children_left .. ]) else None,
      child.buckets[ num_children_left .. ]
    )
  }

  lemma lemmaSplitChild(child: Node, num_children_left: int)
  requires WFNode(child)
  requires BT.WFNode(INode(child))
  requires 1 <= num_children_left <= |child.buckets| - 1
  ensures WFNode(SplitChildLeft(child, num_children_left))
  ensures WFNode(SplitChildRight(child, num_children_left))
  ensures INode(SplitChildLeft(child, num_children_left)) == BT.SplitChildLeft(INode(child), num_children_left)
  ensures INode(SplitChildRight(child, num_children_left)) == BT.SplitChildRight(INode(child), num_children_left)
  {
    reveal_SplitChildLeft();
    reveal_SplitChildRight();
    Pivots.WFSlice(child.pivotTable, 0, num_children_left - 1);
    Pivots.WFSuffix(child.pivotTable, num_children_left);
    KMTable.Islice(child.buckets, 0, num_children_left);
    KMTable.Isuffix(child.buckets, num_children_left);
    WFBucketListSplitLeft(KMTable.ISeq(child.buckets), child.pivotTable, num_children_left);
    WFBucketListSplitRight(KMTable.ISeq(child.buckets), child.pivotTable, num_children_left);
    assert WFNode(SplitChildRight(child, num_children_left));
    assert WFNode(SplitChildLeft(child, num_children_left));
  }

  // TODO can we get BetreeBlockCache to ensure that will be true generally whenever taking a betree step?
  // This sort of proof logic shouldn't have to be in the implementation.
  lemma lemmaSplitChildValidReferences(child1: BT.G.Node, child: BT.G.Node, num_children_left: int, graph: map<BT.G.Reference, seq<BT.G.Reference>>, lbound: Option<Key>, rbound: Option<Key>)
  requires BT.WFNode(child1)
  requires BT.WFNode(child)
  requires 1 <= num_children_left <= |child.buckets| - 1
  requires BC.BlockPointsToValidReferences(child1, graph);
  requires child == BT.CutoffNode(child1, lbound, rbound);
  ensures BC.BlockPointsToValidReferences(BT.SplitChildLeft(child, num_children_left), graph);
  ensures BC.BlockPointsToValidReferences(BT.SplitChildRight(child, num_children_left), graph);
  {
  }

  function SplitParent(fused_parent: Node, pivot: Key, slot_idx: int, left_childref: BT.G.Reference, right_childref: BT.G.Reference)
  : (res : Node)
  requires WFNode(fused_parent)
  requires 0 <= slot_idx < |fused_parent.buckets|
  requires fused_parent.children.Some?
  {
    var pivots := Sequences.insert(fused_parent.pivotTable, pivot, slot_idx);
    var buckets := KMTable.splitKMTableInList(fused_parent.buckets, slot_idx, pivot);
    Node(
      pivots,
      Some(replace1with2(fused_parent.children.value, left_childref, right_childref, slot_idx)),
      buckets
    )
  }

  lemma SplitParentCorrect(fused_parent: Node, pivot: Key, slot_idx: int, left_childref: BT.G.Reference, right_childref: BT.G.Reference)
  requires WFNode(fused_parent)
  requires BT.WFNode(INode(fused_parent))
  requires 0 <= slot_idx < |fused_parent.buckets|
  requires PivotsLib.PivotInsertable(fused_parent.pivotTable, slot_idx, pivot)
  requires fused_parent.children.Some?
  ensures var res := SplitParent(fused_parent, pivot, slot_idx, left_childref, right_childref);
    && WFNode(res)
    && INode(res) == BT.SplitParent(INode(fused_parent), pivot, slot_idx, left_childref, right_childref)
  {
    KMTable.splitKMTableInListCorrect(fused_parent.buckets, slot_idx, pivot);
    var res := SplitParent(fused_parent, pivot, slot_idx, left_childref, right_childref);
    WFSplitBucketInList(KMTable.ISeq(fused_parent.buckets), slot_idx, pivot, fused_parent.pivotTable);
    assert WFNode(res);
    assert INode(res) == BT.SplitParent(INode(fused_parent), pivot, slot_idx, left_childref, right_childref);
  }

  lemma lemmaSplitParentValidReferences(fused_parent: BT.G.Node, pivot: Key, slot_idx: int, left_childref: BT.G.Reference, right_childref: BT.G.Reference, graph: map<BT.G.Reference, seq<BT.G.Reference>>)
  requires BT.WFNode(fused_parent)
  requires 0 <= slot_idx < |fused_parent.buckets|
  requires fused_parent.children.Some?
  requires BC.BlockPointsToValidReferences(fused_parent, graph);
  requires left_childref in graph
  requires right_childref in graph
  ensures BC.BlockPointsToValidReferences(BT.SplitParent(fused_parent, pivot, slot_idx, left_childref, right_childref), graph);
  {
    var split_parent := BT.SplitParent(fused_parent, pivot, slot_idx, left_childref, right_childref);
    forall r | r in BT.G.Successors(split_parent)
    ensures r in graph
    {
      assert BC.BlockPointsToValidReferences(fused_parent, graph);
      var idx :| 0 <= idx < |split_parent.children.value| && split_parent.children.value[idx] == r;
      if (idx < slot_idx) {
        assert r == fused_parent.children.value[idx];
        assert r in graph;
      } else if (idx == slot_idx) {
        assert r == left_childref;
        assert r in graph;
      } else if (idx == slot_idx + 1) {
        assert r == right_childref;
        assert r in graph;
      } else {
        assert r == fused_parent.children.value[idx-1];
        assert r in graph;
      }
    }
  }

  function {:opaque} doSplit(k: Constants, s: Variables, parentref: BT.G.Reference, ref: BT.G.Reference, slot: int)
  : (s': Variables)
  requires s.Ready?
  requires Inv(k, s)
  requires ref in s.ephemeralIndirectionTable
  requires parentref in s.ephemeralIndirectionTable
  requires ref in s.cache
  requires parentref in s.cache
  requires s.cache[parentref].children.Some?
  requires 0 <= slot < |s.cache[parentref].children.value|
  requires s.cache[parentref].children.value[slot] == ref
  {
    if (
      && s.frozenIndirectionTable.Some?
      && parentref in s.frozenIndirectionTable.value
      && var entry := s.frozenIndirectionTable.value[parentref];
      && var (loc, _) := entry;
      && loc.None?
    ) then (
      s
    ) else (
      var fused_parent := s.cache[parentref];
      var fused_child := s.cache[ref];

      var lbound := (if slot > 0 then Some(fused_parent.pivotTable[slot - 1]) else None);
      var ubound := (if slot < |fused_parent.pivotTable| then Some(fused_parent.pivotTable[slot]) else None);
      var child := CutoffNode(fused_child, lbound, ubound);

      if (|child.pivotTable| == 0) then (
        // TODO there should be an operation which just
        // cuts off the node and doesn't split it.
        s
      ) else (
        var left_childref := getFreeRef(s);
        if left_childref.None? then (
          s
        ) else (
          var right_childref := getFreeRef2(s, left_childref.value);
          if right_childref.None? then (
            s
          ) else (
            var num_children_left := |child.buckets| / 2;
            var pivot := child.pivotTable[num_children_left - 1];

            var left_child := SplitChildLeft(child, num_children_left);
            var right_child := SplitChildRight(child, num_children_left);
            var split_parent := SplitParent(fused_parent, pivot, slot, left_childref.value, right_childref.value);

            var s1 := write(k, s, left_childref.value, left_child);
            var s2 := write(k, s1, right_childref.value, right_child);
            var s' := write(k, s2, parentref, split_parent);
            s'
          )
        )
      )
    )
  }

  lemma doSplitCorrect(k: Constants, s: Variables, parentref: BT.G.Reference, ref: BT.G.Reference, slot: int)
  requires s.Ready?
  requires Inv(k, s)
  requires ref in s.ephemeralIndirectionTable
  requires parentref in s.ephemeralIndirectionTable
  requires ref in s.cache
  requires parentref in s.cache
  requires s.cache[parentref].children.Some?
  requires 0 <= slot < |s.cache[parentref].children.value|
  requires s.cache[parentref].children.value[slot] == ref
  requires s.rootBucket == map[] // FIXME we don't actually need this unless paretnref is root
  ensures var s' := doSplit(k, s, parentref, ref, slot);
    && WFVars(s')
    && M.Next(Ik(k), IVars(s), IVars(s'), UI.NoOp, D.NoDiskOp)
  {
    reveal_doSplit();

    if (
      && s.frozenIndirectionTable.Some?
      && parentref in s.frozenIndirectionTable.value
      && var entry := s.frozenIndirectionTable.value[parentref];
      && var (loc, _) := entry;
      && loc.None?
    ) {
      assert noop(k, IVars(s), IVars(s));
    } else {
      var fused_parent := s.cache[parentref];
      var fused_child := s.cache[ref];

      INodeRootEqINodeForEmptyRootBucket(fused_parent);
      INodeRootEqINodeForEmptyRootBucket(fused_child);

      var lbound := (if slot > 0 then Some(fused_parent.pivotTable[slot - 1]) else None);
      var ubound := (if slot < |fused_parent.pivotTable| then Some(fused_parent.pivotTable[slot]) else None);
      var child := CutoffNode(fused_child, lbound, ubound);
      CutoffNodeCorrect(fused_child, lbound, ubound);

      if (|child.pivotTable| == 0) {
        // TODO there should be an operation which just
        // cuts off the node and doesn't split it.
        assert noop(k, IVars(s), IVars(s));
      } else {
        var left_childref := getFreeRef(s);
        if left_childref.None? {
          assert noop(k, IVars(s), IVars(s));
        } else {
          var right_childref := getFreeRef2(s, left_childref.value);
          if right_childref.None? {
            assert noop(k, IVars(s), IVars(s));
          } else {
            var num_children_left := |child.buckets| / 2;
            var pivot := child.pivotTable[num_children_left - 1];
            PivotsLib.PivotNotMinimum(child.pivotTable, num_children_left - 1);

            var left_child := SplitChildLeft(child, num_children_left);
            var right_child := SplitChildRight(child, num_children_left);
            var split_parent := SplitParent(fused_parent, pivot, slot, left_childref.value, right_childref.value);

            reveal_write();
            var s1 := write(k, s, left_childref.value, left_child);
            var s2 := write(k, s1, right_childref.value, right_child);
            var s' := write(k, s2, parentref, split_parent);

            lemmaSplitChild(child, num_children_left);
            SplitParentCorrect(fused_parent, pivot, slot, left_childref.value, right_childref.value);

            lemmaBlockPointsToValidReferences(k, s, ref);
            assert BC.BlockPointsToValidReferences(INode(fused_child), IIndirectionTable(s.ephemeralIndirectionTable).graph);
            lemmaSplitChildValidReferences(INode(fused_child), INode(child), num_children_left, IIndirectionTable(s.ephemeralIndirectionTable).graph, lbound, ubound);

            writeNewRefIsAlloc(k, s, left_childref.value, left_child);
            writeNewRefIsAlloc(k, s1, right_childref.value, right_child);

            lemmaBlockPointsToValidReferences(k, s, parentref);
            assert BC.BlockPointsToValidReferences(INode(fused_parent), IIndirectionTable(s2.ephemeralIndirectionTable).graph);
            lemmaSplitParentValidReferences(INode(fused_parent), pivot, slot, left_childref.value, right_childref.value, IIndirectionTable(s2.ephemeralIndirectionTable).graph);

            writeCorrect(k, s2, parentref, split_parent);
          
            reveal_SplitChildLeft();
            reveal_SplitChildRight();

            assert WFBuckets(child.buckets);
            assert INode(child) == BT.CutoffNode(INode(fused_child), lbound, ubound);
            assert 1 <= num_children_left < |child.buckets|;

            var splitStep := BT.NodeFusion(
              parentref,
              ref,
              left_childref.value,
              right_childref.value,
              INode(fused_parent),
              INode(split_parent),
              INode(fused_child),
              INode(left_child),
              INode(right_child),
              slot,
              num_children_left,
              pivot
            );

            assert splitStep.num_children_left == num_children_left;
            assert splitStep.fused_child == INode(fused_child);

            assert left_childref.value != right_childref.value;
            assert BT.ValidSplit(splitStep);
            var step := BT.BetreeSplit(splitStep);
            var ops := [
              BT.G.AllocOp(left_childref.value, INode(left_child)),
              BT.G.AllocOp(right_childref.value, INode(right_child)),
              BT.G.WriteOp(parentref, INode(split_parent))
            ];
            assert ops == BT.BetreeStepOps(step);
            BC.MakeTransaction3(Ik(k), IVars(s), IVars(s1), IVars(s2), IVars(s'), ops);
            assert stepsBetree(k, IVars(s), IVars(s'), UI.NoOp, step);
          }
        }
      }
    }
  }
}
