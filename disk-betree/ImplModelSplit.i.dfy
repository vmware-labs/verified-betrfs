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
  import opened BucketWeights
  import opened Bounds
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
    var splitBucket := SplitBucketLeft(node.buckets[cLeft], pivot);
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
    var splitBucket := SplitBucketLeft(node.buckets[cLeft], pivot);
    var leftBuckets := node.buckets[.. cLeft] + [splitBucket];
    Pivots.WFSlice(node.pivotTable, 0, cLeft);
    WFSplitBucketListLeft(node.buckets, node.pivotTable, cLeft, pivot);
    WeightSplitBucketListLeft(node.buckets, node.pivotTable, cLeft, pivot);
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
    var splitBucket := SplitBucketRight(node.buckets[cRight], pivot);
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
    var splitBucket := SplitBucketRight(node.buckets[cRight], pivot);
    var rightBuckets := [splitBucket] + node.buckets[cRight + 1 ..];
    Pivots.WFSuffix(node.pivotTable, cRight);
    WFSplitBucketListRight(node.buckets, node.pivotTable, cRight, pivot);
    WeightSplitBucketListRight(node.buckets, node.pivotTable, cRight, pivot);
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
    WFBucketListSplitLeft(child.buckets, child.pivotTable, num_children_left);
    WFBucketListSplitRight(child.buckets, child.pivotTable, num_children_left);
    WeightBucketListSlice(child.buckets, 0, num_children_left);
    WeightBucketListSuffix(child.buckets, num_children_left);
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

  function {:opaque} SplitParent(fused_parent: Node, pivot: Key, slot_idx: int, left_childref: BT.G.Reference, right_childref: BT.G.Reference)
  : (res : Node)
  requires WFNode(fused_parent)
  requires 0 <= slot_idx < |fused_parent.buckets|
  requires fused_parent.children.Some?
  {
    var pivots := Sequences.insert(fused_parent.pivotTable, pivot, slot_idx);
    var buckets := SplitBucketInList(fused_parent.buckets, slot_idx, pivot);
    Node(
      pivots,
      Some(replace1with2(fused_parent.children.value, left_childref, right_childref, slot_idx)),
      buckets
    )
  }

  lemma SplitParentCorrect(parentref: BT.G.Reference, fused_parent: Node, pivot: Key, slot_idx: int, left_childref: BT.G.Reference, right_childref: BT.G.Reference)
  requires WFNode(fused_parent)
  requires BT.WFNode(INode(fused_parent))
  requires 0 <= slot_idx < |fused_parent.buckets|
  requires PivotsLib.PivotInsertable(fused_parent.pivotTable, slot_idx, pivot)
  requires |fused_parent.buckets| <= MaxNumChildren() - 1
  requires fused_parent.children.Some?
  ensures
    && var res := SplitParent(fused_parent, pivot, slot_idx, left_childref, right_childref);
    && WFNode(res)
    && var inode := INode(fused_parent);
    && var inode' := INode(res);
    && inode' == BT.SplitParent(inode, pivot, slot_idx, left_childref, right_childref)
    && WeightBucketList(res.buckets) == WeightBucketList(fused_parent.buckets)
  {
    reveal_SplitParent();
    var res := SplitParent(fused_parent, pivot, slot_idx, left_childref, right_childref);
    WFSplitBucketInList(fused_parent.buckets, slot_idx, pivot, fused_parent.pivotTable);
    WeightSplitBucketInList(fused_parent.buckets, slot_idx, pivot);
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

  function {:opaque} doSplit(k: Constants, s: Variables, parentref: BT.G.Reference, childref: BT.G.Reference, slot: int)
  : (s': Variables)
  requires s.Ready?
  requires Inv(k, s)
  requires childref in s.ephemeralIndirectionTable
  requires parentref in s.ephemeralIndirectionTable
  requires childref in s.cache
  requires parentref in s.cache
  requires s.cache[parentref].children.Some?
  requires 0 <= slot < |s.cache[parentref].children.value|
  requires s.cache[parentref].children.value[slot] == childref
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
      var fused_child := s.cache[childref];

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

            var s1 := writeBookkeeping(k, s, left_childref.value, left_child.children);
            var s2 := writeBookkeeping(k, s1, right_childref.value, right_child.children);
            var s3 := writeBookkeeping(k, s2, parentref, split_parent.children);
            var s' := s3.(cache := s.cache
                [left_childref.value := left_child]
                [right_childref.value := right_child]
                [parentref := split_parent]);
            s'
          )
        )
      )
    )
  }

  lemma doSplitCorrect(k: Constants, s: Variables, parentref: BT.G.Reference, childref: BT.G.Reference, slot: int)
  requires s.Ready?
  requires Inv(k, s)
  requires childref in s.ephemeralIndirectionTable
  requires parentref in s.ephemeralIndirectionTable
  requires childref in s.cache
  requires parentref in s.cache
  requires s.cache[parentref].children.Some?
  requires |s.cache[parentref].buckets| <= MaxNumChildren() - 1
  requires 0 <= slot < |s.cache[parentref].children.value|
  requires s.cache[parentref].children.value[slot] == childref
  requires TotalCacheSize(s) <= MaxCacheSize() - 2
  ensures var s' := doSplit(k, s, parentref, childref, slot);
    && WFVars(s')
    && M.Next(Ik(k), IVars(s), IVars(s'), UI.NoOp, D.NoDiskOp)
  {
    var s' := doSplit(k, s, parentref, childref, slot);
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
      var fused_child := s.cache[childref];

      assume childref != BT.G.Root(); // TODO

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
            reveal_SplitParent();

            reveal_writeBookkeeping();
            var s1 := writeWithNode(k, s, left_childref.value, left_child);
            var s2 := writeWithNode(k, s1, right_childref.value, right_child);
            var s3 := writeWithNode(k, s2, parentref, split_parent);
            assert s' == s3;

            lemmaSplitChild(child, num_children_left);
            SplitParentCorrect(parentref, fused_parent, pivot, slot, left_childref.value, right_childref.value);

            lemmaBlockPointsToValidReferences(k, s, childref);
            assert BC.BlockPointsToValidReferences(INode(fused_child), IIndirectionTable(s.ephemeralIndirectionTable).graph);
            lemmaSplitChildValidReferences(INode(fused_child), INode(child), num_children_left, IIndirectionTable(s.ephemeralIndirectionTable).graph, lbound, ubound);

            writeNewRefIsAlloc(k, s, left_childref.value, left_child);
            writeNewRefIsAlloc(k, s1, right_childref.value, right_child);

            var inodeFusedParent := INode(fused_parent);
            var inodeSplitParent := INode(split_parent);

            lemmaBlockPointsToValidReferences(k, s, parentref);
            assert BC.BlockPointsToValidReferences(inodeFusedParent, IIndirectionTable(s2.ephemeralIndirectionTable).graph);
            lemmaSplitParentValidReferences(inodeFusedParent, pivot, slot, left_childref.value, right_childref.value, IIndirectionTable(s2.ephemeralIndirectionTable).graph);

            reveal_SplitChildLeft();
            reveal_SplitChildRight();

            assert INode(child) == BT.CutoffNode(INode(fused_child), lbound, ubound);
            assert 1 <= num_children_left < |child.buckets|;

            var splitStep := BT.NodeFusion(
              parentref,
              childref,
              left_childref.value,
              right_childref.value,
              inodeFusedParent,
              inodeSplitParent,
              INode(fused_child),
              INode(left_child),
              INode(right_child),
              slot,
              num_children_left,
              pivot
            );

            LruModel.LruUse(s2.lru, parentref);
            assert LruModel.WF(s'.lru);

            assert splitStep.num_children_left == num_children_left;
            assert splitStep.fused_child == INode(fused_child);

            assert left_childref.value != right_childref.value;
            assert BT.ValidSplit(splitStep);
            var step := BT.BetreeSplit(splitStep);
            var ops := [
              BT.G.AllocOp(left_childref.value, INode(left_child)),
              BT.G.AllocOp(right_childref.value, INode(right_child)),
              BT.G.WriteOp(parentref, inodeSplitParent)
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
