include "BookkeepingModel.i.dfy"

module SplitModel { 
  import opened StateModel
  import opened IOModel
  import opened BookkeepingModel

  import opened Options
  import opened Maps
  import opened Sequences
  import opened Sets

  import opened BucketsLib
  import opened BucketWeights
  import opened Bounds
  import PivotsLib
  import opened KeyType

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

  lemma lemmaChildrenConditionsCutoffNode(k: Constants, s: Variables, 
      node: Node, lbound: Option<Key>, rbound: Option<Key>)
  requires WFNode(node)
  requires s.Ready?
  requires ChildrenConditions(k, s, node.children)
  ensures ChildrenConditions(k, s, CutoffNode(node, lbound, rbound).children)
  {
    reveal_CutoffNode();
    reveal_CutoffNodeAndKeepLeft();
    reveal_CutoffNodeAndKeepRight();
  }

  function {:opaque} SplitChildLeft(child: Node, num_children_left: int) : Node
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

  function {:opaque} SplitChildRight(child: Node, num_children_left: int) : Node
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

  lemma lemmaChildrenConditionsSplitChild(
      k: Constants, s: Variables, child: Node, num_children_left: int)
  requires SplitChildLeft.requires(child, num_children_left)
  requires SplitChildRight.requires(child, num_children_left)
  requires s.Ready?
  requires ChildrenConditions(k, s, child.children)
  ensures ChildrenConditions(k, s, SplitChildLeft(child, num_children_left).children)
  ensures ChildrenConditions(k, s, SplitChildRight(child, num_children_left).children)
  {
    reveal_SplitChildLeft();
    reveal_SplitChildRight();
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

  function {:opaque} SplitParent(fused_parent: Node, pivot: Key, slot: int, left_childref: BT.G.Reference, right_childref: BT.G.Reference)
  : (res : Node)
  requires WFNode(fused_parent)
  requires 0 <= slot < |fused_parent.buckets|
  requires fused_parent.children.Some?
  {
    var pivots := Sequences.insert(fused_parent.pivotTable, pivot, slot);
    var buckets := SplitBucketInList(fused_parent.buckets, slot, pivot);
    Node(
      pivots,
      Some(replace1with2(fused_parent.children.value, left_childref, right_childref, slot)),
      buckets
    )
  }

  lemma SplitParentCorrect(parentref: BT.G.Reference, fused_parent: Node, pivot: Key, slot: int, left_childref: BT.G.Reference, right_childref: BT.G.Reference)
  requires WFNode(fused_parent)
  requires BT.WFNode(INode(fused_parent))
  requires 0 <= slot < |fused_parent.buckets|
  requires PivotsLib.PivotInsertable(fused_parent.pivotTable, slot, pivot)
  requires |fused_parent.buckets| <= MaxNumChildren() - 1
  requires fused_parent.children.Some?
  ensures
    && var res := SplitParent(fused_parent, pivot, slot, left_childref, right_childref);
    && WFNode(res)
    && var inode := INode(fused_parent);
    && var inode' := INode(res);
    && inode' == BT.SplitParent(inode, pivot, slot, left_childref, right_childref)
    && WeightBucketList(res.buckets) <= WeightBucketList(fused_parent.buckets)
  {
    reveal_SplitParent();
    var res := SplitParent(fused_parent, pivot, slot, left_childref, right_childref);
    WFSplitBucketInList(fused_parent.buckets, slot, pivot, fused_parent.pivotTable);
    WeightSplitBucketInListLe(fused_parent.buckets, slot, pivot);
    assert WFNode(res);
    assert INode(res) == BT.SplitParent(INode(fused_parent), pivot, slot, left_childref, right_childref);
  }

  lemma lemmaSplitParentValidReferences(fused_parent: BT.G.Node, pivot: Key, slot: int, left_childref: BT.G.Reference, right_childref: BT.G.Reference, graph: map<BT.G.Reference, seq<BT.G.Reference>>)
  requires BT.WFNode(fused_parent)
  requires 0 <= slot < |fused_parent.buckets|
  requires fused_parent.children.Some?
  requires BC.BlockPointsToValidReferences(fused_parent, graph);
  requires left_childref in graph
  requires right_childref in graph
  ensures BC.BlockPointsToValidReferences(BT.SplitParent(fused_parent, pivot, slot, left_childref, right_childref), graph);
  {
    var split_parent := BT.SplitParent(fused_parent, pivot, slot, left_childref, right_childref);
    forall r | r in BT.G.Successors(split_parent)
    ensures r in graph
    {
      assert BC.BlockPointsToValidReferences(fused_parent, graph);
      var idx :| 0 <= idx < |split_parent.children.value| && split_parent.children.value[idx] == r;
      if (idx < slot) {
        assert r == fused_parent.children.value[idx];
        assert r in graph;
      } else if (idx == slot) {
        assert r == left_childref;
        assert r in graph;
      } else if (idx == slot + 1) {
        assert r == right_childref;
        assert r in graph;
      } else {
        assert r == fused_parent.children.value[idx-1];
        assert r in graph;
      }
    }
  }

  function {:opaque} splitBookkeeping(k: Constants, s: Variables, left_childref: BT.G.Reference, right_childref: BT.G.Reference, parentref: BT.G.Reference, fused_parent_children: seq<BT.G.Reference>, left_child: Node, right_child: Node, slot: int) : (s': Variables)
  requires 0 <= slot < |fused_parent_children|
  requires s.Ready?
  requires WriteAllocConditions(k, s)
  requires ChildrenConditions(k, s, left_child.children)
  requires ChildrenConditions(k, s, right_child.children)
  requires ChildrenConditions(k, s, Some(fused_parent_children))
  requires |fused_parent_children| < MaxNumChildren()
  requires |s.ephemeralIndirectionTable.graph| <= IndirectionTableModel.MaxSize() - 3
  ensures s'.Ready?
  ensures s'.cache == s.cache
  {
    lemmaChildrenConditionsPreservedWriteBookkeeping(k, s, left_childref, left_child.children, right_child.children);
    lemmaChildrenConditionsPreservedWriteBookkeeping(k, s, left_childref, left_child.children, Some(fused_parent_children));
    lemmaRefInGraphOfWriteBookkeeping(k, s, left_childref, left_child.children);

    var s1 := writeBookkeeping(k, s, left_childref, left_child.children);

    lemmaChildrenConditionsPreservedWriteBookkeeping(k, s1, right_childref, right_child.children, Some(fused_parent_children));
    lemmaRefInGraphOfWriteBookkeeping(k, s1, right_childref, right_child.children);
    lemmaRefInGraphPreservedWriteBookkeeping(k, s1, right_childref, right_child.children, left_childref);

    var s2 := writeBookkeeping(k, s1, right_childref, right_child.children);

    lemmaChildrenConditionsOfReplace1With2(k, s2, fused_parent_children, slot, left_childref, right_childref);

    var s3 := writeBookkeeping(k, s2, parentref, Some(replace1with2(fused_parent_children, left_childref, right_childref, slot)));

    s3
  }

  function {:opaque} splitCacheChanges(s: Variables, left_childref: BT.G.Reference,
      right_childref: BT.G.Reference, parentref: BT.G.Reference, slot: int, num_children_left: int, pivot: Key, left_child: Node, right_child: Node) : (s': Variables)
  requires s.Ready?
  requires parentref in s.cache
  requires WFNode(s.cache[parentref]);
  requires s.cache[parentref].children.Some?
  requires 0 <= slot < |s.cache[parentref].children.value|
  {
    var fused_parent := s.cache[parentref];
    var split_parent := SplitParent(fused_parent, pivot, slot, left_childref, right_childref);
    s.(cache := s.cache
        [left_childref := left_child]
        [right_childref := right_child]
        [parentref := split_parent])
  }

  function {:opaque} splitDoChanges(k: Constants, s: Variables, child: Node,
      left_childref: BT.G.Reference, right_childref: BT.G.Reference, parentref: BT.G.Reference,
      fused_parent_children: seq<BT.G.Reference>, slot: int) : (s': Variables)
  requires s.Ready?
  requires parentref in s.cache
  requires WFNode(s.cache[parentref]);
  requires WFNode(child);
  requires s.cache[parentref].children.Some?
  requires 0 <= slot < |s.cache[parentref].children.value|
  requires 0 <= slot < |fused_parent_children|
  requires |child.buckets| >= 2
  requires WriteAllocConditions(k, s)
  requires ChildrenConditions(k, s, Some(fused_parent_children))
  requires ChildrenConditions(k, s, child.children)
  requires |fused_parent_children| < MaxNumChildren()
  requires |s.ephemeralIndirectionTable.graph| <= IndirectionTableModel.MaxSize() - 3
  {
    var num_children_left := |child.buckets| / 2;
    var pivot := child.pivotTable[num_children_left - 1];

    lemmaChildrenConditionsSplitChild(k, s, child, num_children_left);

    var left_child := SplitChildLeft(child, num_children_left);
    var right_child := SplitChildRight(child, num_children_left);

    var s3 := splitBookkeeping(k, s, left_childref, right_childref, parentref, fused_parent_children, left_child, right_child, slot);
    var s' := splitCacheChanges(s3, left_childref, right_childref, parentref, slot, num_children_left, pivot, left_child, right_child);
    s'
  }

  function {:opaque} doSplit(k: Constants, s: Variables, parentref: BT.G.Reference, childref: BT.G.Reference, slot: int)
  : (s': Variables)
  requires s.Ready?
  requires Inv(k, s)
  requires childref in s.ephemeralIndirectionTable.graph
  requires parentref in s.ephemeralIndirectionTable.graph
  requires childref in s.cache
  requires parentref in s.cache
  requires s.cache[parentref].children.Some?
  requires |s.cache[parentref].buckets| <= MaxNumChildren() - 1
  requires 0 <= slot < |s.cache[parentref].children.value|
  requires s.cache[parentref].children.value[slot] == childref
  requires |s.ephemeralIndirectionTable.graph| <= IndirectionTableModel.MaxSize() - 3
  {
    if (
      && s.frozenIndirectionTable.Some?
      && IndirectionTableModel.HasEmptyLoc(s.frozenIndirectionTable.value, parentref)
    ) then (
      s
    ) else (
      var fused_parent := s.cache[parentref];
      var fused_child := s.cache[childref];

      lemmaChildrenConditionsOfNode(k, s, parentref);
      lemmaChildrenConditionsOfNode(k, s, childref);

      var lbound := (if slot > 0 then Some(fused_parent.pivotTable[slot - 1]) else None);
      var ubound := (if slot < |fused_parent.pivotTable| then Some(fused_parent.pivotTable[slot]) else None);
      
      lemmaChildrenConditionsCutoffNode(k, s, fused_child, lbound, ubound);
      CutoffNodeCorrect(fused_child, lbound, ubound);
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
            splitDoChanges(k, s, child, left_childref.value,
                right_childref.value, parentref, fused_parent.children.value,
                slot)
          )
        )
      )
    )
  }

  lemma doSplitCorrect(k: Constants, s: Variables, parentref: BT.G.Reference, childref: BT.G.Reference, slot: int)
  requires s.Ready?
  requires Inv(k, s)
  requires childref in s.ephemeralIndirectionTable.graph
  requires parentref in s.ephemeralIndirectionTable.graph
  requires childref in s.cache
  requires parentref in s.cache
  requires s.cache[parentref].children.Some?
  requires |s.cache[parentref].buckets| <= MaxNumChildren() - 1
  requires 0 <= slot < |s.cache[parentref].children.value|
  requires s.cache[parentref].children.value[slot] == childref
  requires TotalCacheSize(s) <= MaxCacheSize() - 2
  requires |s.ephemeralIndirectionTable.graph| <= IndirectionTableModel.MaxSize() - 3
  ensures var s' := doSplit(k, s, parentref, childref, slot);
    && WFVars(s')
    && M.Next(Ik(k), IVars(s), IVars(s'), UI.NoOp, D.NoDiskOp)
  {
    var s' := doSplit(k, s, parentref, childref, slot);
    reveal_doSplit();

    if (
      && s.frozenIndirectionTable.Some?
      && IndirectionTableModel.HasEmptyLoc(s.frozenIndirectionTable.value, parentref)
    ) {
      assert noop(k, IVars(s), IVars(s));
    } else {
      var fused_parent := s.cache[parentref];
      var fused_child := s.cache[childref];

      lemmaChildrenConditionsOfNode(k, s, parentref);
      lemmaChildrenConditionsOfNode(k, s, childref);

      var lbound := (if slot > 0 then Some(fused_parent.pivotTable[slot - 1]) else None);
      var ubound := (if slot < |fused_parent.pivotTable| then Some(fused_parent.pivotTable[slot]) else None);
      var child := CutoffNode(fused_child, lbound, ubound);
      lemmaChildrenConditionsCutoffNode(k, s, fused_child, lbound, ubound);
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

            lemmaChildrenConditionsSplitChild(k, s, child, num_children_left);

            var left_child := SplitChildLeft(child, num_children_left);
            var right_child := SplitChildRight(child, num_children_left);
            var split_parent := SplitParent(fused_parent, pivot, slot, left_childref.value, right_childref.value);
            reveal_SplitParent();

            reveal_writeBookkeeping();
            reveal_splitCacheChanges();
            reveal_splitDoChanges();
            reveal_splitBookkeeping();

            lemmaChildrenConditionsPreservedWriteBookkeeping(k, s, left_childref.value, left_child.children, right_child.children);
            lemmaChildrenConditionsPreservedWriteBookkeeping(k, s, left_childref.value, left_child.children, fused_parent.children);
            lemmaRefInGraphOfWriteBookkeeping(k, s, left_childref.value, left_child.children);

            var s1 := writeWithNode(k, s, left_childref.value, left_child);
            var s2 := writeWithNode(k, s1, right_childref.value, right_child);

            lemmaChildrenConditionsOfReplace1With2(k, s2, fused_parent.children.value, slot, left_childref.value, right_childref.value);

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
