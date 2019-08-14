include "ImplCache.i.dfy"

module ImplSplit { 
  import opened Impl
  import opened ImplIO
  import opened ImplCache

  import opened Options
  import opened MainDiskIOHandler
  import opened Maps
  import opened Sequences
  import opened Sets

  import opened BucketsLib
  import PivotsLib

  import opened NativeTypes

  method CutoffNodeAndKeepLeft(node: IS.Node, pivot: Key)
  returns (node': IS.Node)
  requires IS.WFNode(node)
  requires BT.WFNode(IS.INode(node))
  ensures IS.WFNode(node')
  ensures IS.INode(node') == BT.CutoffNodeAndKeepLeft(IS.INode(node), pivot)
  {
    BT.reveal_CutoffNodeAndKeepLeft();
    var cLeft := Pivots.ComputeCutoffForLeft(node.pivotTable, pivot);
    var leftPivots := node.pivotTable[.. cLeft];
    var leftChildren := if node.children.Some? then Some(node.children.value[.. cLeft + 1]) else None;
    var splitBucket := KMTable.SplitLeft(node.buckets[cLeft], pivot);
    var leftBuckets := node.buckets[.. cLeft] + [splitBucket];
    Pivots.WFSlice(node.pivotTable, 0, cLeft);
    KMTable.Islice(node.buckets, 0, cLeft);
    KMTable.IPopBack(node.buckets[.. cLeft], splitBucket);
    WFSplitBucketListLeft(KMTable.ISeq(node.buckets), node.pivotTable, cLeft, pivot);

    node' := IS.Node(leftPivots, leftChildren, leftBuckets);
  }

  method CutoffNodeAndKeepRight(node: IS.Node, pivot: Key)
  returns (node': IS.Node)
  requires IS.WFNode(node)
  requires BT.WFNode(IS.INode(node))
  ensures IS.WFNode(node')
  ensures IS.INode(node') == BT.CutoffNodeAndKeepRight(IS.INode(node), pivot)
  {
    BT.reveal_CutoffNodeAndKeepRight();
    var cRight := Pivots.ComputeCutoffForRight(node.pivotTable, pivot);
    var rightPivots := node.pivotTable[cRight ..];
    var rightChildren := if node.children.Some? then Some(node.children.value[cRight ..]) else None;
    var splitBucket := KMTable.SplitRight(node.buckets[cRight], pivot);
    var rightBuckets := [splitBucket] + node.buckets[cRight + 1 ..];
    Pivots.WFSuffix(node.pivotTable, cRight);
    KMTable.Isuffix(node.buckets, cRight + 1);
    KMTable.IPopFront(splitBucket, node.buckets[cRight + 1 ..]);
    WFSplitBucketListRight(KMTable.ISeq(node.buckets), node.pivotTable, cRight, pivot);

    node' := IS.Node(rightPivots, rightChildren, rightBuckets);
  }

  method CutoffNode(node: IS.Node, lbound: Option<Key>, rbound: Option<Key>)
  returns (node' : IS.Node)
  requires IS.WFNode(node)
  requires BT.WFNode(IS.INode(node))
  ensures IS.WFNode(node')
  ensures IS.INode(node') == BT.CutoffNode(IS.INode(node), lbound, rbound)
  {
    BT.reveal_CutoffNode();

    match lbound {
      case None => {
        match rbound {
          case None => {
            node' := node;
          }
          case Some(rbound) => {
            node' := CutoffNodeAndKeepLeft(node, rbound);
          }
        }
      }
      case Some(lbound) => {
        match rbound {
          case None => {
            node' := CutoffNodeAndKeepRight(node, lbound);
          }
          case Some(rbound) => {
            var node1 := CutoffNodeAndKeepLeft(node, rbound);
            node' := CutoffNodeAndKeepRight(node1, lbound);
          }
        }
      }
    }
  }

  function method SplitChildLeft(child: IS.Node, num_children_left: int) : IS.Node
  requires 0 <= num_children_left - 1 <= |child.pivotTable|
  requires child.children.Some? ==> 0 <= num_children_left <= |child.children.value|
  requires 0 <= num_children_left <= |child.buckets|
  {
    IS.Node(
      child.pivotTable[ .. num_children_left - 1 ],
      if child.children.Some? then Some(child.children.value[ .. num_children_left ]) else None,
      child.buckets[ .. num_children_left ]
    )
  }

  function method SplitChildRight(child: IS.Node, num_children_left: int) : IS.Node
  requires 0 <= num_children_left <= |child.pivotTable|
  requires child.children.Some? ==> 0 <= num_children_left <= |child.children.value|
  requires 0 <= num_children_left <= |child.buckets|
  {
    IS.Node(
      child.pivotTable[ num_children_left .. ],
      if child.children.Some? then Some(child.children.value[ num_children_left .. ]) else None,
      child.buckets[ num_children_left .. ]
    )
  }

  lemma lemmaSplitChild(child: IS.Node, num_children_left: int)
  requires IS.WFNode(child)
  requires BT.WFNode(IS.INode(child))
  requires 1 <= num_children_left <= |child.buckets| - 1
  ensures IS.WFNode(SplitChildLeft(child, num_children_left))
  ensures IS.WFNode(SplitChildRight(child, num_children_left))
  ensures IS.INode(SplitChildLeft(child, num_children_left)) == BT.SplitChildLeft(IS.INode(child), num_children_left)
  ensures IS.INode(SplitChildRight(child, num_children_left)) == BT.SplitChildRight(IS.INode(child), num_children_left)
  {
    Pivots.WFSlice(child.pivotTable, 0, num_children_left - 1);
    Pivots.WFSuffix(child.pivotTable, num_children_left);
    KMTable.Islice(child.buckets, 0, num_children_left);
    KMTable.Isuffix(child.buckets, num_children_left);
    WFBucketListSplitLeft(KMTable.ISeq(child.buckets), child.pivotTable, num_children_left);
    WFBucketListSplitRight(KMTable.ISeq(child.buckets), child.pivotTable, num_children_left);
    assert IS.WFNode(SplitChildRight(child, num_children_left));
    assert IS.WFNode(SplitChildLeft(child, num_children_left));
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

  method SplitParent(fused_parent: IS.Node, pivot: Key, slot_idx: int, left_childref: BT.G.Reference, right_childref: BT.G.Reference) returns (res : IS.Node)
  requires IS.WFNode(fused_parent)
  requires BT.WFNode(IS.INode(fused_parent))
  requires 0 <= slot_idx < |fused_parent.buckets|
  requires PivotsLib.PivotInsertable(fused_parent.pivotTable, slot_idx, pivot)
  requires fused_parent.children.Some?
  ensures IS.WFNode(res)
  ensures IS.INode(res) == BT.SplitParent(IS.INode(fused_parent), pivot, slot_idx, left_childref, right_childref)
  {
    var pivots := Sequences.insert(fused_parent.pivotTable, pivot, slot_idx);
    var buckets := replace1with2(fused_parent.buckets, KMTable.Empty(), KMTable.Empty(), slot_idx);
    res := IS.Node(
      pivots,
      Some(replace1with2(fused_parent.children.value, left_childref, right_childref, slot_idx)),
      buckets
    );

    KMTable.Ireplace1with2(fused_parent.buckets, KMTable.Empty(), KMTable.Empty(), slot_idx);
    WFBucketListReplace1with2(KMTable.ISeq(fused_parent.buckets), fused_parent.pivotTable, slot_idx, pivot);
    assert IS.WFNode(res);
    assert IS.INode(res) == BT.SplitParent(IS.INode(fused_parent), pivot, slot_idx, left_childref, right_childref);
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

  method AllocChildrefs(k: ImplConstants, s: ImplVariables, left_child: IS.Node, right_child: IS.Node)
  returns (s': ImplVariables, childrefs: Option<(BT.G.Reference, BT.G.Reference)>, ghost is1: Option<ImplADM.M.Variables>)
  requires s.Ready?
  requires IS.WFVars(s)
  requires IS.WFNode(left_child)
  requires IS.WFNode(right_child)
  requires BC.Inv(k, IS.IVars(s))
  requires BC.BlockPointsToValidReferences(IS.INode(left_child), IS.IIndirectionTable(s.ephemeralIndirectionTable).graph)
  requires BC.BlockPointsToValidReferences(IS.INode(right_child), IS.IIndirectionTable(s.ephemeralIndirectionTable).graph)
  requires BT.G.Root() in IS.IIndirectionTable(s.ephemeralIndirectionTable).graph
  ensures IS.WFVars(s)
  ensures IS.WFVars(s')
  ensures BC.Inv(k, IS.IVars(s'))
  ensures childrefs.None? ==> s == old(s)
  ensures childrefs.None? ==> IS.IVars(s) == old(IS.IVars(s))
  ensures childrefs.None? ==> IS.IVars(s') == old(IS.IVars(s))
  ensures childrefs.None? ==> noop(k, old(IS.IVars(s)), IS.IVars(s'))
  ensures childrefs.Some? <==> is1.Some?
  ensures childrefs.Some? ==> s'.Ready?
  ensures childrefs.Some? ==> (
      && var (left_child_ref, right_child_ref) := childrefs.value;
      && s' == old(s).(cache := old(s.cache[left_child_ref := left_child][right_child_ref := right_child])))
  ensures childrefs.Some? ==> (
      && var (left_child_ref, right_child_ref) := childrefs.value;
      && BC.Alloc(k, old(IS.IVars(s)), is1.value, left_child_ref, IS.INode(left_child))
      && BC.Alloc(k, is1.value, IS.IVars(s'), right_child_ref, IS.INode(right_child)))
  ensures childrefs.Some? ==> (
      && var (left_child_ref, right_child_ref) := childrefs.value;
      left_child_ref != right_child_ref)
  ensures forall r | r in s.ephemeralIndirectionTable.Repr :: fresh(r) || r in old(s.ephemeralIndirectionTable.Repr)
  modifies s.ephemeralIndirectionTable.Repr
  {
    childrefs := None;
    ghost var is0 := IS.IVars(s);

    var s1, left_child_ref := alloc(k, s, left_child);
    if left_child_ref.None? {
      s' := s;
      assert old(IS.IVars(s)) == IS.IVars(s');
      print "giving up; could not get ref\n";
      is1 := None;
      return;
    }
    is1 := Some(IS.IVars(s1));

    assert BC.Alloc(k, old(IS.IVars(s)), is1.value, left_child_ref.value, IS.INode(left_child));
    
    var s2, right_child_ref := alloc(k, s1, right_child);
    if right_child_ref.None? {
      assert left_child_ref.value in IS.IVars(s1).cache;

      s' := rollbackAlloc(k, s1, left_child_ref.value, left_child, is0);

      assert old(IS.IVars(s)) == IS.IVars(s');
      print "giving up; could not get ref\n";
      is1 := None;
      return;
    }
    s' := s2;
    childrefs := Some((left_child_ref.value, right_child_ref.value));
  }

  datatype SplitNodesReceipt = SplitNodesReceipt(
      // in
      ghost fused_parent: IS.Node,
      ghost fused_child: IS.Node,
      ghost cutoff_child: IS.Node,
      ghost slot: int,
      ghost graph: map<BT.G.Reference, seq<BT.G.Reference>>,
      // out
      left_child: IS.Node,
      right_child: IS.Node,
      pivot: Key,
      ghost num_children_left: int,
      ghost lbound: Option<Key>,
      ghost ubound: Option<Key>)

  predicate {:opaque} SplitNodesReceiptValid(receipt: SplitNodesReceipt)
  ensures SplitNodesReceiptValid(receipt) ==> (receipt.fused_parent.children.Some?)
  ensures SplitNodesReceiptValid(receipt) ==> (0 <= receipt.slot < |receipt.fused_parent.children.value|)
  ensures SplitNodesReceiptValid(receipt) ==> (IS.WFNode(receipt.fused_parent))
  ensures SplitNodesReceiptValid(receipt) ==> (IS.WFNode(receipt.fused_child))
  ensures SplitNodesReceiptValid(receipt) ==> (IS.WFNode(receipt.left_child))
  ensures SplitNodesReceiptValid(receipt) ==> (IS.WFNode(receipt.right_child))
  {
    && (1 <= receipt.num_children_left < |receipt.cutoff_child.buckets|)
    && (1 <= receipt.num_children_left <= |receipt.cutoff_child.pivotTable|)
    && ((receipt.cutoff_child.children.Some? ==> 0 <= receipt.num_children_left <= |receipt.cutoff_child.children.value|))
    && (IS.WFNode(SplitChildLeft(receipt.cutoff_child, receipt.num_children_left)))
    && (IS.WFNode(SplitChildRight(receipt.cutoff_child, receipt.num_children_left)))
    && (IS.INode(SplitChildLeft(receipt.cutoff_child, receipt.num_children_left)) == BT.SplitChildLeft(IS.INode(receipt.cutoff_child), receipt.num_children_left))
    && (IS.INode(SplitChildRight(receipt.cutoff_child, receipt.num_children_left)) == BT.SplitChildRight(IS.INode(receipt.cutoff_child), receipt.num_children_left))
    && (BC.BlockPointsToValidReferences(BT.SplitChildLeft(IS.INode(receipt.cutoff_child), receipt.num_children_left), receipt.graph))
    && (BC.BlockPointsToValidReferences(BT.SplitChildRight(IS.INode(receipt.cutoff_child), receipt.num_children_left), receipt.graph))
    && (receipt.left_child == SplitChildLeft(receipt.cutoff_child, receipt.num_children_left))
    && (receipt.right_child == SplitChildRight(receipt.cutoff_child, receipt.num_children_left))
    && (receipt.cutoff_child.pivotTable[receipt.num_children_left - 1] == receipt.pivot)
    && (IS.WFNode(receipt.fused_parent))
    && (receipt.fused_parent.children.Some?)
    && (0 <= receipt.slot < |receipt.fused_parent.children.value|)
    && (IS.WFNode(receipt.fused_child))
    && (IS.WFBuckets(receipt.cutoff_child.buckets))
    && (IS.INode(receipt.cutoff_child) == BT.CutoffNode(IS.INode(receipt.fused_child), receipt.lbound, receipt.ubound))
    && (receipt.slot > 0 ==> 0 <= receipt.slot - 1 < |receipt.fused_parent.pivotTable|)
    && (receipt.lbound == (if receipt.slot > 0 then Some(receipt.fused_parent.pivotTable[receipt.slot - 1]) else None))
    && (receipt.ubound == (if receipt.slot < |receipt.fused_parent.pivotTable| then Some(receipt.fused_parent.pivotTable[receipt.slot]) else None))
    && (0 <= receipt.slot < |receipt.fused_parent.buckets|)
    && (|receipt.fused_parent.buckets[receipt.slot].keys| == |receipt.fused_parent.buckets[receipt.slot].values|)
    && (KMTable.I(receipt.fused_parent.buckets[receipt.slot]) == map[])
  }

  method splitNodes(
      fused_parent: IS.Node,
      fused_child: IS.Node,
      slot: int,
      ghost graph: map<BT.G.Reference, seq<BT.G.Reference>>
  ) returns (receipt: Option<SplitNodesReceipt>)
  requires fused_parent.children.Some?
  requires 0 <= slot < |fused_parent.children.value|
  requires IS.WFNode(fused_parent)
  requires IS.WFNode(fused_child)
  requires BC.BlockPointsToValidReferences(IS.INode(fused_child), graph)
  requires 0 <= slot < |fused_parent.pivotTable| + 1
  ensures receipt.Some? ==> SplitNodesReceiptValid(receipt.value)
  ensures receipt.Some? ==> IS.WFNode(receipt.value.left_child)
  ensures receipt.Some? ==> IS.WFNode(receipt.value.right_child)
  ensures receipt.Some? ==> receipt.value.fused_parent == fused_parent
  ensures receipt.Some? ==> receipt.value.fused_child == fused_child
  ensures receipt.Some? ==> receipt.value.slot == slot
  ensures receipt.Some? ==> receipt.value.graph == graph
  ensures receipt.Some? ==> BC.BlockPointsToValidReferences(IS.INode(receipt.value.left_child), receipt.value.graph)
  ensures receipt.Some? ==> BC.BlockPointsToValidReferences(IS.INode(receipt.value.right_child), receipt.value.graph)
  ensures receipt.Some? ==> PivotsLib.PivotInsertable(
      receipt.value.fused_parent.pivotTable,
      receipt.value.slot,
      receipt.value.pivot)
  {
    reveal_SplitNodesReceiptValid();

    INodeRootEqINodeForEmptyRootBucket(fused_parent);
    INodeRootEqINodeForEmptyRootBucket(fused_child);

    var lbound := (if slot > 0 then Some(fused_parent.pivotTable[slot - 1]) else None);
    var ubound := (if slot < |fused_parent.pivotTable| then Some(fused_parent.pivotTable[slot]) else None);
    var cutoff_child := CutoffNode(fused_child, lbound, ubound);

    if !KMTable.IsEmpty(fused_parent.buckets[slot]) {
      receipt := None;
      print "giving up; trying to split but parent has non-empty buffer\n";
      return;
    }
    assert KMTable.IsEmpty(fused_parent.buckets[slot]);

    if (|cutoff_child.pivotTable| == 0) {
      receipt := None;
      // TODO there should be an operation which just
      // cuts off the node and doesn't split it.
      print "giving up; child.pivots == 0\n";
      return;
    }
    assert |cutoff_child.pivotTable| != 0;

    assert |cutoff_child.buckets| == |cutoff_child.pivotTable| + 1;
    var num_children_left := |cutoff_child.buckets| / 2;
    var pivot := cutoff_child.pivotTable[num_children_left - 1];

    var left_child := SplitChildLeft(cutoff_child, num_children_left);
    var right_child := SplitChildRight(cutoff_child, num_children_left);

    lemmaSplitChild(cutoff_child, num_children_left);
    lemmaSplitChildValidReferences(IS.INode(fused_child), IS.INode(cutoff_child), num_children_left,
        graph, lbound, ubound);

    receipt := Some(SplitNodesReceipt(
        // in
        fused_parent, fused_child, cutoff_child, slot, graph,
        // out
        left_child, right_child, pivot, num_children_left, lbound, ubound));

    assert IS.WFNode(left_child);
    assert IS.WFNode(right_child);
    assert IS.INode(left_child) == BT.SplitChildLeft(IS.INode(cutoff_child), num_children_left);
    assert IS.INode(right_child) == BT.SplitChildRight(IS.INode(cutoff_child), num_children_left);
    assert BC.BlockPointsToValidReferences(BT.SplitChildLeft(IS.INode(cutoff_child), num_children_left), graph);
    assert BC.BlockPointsToValidReferences(BT.SplitChildRight(IS.INode(cutoff_child), num_children_left), graph);
    assert left_child == SplitChildLeft(cutoff_child, num_children_left);
    assert right_child == SplitChildRight(cutoff_child, num_children_left);

    assert SplitNodesReceiptValid(receipt.value);

    PivotsLib.PivotNotMinimum(cutoff_child.pivotTable, num_children_left - 1);
  }

  method doSplit(k: ImplConstants, s: ImplVariables, io: DiskIOHandler, parentref: BT.G.Reference, ref: BT.G.Reference, slot: int)
  returns (s': ImplVariables)
  requires s.Ready?
  requires IS.WFVars(s)
  requires BBC.Inv(k, IS.IVars(s))
  requires ref in IS.IIndirectionTable(s.ephemeralIndirectionTable).graph
  requires parentref in IS.IIndirectionTable(s.ephemeralIndirectionTable).graph
  requires ref in s.cache
  requires parentref in s.cache
  requires s.cache[parentref].children.Some?
  requires 0 <= slot < |s.cache[parentref].children.value|
  requires s.cache[parentref].children.value[slot] == ref
  requires io.initialized()
  requires s.rootBucket == TTT.EmptyTree // FIXME we don't actually need this unless paretnref is root
  modifies io
  ensures IS.WFVars(s')
  ensures ImplADM.M.Next(Ik(k), old(IS.IVars(s)), IS.IVars(s'), UI.NoOp, io.diskOp())
  // NOALIAS statically enforced no-aliasing would probably help here
  ensures forall r | r in s.ephemeralIndirectionTable.Repr :: fresh(r) || r in old(s.ephemeralIndirectionTable.Repr)
  modifies s.ephemeralIndirectionTable.Repr
  {
    if s.frozenIndirectionTable.Some? {
      var parentrefLbaGraph := s.frozenIndirectionTable.value.Get(parentref);
      if parentrefLbaGraph.Some? {
        assert parentref in IS.IIndirectionTable(s.frozenIndirectionTable.value).graph;
        var (lba, _) := parentrefLbaGraph.value;
        if lba.None? {
          assert parentref !in IS.IIndirectionTable(s.frozenIndirectionTable.value).locs;
          s' := s;
          assert noop(k, old(IS.IVars(s)), IS.IVars(s'));
          print "giving up; doSplit can't run because frozen isn't written\n";
          return;
        }
      }
    }

    var fused_parent := s.cache[parentref];
    var fused_child := s.cache[ref];

    assert BT.WFNode(IS.ICache(s.cache, s.rootBucket)[parentref]);
    assert BT.WFNode(IS.ICache(s.cache, s.rootBucket)[ref]);

    INodeRootEqINodeForEmptyRootBucket(fused_parent);
    INodeRootEqINodeForEmptyRootBucket(fused_child);

    assert WFBucketList(KMTable.ISeq(fused_parent.buckets), fused_parent.pivotTable);
    assert |KMTable.ISeq(fused_parent.buckets)| == |fused_parent.pivotTable| + 1;
    assert IS.WFNode(fused_parent);
    assert |fused_parent.buckets| == |fused_parent.children.value|;
    assert 0 <= slot < |fused_parent.pivotTable| + 1;

    var splitNodesReceipt := splitNodes(
        fused_parent,
        fused_child,
        slot,
        IS.IIndirectionTable(s.ephemeralIndirectionTable).graph);

    if splitNodesReceipt.None? {
      s' := s;
      assert noop(k, old(IS.IVars(s)), IS.IVars(s'));
      return;
    }
    assert splitNodesReceipt.Some?;

    var left_child := splitNodesReceipt.value.left_child;
    var right_child := splitNodesReceipt.value.right_child;
    ghost var num_children_left := splitNodesReceipt.value.num_children_left;
    var pivot := splitNodesReceipt.value.pivot;

    ghost var is0 := IS.IVars(s);

    assert BC.BlockPointsToValidReferences(IS.INode(left_child), IS.IIndirectionTable(s.ephemeralIndirectionTable).graph);
    assert BC.BlockPointsToValidReferences(IS.INode(right_child), IS.IIndirectionTable(s.ephemeralIndirectionTable).graph);

    var s2, allocedChildrefs, is1 := AllocChildrefs(k, s, left_child, right_child);
    if allocedChildrefs.None? {
      s' := s;
      assert noop(k, old(IS.IVars(s)), IS.IVars(s'));
      return;
    }
    var (left_child_ref, right_child_ref) := allocedChildrefs.value;
    ghost var is2 := IS.IVars(s2);

    var split_parent := SplitParent(fused_parent, pivot, slot, left_child_ref, right_child_ref);

    lemmaSplitParentValidReferences(IS.INode(fused_parent), pivot, slot, left_child_ref, right_child_ref, IS.IIndirectionTable(s2.ephemeralIndirectionTable).graph);

    assert parentref == BT.G.Root() ==> s.rootBucket == TTT.EmptyTree;

    s' := write(k, s2, parentref, split_parent);
    ghost var is' := IS.IVars(s');

    var step := doSplitSteps(splitNodesReceipt.value,
      parentref,
      ref,
      left_child_ref,
      right_child_ref,
      IS.INode(split_parent),
      k, is0, is1.value, is2, is');

    assert ImplADM.M.Next(Ik(k), old(IS.IVars(s)), IS.IVars(s'), UI.NoOp, io.diskOp());
  }

  lemma doSplitSteps(splitNodesReceipt: SplitNodesReceipt,
      parent_ref: BT.G.Reference,
      fused_child_ref: BT.G.Reference,
      left_child_ref: BT.G.Reference,
      right_child_ref: BT.G.Reference,
      split_parent: BT.G.Node,
      k: ImplADM.M.Constants,
      is: ImplADM.M.Variables,
      is1: ImplADM.M.Variables,
      is2: ImplADM.M.Variables,
      is': ImplADM.M.Variables) returns (step: BT.BetreeStep)
  requires left_child_ref != right_child_ref
  requires BT.WFNode(split_parent)
  requires SplitNodesReceiptValid(splitNodesReceipt)
  requires splitNodesReceipt.fused_parent.children.value[splitNodesReceipt.slot] == fused_child_ref
  requires 0 <= splitNodesReceipt.slot <= |IS.INode(splitNodesReceipt.fused_parent).pivotTable|
  requires split_parent == BT.SplitParent(IS.INode(splitNodesReceipt.fused_parent), splitNodesReceipt.pivot, splitNodesReceipt.slot, left_child_ref, right_child_ref)
  requires BC.ReadStep(k, is, BT.G.ReadOp(parent_ref, IS.INode(splitNodesReceipt.fused_parent)));
  requires BC.ReadStep(k, is, BT.G.ReadOp(fused_child_ref, IS.INode(splitNodesReceipt.fused_child)));
  requires BC.Alloc(k, is, is1, left_child_ref, IS.INode(splitNodesReceipt.left_child))
  requires BC.Alloc(k, is1, is2, right_child_ref, IS.INode(splitNodesReceipt.right_child))
  requires BC.Dirty(k, is2, is', parent_ref, split_parent)
  ensures stepsBetree(k, is, is', UI.NoOp, step)
  {
    // == start transaction ==
    reveal_SplitNodesReceiptValid();

    assert SplitNodesReceiptValid(splitNodesReceipt);
    assert IS.WFBuckets(splitNodesReceipt.cutoff_child.buckets);
    assert IS.INode(splitNodesReceipt.cutoff_child) == BT.CutoffNode(IS.INode(splitNodesReceipt.fused_child), splitNodesReceipt.lbound, splitNodesReceipt.ubound);
    assert 1 <= splitNodesReceipt.num_children_left < |splitNodesReceipt.cutoff_child.buckets|;

    ghost var splitStep := BT.NodeFusion(
      parent_ref,
      fused_child_ref,
      left_child_ref,
      right_child_ref,
      IS.INode(splitNodesReceipt.fused_parent),
      split_parent,
      IS.INode(splitNodesReceipt.fused_child),
      IS.INode(splitNodesReceipt.left_child),
      IS.INode(splitNodesReceipt.right_child),
      splitNodesReceipt.slot,
      splitNodesReceipt.num_children_left,
      splitNodesReceipt.pivot
    );

    assert splitStep.num_children_left == splitNodesReceipt.num_children_left;
    assert splitStep.fused_child == IS.INode(splitNodesReceipt.fused_child);

    assert left_child_ref != right_child_ref;
    assert BT.ValidSplit(splitStep);
    step := BT.BetreeSplit(splitStep);
    ghost var ops := [
      BT.G.AllocOp(left_child_ref, IS.INode(splitNodesReceipt.left_child)),
      BT.G.AllocOp(right_child_ref, IS.INode(splitNodesReceipt.right_child)),
      BT.G.WriteOp(parent_ref, split_parent)
    ];
    assert ops == BT.BetreeStepOps(step);
    BC.MakeTransaction3(k, is, is1, is2, is', ops);
    /* (doc) assert BT.SplitReads(splitStep) ==[
      BT.G.ReadOp(parent_ref, IS.INode(splitNodesReceipt.fused_parent)),
      BT.G.ReadOp(fused_child_ref, IS.INode(splitNodesReceipt.fused_child))
    ]; */
    assert stepsBetree(k, is, is', UI.NoOp, step);
  }
}
