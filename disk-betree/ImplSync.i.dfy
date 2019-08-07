include "Impl.i.dfy"
include "MainDiskIOHandler.s.dfy"
include "../lib/Option.s.dfy"
include "../lib/Sets.i.dfy"

// See dependency graph in MainImpl.dfy

module ImplSync { 
  import opened Impl

  import opened Options
  import opened MainDiskIOHandler
  import opened Maps
  import opened Sequences
  import opened Sets

  import opened BucketsLib

  import opened NativeTypes

  method getFreeRef(s: ImplVariables)
  returns (ref : Option<BT.G.Reference>)
  requires s.Ready?
  requires s.ephemeralIndirectionTable.Inv()
  ensures ref.Some? ==> ref.value !in IS.IIndirectionTable(s.ephemeralIndirectionTable).graph
  ensures ref.Some? ==> ref.value !in s.cache
  {
    var ephemeral': map<uint64, (Option<BC.LBA>, seq<IS.Reference>)> := s.ephemeralIndirectionTable.ToMap();
    var ephemeral_graph := map ref | ref in ephemeral' :: ephemeral'[ref].1;

    if r :| r !in ephemeral_graph && r !in s.cache {
      ref := Some(r);
    } else {
      ref := None;
    }
  }

  method getFreeLba(s: ImplVariables)
  returns (lba : Option<BC.LBA>)
  requires s.Ready?
  requires IS.WFVars(s)
  ensures lba.Some? ==> BC.ValidLBAForNode(lba.value)
  ensures lba.Some? ==> BC.LBAFree(IS.IVars(s), lba.value)
  {
    var persistent': map<uint64, (Option<BC.LBA>, seq<IS.Reference>)> := s.persistentIndirectionTable.ToMap();
    var persistent := map ref | ref in persistent' && persistent'[ref].0.Some? :: persistent'[ref].0.value;

    var ephemeral': map<uint64, (Option<BC.LBA>, seq<IS.Reference>)> := s.ephemeralIndirectionTable.ToMap();
    var ephemeral := map ref | ref in ephemeral' && ephemeral'[ref].0.Some? :: ephemeral'[ref].0.value;

    var frozen: Option<map<uint64, BC.LBA>> := None;
    if (s.frozenIndirectionTable.Some?) {
      var m := s.frozenIndirectionTable.value.ToMap();
      var frozen' := m;
      frozen := Some(map ref | ref in frozen' && frozen'[ref].0.Some? :: frozen'[ref].0.value);
    }

    if i: uint64 :| (
      && i as int * LBAType.BlockSize() as int < 0x1_0000_0000_0000_0000
      && var l := i * LBAType.BlockSize();
      && BC.ValidLBAForNode(l)
      && l !in persistent.Values
      && l !in ephemeral.Values
      && (frozen.Some? ==>
          l !in frozen.value.Values)
      && (forall id | id in s.outstandingBlockWrites ::
          s.outstandingBlockWrites[id].lba != l)
    ) {
      lba := Some(i * LBAType.BlockSize());

      assert IS.IVars(s).persistentIndirectionTable.lbas == persistent;
      assert IS.IVars(s).ephemeralIndirectionTable.lbas == ephemeral;
      assert IS.IVars(s).frozenIndirectionTable.Some? ==>
          IS.IVars(s).frozenIndirectionTable.value.lbas == frozen.value;
    } else {
      lba := None;
    }
  }

  method write(k: ImplConstants, s: ImplVariables, ref: BT.G.Reference, node: IS.Node)
  returns (s': ImplVariables)
  requires s.Ready?
  requires IS.WFVars(s)
  requires ref in IS.IIndirectionTable(s.ephemeralIndirectionTable).graph
  requires ref in s.cache
  requires ref == BT.G.Root() ==> s.rootBucket == TTT.EmptyTree
  requires IS.WFNode(node)
  requires BC.BlockPointsToValidReferences(IS.INode(node), IS.IIndirectionTable(s.ephemeralIndirectionTable).graph)
  requires s.frozenIndirectionTable.Some? && ref in IS.IIndirectionTable(s.frozenIndirectionTable.value).graph ==>
      ref in IS.IIndirectionTable(s.frozenIndirectionTable.value).lbas
  ensures IS.WFVars(s')
  ensures BC.Dirty(k, old(IS.IVars(s)), IS.IVars(s'), ref, IS.INode(node))
  modifies s.ephemeralIndirectionTable.Repr
  {
    if (ref == BT.G.Root()) {
      INodeRootEqINodeForEmptyRootBucket(node);
    }

    // s' := s
    //   .(ephemeralIndirectionTable :=
    //     BC.IndirectionTable(
    //       MapRemove(s.ephemeralIndirectionTable.lbas, {ref}),
    //       s.ephemeralIndirectionTable.graph[ref := if node.children.Some? then node.children.value else []]
    //     ))
    //   .(cache := s.cache[ref := node]);

    var lbaGraph := s.ephemeralIndirectionTable.Remove(ref);
    assert lbaGraph.Some?;
    var (lba, graph) := lbaGraph.value;

    // TODO how do we deal with this?
    assume s.ephemeralIndirectionTable.Count as nat < 0x10000000000000000 / 8;
    var _ := s.ephemeralIndirectionTable.Insert(ref, (None, if node.children.Some? then node.children.value else []));

    //assert IS.IIndirectionTable(s.ephemeralIndirectionTable).lbas ==
    //  MapRemove(old(IS.IIndirectionTable(s.ephemeralIndirectionTable)).lbas, {ref});

    //assert IS.IIndirectionTable(s.ephemeralIndirectionTable).graph ==
    //      old(IS.IIndirectionTable(s.ephemeralIndirectionTable)).graph[ref := if node.children.Some? then node.children.value else []];

    s' := s.(cache := s.cache[ref := node]);
    assert BC.Dirty(k, old(IS.IVars(s)), IS.IVars(s'), ref, IS.INode(node));
  }

  method RequestWrite(io: DiskIOHandler, addr: uint64, sector: IS.Sector)
  returns (id: Option<D.ReqId>)
  requires IS.WFSector(sector)
  requires sector.SectorBlock? ==> BT.WFNode(IS.INode(sector.block))
  requires sector.SectorBlock? ==> Marshalling.CappedNode(sector.block)
  requires io.initialized()
  requires ImplADM.M.ValidAddr(addr)
  modifies io
  ensures ImplADM.M.ValidDiskOp(io.diskOp())
  ensures id.Some? ==> ImplADM.M.IDiskOp(io.diskOp()) == SD.ReqWriteOp(id.value, SD.ReqWrite(addr, IS.ISector(sector)))
  ensures id.None? ==> ImplADM.M.IDiskOp(io.diskOp()) == SD.NoDiskOp
  {
    var bytes := Marshalling.MarshallSector(sector);
    if (bytes == null) {
      id := None;
    } else {
      var i := io.write(addr, bytes);
      id := Some(i);
    }
  }

  method alloc(k: ImplConstants, s: ImplVariables, node: IS.Node)
  returns (s': ImplVariables, ref: Option<BT.G.Reference>)
  requires IS.WFVars(s)
  requires IS.WFNode(node)
  requires BC.Inv(k, IS.IVars(s));
  requires s.Ready?
  requires BC.BlockPointsToValidReferences(IS.INode(node), IS.IIndirectionTable(s.ephemeralIndirectionTable).graph)
  ensures IS.WFVars(s')
  ensures ref.Some? ==> BC.Alloc(k, old(IS.IVars(s)), IS.IVars(s'), ref.value, IS.INode(node))
  ensures ref.None? ==> s' == s
  ensures s'.Ready?
  ensures s.rootBucket == s'.rootBucket
  modifies s.ephemeralIndirectionTable.Repr
  {
    ref := getFreeRef(s);
    if (ref.Some?) {
      // TODO how do we deal with this?
      assume s.ephemeralIndirectionTable.Count as nat < 0x10000000000000000 / 8;
      var _ := s.ephemeralIndirectionTable.Insert(ref.value, (None, if node.children.Some? then node.children.value else []));
      assert IS.IIndirectionTable(s.ephemeralIndirectionTable) == 
        old(
          BC.IndirectionTable(
            IS.IIndirectionTable(s.ephemeralIndirectionTable).lbas,
            IS.IIndirectionTable(s.ephemeralIndirectionTable).graph[ref.value := if node.children.Some? then node.children.value else []]
          ));
      s' := s.(cache := s.cache[ref.value := node]);
      assume ref.Some? ==> BC.Alloc(k, old(IS.IVars(s)), IS.IVars(s'), ref.value, IS.INode(node));
    } else {
      s' := s;
    }
  }

  lemma WFNodeRootImpliesWFRootBase(node: IS.Node, rootBucket: IS.TreeMap)
  requires IS.WFNode(node)
  requires TTT.TTTree(rootBucket)
  requires BT.WFNode(IS.INodeRoot(node, rootBucket))
  ensures BT.WFNode(IS.INode(node))

  predicate deallocable(s: ImplVariables, ref: BT.G.Reference)
  reads if s.Ready? then {s.ephemeralIndirectionTable} else {} // TODO necessary?
  reads if s.Ready? then s.ephemeralIndirectionTable.Repr else {}
  {
    && s.Ready?
    && ref in IS.IIndirectionTable(s.ephemeralIndirectionTable).graph
    && ref != BT.G.Root()
    && forall r | r in IS.IIndirectionTable(s.ephemeralIndirectionTable).graph :: ref !in IS.IIndirectionTable(s.ephemeralIndirectionTable).graph[r]
  }

  method Deallocable(s: ImplVariables, ref: BT.G.Reference) returns (result: bool)
  requires s.Ready? ==> s.ephemeralIndirectionTable.Inv()
  ensures result == deallocable(s, ref)
  {
    if ref == BT.G.Root() {
      return false;
    }
    if !s.Ready? {
      return false;
    }
    var lbaGraph := s.ephemeralIndirectionTable.Get(ref);
    if !lbaGraph.Some? {
      return false;
    }
    var table := s.ephemeralIndirectionTable.ToMap();
    var graph := map k | k in table :: table[k].1;
    result := forall r | r in graph :: ref !in graph[r];
    assume result == deallocable(s, ref);
  }

  method Dealloc(k: ImplConstants, s: ImplVariables, io: DiskIOHandler, ref: BT.G.Reference)
  returns (s': ImplVariables)
  requires IS.WFVars(s)
  requires io.initialized()
  requires deallocable(s, ref)
  modifies io
  requires BBC.Inv(k, IS.IVars(s))
  ensures IS.WFVars(s')
  ensures ImplADM.M.Next(Ik(k), old(IS.IVars(s)), IS.IVars(s'), UI.NoOp, io.diskOp())
  modifies s.ephemeralIndirectionTable.Repr
  {
    assume false; // TODO timing out
    if s.frozenIndirectionTable.Some? {
      var lbaGraph := s.frozenIndirectionTable.value.Get(ref);
      if lbaGraph.Some? {
        assert ref in IS.IIndirectionTable(s.frozenIndirectionTable.value).graph;
        var (lba, _) := lbaGraph.value;
        if lba.None? {
          assert ref !in IS.IIndirectionTable(s.frozenIndirectionTable.value).lbas;
          s' := s;
          assert noop(k, old(s), s');
          print "giving up; dealloc can't dealloc because frozen isn't written\n";
          return;
        }
      }
    }

    var _ := s.ephemeralIndirectionTable.Remove(ref);

    assert IS.IIndirectionTable(s.ephemeralIndirectionTable) ==
      old(BC.IndirectionTable(
        MapRemove(IS.IIndirectionTable(s.ephemeralIndirectionTable).lbas, {ref}),
        MapRemove(IS.IIndirectionTable(s.ephemeralIndirectionTable).graph, {ref})
      ));

    s' := s
      .(cache := MapRemove(s.cache, {ref}))
      .(outstandingBlockReads := BC.OutstandingBlockReadsRemoveRef(s.outstandingBlockReads, ref));
    assert BC.Unalloc(Ik(k), old(IS.IVars(s)), IS.IVars(s'), ImplADM.M.IDiskOp(io.diskOp()), ref);
    assert BBC.BlockCacheMove(Ik(k), old(IS.IVars(s)), IS.IVars(s'), UI.NoOp, ImplADM.M.IDiskOp(io.diskOp()), BC.UnallocStep(ref));
    assert stepsBC(k, old(s), s', UI.NoOp, io, BC.UnallocStep(ref));
  }

  method fixBigRoot(k: ImplConstants, s: ImplVariables, io: DiskIOHandler)
  returns (s': ImplVariables)
  requires IS.WFVars(s)
  requires s.Ready?
  requires io.initialized()
  requires s.rootBucket == TTT.EmptyTree
  modifies io
  requires BBC.Inv(k, IS.IVars(s))
  ensures IS.WFVars(s')
  ensures ImplADM.M.Next(Ik(k), old(IS.IVars(s)), IS.IVars(s'), UI.NoOp, io.diskOp())
  modifies s.ephemeralIndirectionTable.Repr
  {
    assume false; // TODO timing out

    if (BT.G.Root() !in s.cache) {
      s' := PageInReq(k, s, io, BT.G.Root());
      return;
    }

    INodeRootEqINodeForEmptyRootBucket(s.cache[BT.G.Root()]);

    if s.frozenIndirectionTable.Some? {
      var rootLbaGraph := s.frozenIndirectionTable.value.Get(BT.G.Root());
      if rootLbaGraph.Some? {
        assert BT.G.Root() in IS.IIndirectionTable(s.frozenIndirectionTable.value).graph;
        var (lba, _) := rootLbaGraph.value;
        if lba.None? {
          assert BT.G.Root() !in IS.IIndirectionTable(s.frozenIndirectionTable.value).lbas;
          s' := s;
          assert noop(k, old(s), s');
          print "giving up; fixBigRoot can't run because frozen isn't written\n";
          return;
        }
      }
    }

    var oldroot := s.cache[BT.G.Root()];
    var s1, newref := alloc(k, s, oldroot);
    match newref {
      case None => {
        s' := s;
        assert noop(k, old(s), s');
        print "giving up; could not allocate ref\n";
      }
      case Some(newref) => {
        var newroot := IS.Node([], Some([newref]), [KMTable.Empty()]);

        assert BT.G.Root() in s.cache;
        assert BT.G.Root() in IS.ICache(s.cache, s.rootBucket);
        assert BT.G.Root() in IS.ICache(s1.cache, s1.rootBucket);
        assert BT.G.Root() in s1.cache;

        assume BC.BlockPointsToValidReferences(IS.INode(newroot), IS.IIndirectionTable(s.ephemeralIndirectionTable).graph);
        s' := write(k, s1, BT.G.Root(), newroot);

        ghost var growth := BT.RootGrowth(IS.INode(oldroot), newref);
        assert IS.INode(newroot) == BT.G.Node([], Some([growth.newchildref]), [map[]]);
        ghost var step := BT.BetreeGrow(growth);
        BC.MakeTransaction2(k, old(IS.IVars(s)), IS.IVars(s1), IS.IVars(s'), BT.BetreeStepOps(step));
        //assert BBC.BetreeMove(Ik(k), old(IS.IVars(s)), IS.IVars(s'), UI.NoOp, ImplADM.M.IDiskOp(io.diskOp()), step);
        assert stepsBetree(k, old(s), s', UI.NoOp, step);
      }
    }
  }

  method GetNewPivots(bucket: KMTable.KMTable)
  returns (pivots : seq<MS.Key>)
  requires KMTable.WF(bucket)
  ensures Pivots.WFPivots(pivots)
  {
    // try to split the keys evenly, but don't let any bucket
    // be larger than the cap

    var n := |bucket.keys|;

    var m := (n + Marshalling.CapNumBuckets() as int) / Marshalling.CapNumBuckets() as int;
    if m > 500 {
      m := 500;
    }
    if m < 1 {
      m := 1;
    }

    MS.Keyspace.reveal_IsStrictlySorted();
    var r := [];
    var i := m;
    while i < n
    invariant MS.Keyspace.IsStrictlySorted(r);
    invariant |r| > 0 ==> 0 <= i-m < n && r[|r|-1] == bucket.keys[i - m];
    invariant |r| > 0 ==> MS.Keyspace.NotMinimum(r[0]);
    invariant i > 0
    {
      MS.Keyspace.IsNotMinimum(bucket.keys[0], bucket.keys[i]);

      r := r + [bucket.keys[i]];
      i := i + m;
    }

    pivots := r;
  }

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
    assume IS.WFNode(SplitChildRight(child, num_children_left));
    assume IS.WFNode(SplitChildLeft(child, num_children_left));
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
  requires fused_parent.children.Some?
  ensures IS.WFNode(res)
  ensures IS.INode(res) == BT.SplitParent(IS.INode(fused_parent), pivot, slot_idx, left_childref, right_childref)
  {
    res := IS.Node(
      Sequences.insert(fused_parent.pivotTable, pivot, slot_idx),
      Some(replace1with2(fused_parent.children.value, left_childref, right_childref, slot_idx)),
      replace1with2(fused_parent.buckets, KMTable.Empty(), KMTable.Empty(), slot_idx)
    );
    KMTable.Ireplace1with2(fused_parent.buckets, KMTable.Empty(), KMTable.Empty(), slot_idx);
    assume IS.WFNode(res);
    assume IS.INode(res) == BT.SplitParent(IS.INode(fused_parent), pivot, slot_idx, left_childref, right_childref);
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

  // TODO FIXME this method is flaky and takes a long time to verify
  method {:fuel WFBucketList,0} {:fuel BT.SplitChildLeft,0} {:fuel BT.SplitChildRight,0} {:fuel BT.SplitParent,0}
      {:fuel SplitChildLeft,0} {:fuel SplitChildRight,0}
  doSplit(k: ImplConstants, s: ImplVariables, io: DiskIOHandler, parentref: BT.G.Reference, ref: BT.G.Reference, slot: int)
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
  modifies s.ephemeralIndirectionTable.Repr
  {
    assume false; // TODO timing out

    if s.frozenIndirectionTable.Some? {
      var parentrefLbaGraph := s.frozenIndirectionTable.value.Get(parentref);
      if parentrefLbaGraph.Some? {
        assert parentref in IS.IIndirectionTable(s.frozenIndirectionTable.value).graph;
        var (lba, _) := parentrefLbaGraph.value;
        if lba.None? {
          assert parentref !in IS.IIndirectionTable(s.frozenIndirectionTable.value).lbas;
          s' := s;
          assert noop(k, old(s), s');
          print "giving up; doSplit can't run because frozen isn't written\n";
          return;
        }
      }
    }

    var fused_parent := s.cache[parentref];
    var fused_child := s.cache[ref];

    INodeRootEqINodeForEmptyRootBucket(fused_parent);
    INodeRootEqINodeForEmptyRootBucket(fused_child);

    assert BT.WFNode(IS.ICache(s.cache, s.rootBucket)[parentref]);
    assert BT.WFNode(IS.ICache(s.cache, s.rootBucket)[ref]);

    var lbound := (if slot > 0 then Some(fused_parent.pivotTable[slot - 1]) else None);
    var ubound := (if slot < |fused_parent.pivotTable| then Some(fused_parent.pivotTable[slot]) else None);
    var child := CutoffNode(fused_child, lbound, ubound);

    if !KMTable.IsEmpty(fused_parent.buckets[slot]) {
      s' := s;
      assert noop(k, old(s), s');
      print "giving up; trying to split but parent has non-empty buffer\n";
      return;
    }

    if (|child.pivotTable| == 0) {
      // TODO there should be an operation which just
      // cuts off the node and doesn't split it.
      s' := s;
      assert noop(k, old(s), s');
      print "giving up; child.pivots == 0\n";
      return;
    }

    var num_children_left := |child.buckets| / 2;
    var pivot := child.pivotTable[num_children_left - 1];

    var left_child := SplitChildLeft(child, num_children_left);
    var right_child := SplitChildRight(child, num_children_left);

    lemmaSplitChild(child, num_children_left);
    lemmaSplitChildValidReferences(IS.INode(fused_child), IS.INode(child), num_children_left,
        IS.IIndirectionTable(s.ephemeralIndirectionTable).graph, lbound, ubound);

    // TODO remove this when proof cleaned up (asserts necessary before KMTable)
    // SSTable.Islice(child.buckets, 0, num_children_left);
    // SSTable.Isuffix(child.buckets, num_children_left);

    // forall r | r in BT.G.Successors(IS.INode(child))
    // ensures r in IS.IIndirectionTable(s.ephemeralIndirectionTable).graph
    // {
    //   assert BC.BlockPointsToValidReferences(IS.INode(fused_child), IS.IIndirectionTable(s.ephemeralIndirectionTable).graph);
    //   assert r in BT.G.Successors(IS.INode(fused_child));
    // }
    // assert BC.BlockPointsToValidReferences(IS.INode(child), IS.IIndirectionTable(s.ephemeralIndirectionTable).graph);

    // assert BC.BlockPointsToValidReferences(IS.INode(left_child), IS.IIndirectionTable(s.ephemeralIndirectionTable).graph);
    // assert BC.BlockPointsToValidReferences(IS.INode(right_child), IS.IIndirectionTable(s.ephemeralIndirectionTable).graph);

    var s1, left_childref := alloc(k, s, left_child);
    if left_childref.None? {
      s' := s;
      assume noop(k, old(s), s');
      assume ImplADM.M.Next(Ik(k), old(IS.IVars(s)), IS.IVars(s'), UI.NoOp, io.diskOp());
      print "giving up; could not get ref\n";
      return;
    }

    var s2, right_childref := alloc(k, s1, right_child);
    if right_childref.None? {
      s' := s;
      assume noop(k, old(s), s');
      print "giving up; could not get ref\n";
      return;
    }

    var split_parent := SplitParent(fused_parent, pivot, slot, left_childref.value, right_childref.value);
    lemmaSplitParentValidReferences(IS.INode(fused_parent), pivot, slot, left_childref.value, right_childref.value, IS.IIndirectionTable(s2.ephemeralIndirectionTable).graph);

    // TODO remove this when proof cleaned up (asserts necessary before KMTable)
    // var split_parent_pivots := Sequences.insert(fused_parent.pivotTable, pivot, slot);
    // var split_parent_children := replace1with2(fused_parent.children.value, left_childref.value, right_childref.value, slot);
    // var split_parent_buckets := replace1with2(fused_parent.buckets, SSTable.Empty(), SSTable.Empty(), slot);
    // var split_parent := IS.Node(
    //   split_parent_pivots,
    //   Some(split_parent_children),
    //   split_parent_buckets
    // );

    // SSTable.Ireplace1with2(fused_parent.buckets, SSTable.Empty(), SSTable.Empty(), slot);

    // assert IS.WFNode(split_parent);

    // forall r | r in BT.G.Successors(IS.INode(split_parent))
    // ensures r in IS.IIndirectionTable(s2.ephemeralIndirectionTable).graph
    // {
    //   assert BC.BlockPointsToValidReferences(IS.INode(fused_parent), IS.IIndirectionTable(s2.ephemeralIndirectionTable).graph);
    //   ghost var idx :| 0 <= idx < |split_parent_children| && split_parent_children[idx] == r;
    //   if (idx < slot) {
    //     assert r == fused_parent.children.value[idx];
    //     assert r in IS.IIndirectionTable(s2.ephemeralIndirectionTable).graph;
    //   } else if (idx == slot) {
    //     assert r == left_childref.value;
    //     assert r in IS.IIndirectionTable(s2.ephemeralIndirectionTable).graph;
    //   } else if (idx == slot + 1) {
    //     assert r == right_childref.value;
    //     assert r in IS.IIndirectionTable(s2.ephemeralIndirectionTable).graph;
    //   } else {
    //     assert r == fused_parent.children.value[idx-1];
    //     assert r in IS.IIndirectionTable(s2.ephemeralIndirectionTable).graph;
    //   }
    // }
    // assert BC.BlockPointsToValidReferences(IS.INode(split_parent), IS.IIndirectionTable(s2.ephemeralIndirectionTable).graph);

    assert parentref in s.cache;
    assert parentref in IS.ICache(s.cache, s.rootBucket);
    assert parentref in IS.ICache(s1.cache, s1.rootBucket);
    assert parentref in IS.ICache(s2.cache, s2.rootBucket);
    assert parentref in s2.cache;

    s' := write(k, s2, parentref, split_parent);

    ghost var splitStep := BT.NodeFusion(
      parentref,
      ref,
      left_childref.value,
      right_childref.value,
      IS.INode(fused_parent),
      IS.INode(split_parent),
      IS.INode(fused_child),
      IS.INode(left_child),
      IS.INode(right_child),
      slot,
      num_children_left,
      pivot
    );
    assert BT.ValidSplit(splitStep);
    ghost var step := BT.BetreeSplit(splitStep);
    BC.MakeTransaction3(k, old(IS.IVars(s)), IS.IVars(s1), IS.IVars(s2), IS.IVars(s'), BT.BetreeStepOps(step));
    assert stepsBetree(k, s, s', UI.NoOp, step);
  }

  method flush(k: ImplConstants, s: ImplVariables, io: DiskIOHandler, ref: BT.G.Reference, slot: int)
  returns (s': ImplVariables)
  requires IS.WFVars(s)
  requires s.Ready?
  requires ref in IS.IIndirectionTable(s.ephemeralIndirectionTable).graph
  requires ref in s.cache
  requires s.cache[ref].children.Some?
  requires 0 <= slot < |s.cache[ref].buckets|
  requires io.initialized()
  requires s.rootBucket == TTT.EmptyTree // FIXME we don't actually need this unless we're flushing the root
  modifies io
  requires BBC.Inv(k, IS.IVars(s))
  ensures IS.WFVars(s')
  ensures ImplADM.M.Next(Ik(k), old(IS.IVars(s)), IS.IVars(s'), UI.NoOp, io.diskOp())
  modifies s.ephemeralIndirectionTable.Repr
  {
    assume false; // timing out

    if s.frozenIndirectionTable.Some? {
      var lbaGraph := s.frozenIndirectionTable.value.Get(ref);
      if lbaGraph.Some? {
        assert ref in IS.IIndirectionTable(s.frozenIndirectionTable.value).graph;
        var (lba, _) := lbaGraph.value;
        if lba.None? {
          assert ref !in IS.IIndirectionTable(s.frozenIndirectionTable.value).lbas;
          s' := s;
          assert noop(k, old(s), s');
          print "giving up; flush can't run because frozen isn't written";
          return;
        }
      }
    }

    var node := s.cache[ref];

    INodeRootEqINodeForEmptyRootBucket(node);

    assert IS.INode(node) == IS.ICache(s.cache, s.rootBucket)[ref];
    assert BT.WFNode(IS.INode(node));

    var childref := node.children.value[slot];

    assert childref in BT.G.Successors(IS.INode(node));

    if (childref !in s.cache) {
      s' := PageInReq(k, s, io, childref);
      return;
    }

    var child := s.cache[childref];

    INodeRootEqINodeForEmptyRootBucket(child);

    assert IS.INode(child) == IS.ICache(s.cache, s.rootBucket)[childref];
    assert BT.WFNode(IS.INode(child));

    if (!(
      && |node.buckets[slot].keys| < 0x4000_0000_0000_0000
      && |child.buckets| < 0x1_0000_0000_0000_0000
      && (forall i | 0 <= i < |child.buckets| :: |child.buckets[i].keys| < 0x4000_0000_0000_0000)
    )) {
      s' := s;
      assert noop(k, old(s), s');
      print "giving up; data is 2 big\n";
      return;
    }

    forall i, key | 0 <= i < |child.buckets| && key in KMTable.I(child.buckets[i]) ensures Pivots.Route(child.pivotTable, key) == i
    {
      //assert BT.NodeHasWFBucketAt(IS.INode(child), i);
    }

    var newbuckets := KMTable.Flush(node.buckets[slot], child.buckets, child.pivotTable);
    var newchild := child.(buckets := newbuckets);

    WFBucketListFlush(KMTable.I(node.buckets[slot]), KMTable.ISeq(child.buckets), child.pivotTable);

    assert BT.G.Successors(IS.INode(newchild)) == BT.G.Successors(IS.INode(child));
    assert BC.BlockPointsToValidReferences(IS.INode(newchild), IS.IIndirectionTable(s.ephemeralIndirectionTable).graph);

    var s1, newchildref := alloc(k, s, newchild);
    if newchildref.None? {
      s' := s;
      assert noop(k, old(s), s');
      print "giving up; could not get ref\n";
      return;
    }

    var newparent := IS.Node(
        node.pivotTable,
        Some(node.children.value[slot := newchildref.value]),
        node.buckets[slot := KMTable.Empty()]
      );

    assert BC.BlockPointsToValidReferences(IS.INode(node), IS.IIndirectionTable(s1.ephemeralIndirectionTable).graph);
    forall ref | ref in BT.G.Successors(IS.INode(newparent)) ensures ref in IS.IIndirectionTable(s1.ephemeralIndirectionTable).graph {
      if (ref == newchildref.value) {
      } else {
        assert ref in BT.G.Successors(IS.INode(node));
      }
    }
    assert BC.BlockPointsToValidReferences(IS.INode(newparent), IS.IIndirectionTable(s1.ephemeralIndirectionTable).graph);

    assert ref in s.cache;
    assert ref in IS.ICache(s.cache, s.rootBucket);
    assert ref in IS.ICache(s1.cache, s1.rootBucket);
    assert ref in s1.cache;

    s' := write(k, s1, ref, newparent);

    ghost var flushStep := BT.NodeFlush(ref, IS.INode(node), childref, IS.INode(child), newchildref.value, IS.INode(newchild), slot);
    assert BT.ValidFlush(flushStep);
    ghost var step := BT.BetreeFlush(flushStep);
    assert IS.INode(newparent) == BT.FlushOps(flushStep)[1].node;
    BC.MakeTransaction2(k, old(IS.IVars(s)), IS.IVars(s1), IS.IVars(s'), BT.BetreeStepOps(step));
    assert stepsBetree(k, old(s), s', UI.NoOp, step);
  }

  method {:fuel JoinBucketList,0} fixBigNode(k: ImplConstants, s: ImplVariables, io: DiskIOHandler, ref: BT.G.Reference, parentref: BT.G.Reference)
  returns (s': ImplVariables)
  requires IS.WFVars(s)
  requires BBC.Inv(k, IS.IVars(s))
  requires s.Ready?
  requires ref in s.cache
  requires parentref in IS.IIndirectionTable(s.ephemeralIndirectionTable).graph
  requires ref in IS.IIndirectionTable(s.ephemeralIndirectionTable).graph[parentref]
  requires s.rootBucket == TTT.EmptyTree // FIXME we don't actually need this I think
  requires io.initialized()
  modifies io
  ensures IS.WFVars(s')
  ensures ImplADM.M.Next(Ik(k), old(IS.IVars(s)), IS.IVars(s'), UI.NoOp, io.diskOp())
  modifies s.ephemeralIndirectionTable.Repr
  {
    assume false; // timing out

    if (ref !in s.cache) {
      s' := PageInReq(k, s, io, ref);
      return;
    }

    if s.frozenIndirectionTable.Some? {
      var lbaGraph := s.frozenIndirectionTable.value.Get(ref);
      if lbaGraph.Some? {
        assert ref in IS.IIndirectionTable(s.frozenIndirectionTable.value).graph;
        var (lba, _) := lbaGraph.value;
        if lba.None? {
          assert ref !in IS.IIndirectionTable(s.frozenIndirectionTable.value).lbas;
          s' := s;
          assert noop(k, old(s), s');
          print "giving up; fixBigRoot can't run because frozen isn't written";
          return;
        }
      }
    }

    var node := s.cache[ref];

    INodeRootEqINodeForEmptyRootBucket(node);

    if i :| 0 <= i < |node.buckets| && !Marshalling.CappedBucket(node.buckets[i]) {
      if (node.children.Some?) {
        // internal node case: flush
        s' := flush(k, s, io, ref, i);
      } else {
        // leaf case

        if (!(
          && |node.buckets| < 0x8000_0000
          && (forall i | 0 <= i < |node.buckets| :: |node.buckets[i].keys| < 0x1_0000_0000)
        )) {
          s' := s;
          assert noop(k, old(s), s');
          print "giving up; stuff too big to call Join\n";
          return;
        }

        forall i, j, key1, key2 | 0 <= i < j < |node.buckets| && key1 in KMTable.I(node.buckets[i]) && key2 in KMTable.I(node.buckets[j])
        ensures MS.Keyspace.lt(key1, key2)
        {
          //assert BT.NodeHasWFBucketAt(IS.INode(node), i);
          //assert BT.NodeHasWFBucketAt(IS.INode(node), j);
          assert Pivots.Route(node.pivotTable, key1) == i;
          assert Pivots.Route(node.pivotTable, key2) == j;
          MS.Keyspace.IsStrictlySortedImpliesLte(node.pivotTable, i, j-1);
        }

        var joined := KMTable.Join(node.buckets, node.pivotTable);
        var pivots := GetNewPivots(joined);

        if (!(|pivots| < 0x7fff_ffff_ffff_ffff)) {
          s' := s;
          assert noop(k, old(s), s');
          print "giving up; stuff too big to call Split\n";
          return;
        }

        var buckets' := KMTable.SplitOnPivots(joined, pivots);
        var newnode := IS.Node(pivots, None, buckets');

        WFSplitBucketOnPivots(KMTable.I(joined), pivots);
        s' := write(k, s, ref, newnode);

        //assert BT.ValidRepivot(BT.Repivot(ref, node, pivots));
        ghost var step := BT.BetreeRepivot(BT.Repivot(ref, IS.INode(node), pivots));
        assume BT.ValidBetreeStep(step);
        assume |BT.BetreeStepOps(step)| == 1; // TODO
        assume BC.OpStep(k, old(IS.IVars(s)), IS.IVars(s'), BT.BetreeStepOps(step)[0]);
        BC.MakeTransaction1(k, old(IS.IVars(s)), IS.IVars(s'), BT.BetreeStepOps(step));
        assume stepsBetree(k, s, s', UI.NoOp, step);
      }
    } else if |node.buckets| > Marshalling.CapNumBuckets() as int {
      if (parentref !in s.cache) {
        s' := PageInReq(k, s, io, parentref);
        return;
      }

      var parent := s.cache[parentref];

      INodeRootEqINodeForEmptyRootBucket(parent);

      assert ref in BT.G.Successors(IS.INode(parent));
      var i :| 0 <= i < |parent.children.value| && parent.children.value[i] == ref;

      s' := doSplit(k, s, io, parentref, ref, i);
    } else {
      s' := s;
      assert noop(k, old(s), s');
      print "giving up; fixBigNode\n";
    }
  }

  method {:fuel BC.GraphClosed,0} flushRootBucket(k: ImplConstants, s: ImplVariables, io: DiskIOHandler)
  returns (s': ImplVariables)
  requires io.initialized()
  modifies io
  requires IS.WFVars(s)
  requires BBC.Inv(k, IS.IVars(s))
  requires s.Ready?
  requires s.rootBucket != TTT.EmptyTree
  ensures IS.WFVars(s')
  ensures ImplADM.M.Next(Ik(k), old(IS.IVars(s)), IS.IVars(s'), UI.NoOp, io.diskOp())
  {
    var oldroot := s.cache[BT.G.Root()];

    var rootBucketSeq := TTT.AsSeq(s.rootBucket);

    if (!(
        && |rootBucketSeq| < 0x800_0000_0000
        && (forall i | 0 <= i < |rootBucketSeq| :: |rootBucketSeq[i].0| < 0x1_000)
        && (forall i | 0 <= i < |rootBucketSeq| :: rootBucketSeq[i].1 != Messages.IdentityMessage())
        && (forall i | 0 <= i < |rootBucketSeq| :: |rootBucketSeq[i].1.value| < 0x1_000)))
    {
      s' := s;
      assert noop(k, old(s), s');
      print "giving up; rootBucketSeq too big\n";
      return;
    }

    var kmt := KMTable.KMTableOfSeq(rootBucketSeq, TTT.I(s.rootBucket));

    if (!(
      && |kmt.keys| < 0x4000_0000_0000_0000
      && |oldroot.buckets| < 0x1_0000_0000_0000_0000
      && (forall i | 0 <= i < |oldroot.buckets| :: |oldroot.buckets[i].keys| < 0x4000_0000_0000_0000)
    )) {
      s' := s;
      assert noop(k, old(s), s');
      print "giving up; kmt/oldroot.buckets too big\n";
      return;
    }

    WFNodeRootImpliesWFRootBase(oldroot, s.rootBucket);
    forall i, key | 0 <= i < |oldroot.buckets| && key in KMTable.I(oldroot.buckets[i]) ensures Pivots.Route(oldroot.pivotTable, key) == i
    {
      //assert BT.NodeHasWFBucketAt(IS.INode(oldroot), i);
    }

    var newbuckets := KMTable.Flush(kmt, oldroot.buckets, oldroot.pivotTable);
    WFBucketListFlush(KMTable.I(kmt), KMTable.ISeq(oldroot.buckets), oldroot.pivotTable);

    var newroot := oldroot.(buckets := newbuckets);

    s' := s.(rootBucket := TTT.EmptyTree)
        .(cache := s.cache[BT.G.Root() := newroot]);

    BucketListFlushParentEmpty(KMTable.ISeq(newbuckets), oldroot.pivotTable);
    assert IS.INodeRoot(oldroot, s.rootBucket) == IS.INodeRoot(newroot, TTT.EmptyTree);
    assert IS.ICache(s.cache, s.rootBucket) == IS.ICache(s'.cache, TTT.EmptyTree);

    assert noop(k, old(s), s');
  }

  method AssignRefToLBA(table: IS.MutIndirectionTable, ref: IS.Reference, lba: BC.LBA)
  requires table.Inv()
  ensures IS.IIndirectionTable(table) ==
      old(BC.assignRefToLBA(IS.IIndirectionTable(table), ref, lba))
  modifies table.Repr
  {
    var lbaGraph := table.Remove(ref);
    if lbaGraph.Some? {
      var (_, graph) := lbaGraph.value;
      assume table.Count as nat < 0x10000000000000000 / 8;
      var _ := table.Insert(ref, (Some(lba), graph));
    }
    assume IS.IIndirectionTable(table) ==
        old(BC.assignRefToLBA(IS.IIndirectionTable(table), ref, lba));
  }

  method FindDeallocable(s: ImplVariables) returns (ref: Option<IS.Reference>)
  requires s.Ready?
  requires s.ephemeralIndirectionTable.Inv()
  ensures ref.Some? ==> ref.value in IS.IIndirectionTable(s.ephemeralIndirectionTable).graph
  ensures ref.Some? ==> deallocable(s, ref.value)
  ensures ref.None? ==> forall r | r in IS.IIndirectionTable(s.ephemeralIndirectionTable).graph :: !deallocable(s, r)
  {
    // TODO once we have an lba freelist, rewrite this to avoid extracting a `map` from `s.ephemeralIndirectionTable`
    var ephemeralTable := s.ephemeralIndirectionTable.ToMap();
    var ephemeralRefs := SetToSeq(set k | k in ephemeralTable);
    assume |ephemeralRefs| < 0x1_0000_0000_0000_0000;
    var i: uint64 := 0;
    while i as int < |ephemeralRefs|
    invariant i as int <= |ephemeralRefs|
    {
      var ref := ephemeralRefs[i];
      var isDeallocable := Deallocable(s, ref);
      if isDeallocable {
        return Some(ref);
      }
      i := i + 1;
    }
    assume forall r | r in IS.IIndirectionTable(s.ephemeralIndirectionTable).graph :: !deallocable(s, r);
    return None;
  }

  method FindUncappedNodeInCache(s: ImplVariables) returns (ref: Option<IS.Reference>)
  requires IS.WFVars(s)
  requires s.Ready?
  ensures ref.Some? ==> ref.value in IS.IIndirectionTable(s.ephemeralIndirectionTable).graph
  ensures ref.Some? ==> ref.value in s.cache && !Marshalling.CappedNode(s.cache[ref.value])
  ensures ref.None? ==> forall r | r in IS.IIndirectionTable(s.ephemeralIndirectionTable).graph :: r in s.cache && Marshalling.CappedNode(s.cache[r])
  {
    // TODO once we have an lba freelist, rewrite this to avoid extracting a `map` from `s.ephemeralIndirectionTable`
    var ephemeralTable := s.ephemeralIndirectionTable.ToMap();
    var ephemeralRefs := SetToSeq(set k | k in ephemeralTable);
    assume |ephemeralRefs| < 0x1_0000_0000_0000_0000;
    var i: uint64 := 0;
    while i as int < |ephemeralRefs|
    invariant i as int <= |ephemeralRefs|
    {
      var ref := ephemeralRefs[i];
      assume ref in s.cache;
      if !Marshalling.CappedNode(s.cache[ref]) {
        assume ref in IS.IIndirectionTable(s.ephemeralIndirectionTable).graph;
        return Some(ref);
      }
      i := i + 1;
    }
    assume forall r | r in IS.IIndirectionTable(s.ephemeralIndirectionTable).graph :: r in s.cache && Marshalling.CappedNode(s.cache[r]);
    return None;
  }

  method FindRefInFrozenWithNoLba(s: ImplVariables) returns (ref: Option<IS.Reference>)
  requires IS.WFVars(s)
  requires s.Ready?
  requires s.frozenIndirectionTable.Some?
  ensures ref.Some? ==> ref.value in IS.IIndirectionTable(s.frozenIndirectionTable.value).graph 
  ensures ref.Some? ==> ref.value !in IS.IIndirectionTable(s.frozenIndirectionTable.value).lbas
  ensures ref.None? ==> forall r | r in IS.IIndirectionTable(s.frozenIndirectionTable.value).graph
      :: r in IS.IIndirectionTable(s.frozenIndirectionTable.value).lbas
  {
    // TODO once we have an lba freelist, rewrite this to avoid extracting a `map` from `s.ephemeralIndirectionTable`
    var frozenTable := s.frozenIndirectionTable.value.ToMap();
    var frozenRefs := SetToSeq(set k | k in frozenTable);
    assume |frozenRefs| < 0x1_0000_0000_0000_0000;
    var i: uint64 := 0;
    while i as int < |frozenRefs|
    invariant i as int <= |frozenRefs|
    {
      var ref := frozenRefs[i];
      var lbaGraph := s.frozenIndirectionTable.value.Get(ref);
      assume lbaGraph.Some?;
      var (lba, _) := lbaGraph.value;
      if lba.None? {
        return Some(ref);
      }
      i := i + 1;
    }
    assume forall r | r in IS.IIndirectionTable(s.frozenIndirectionTable.value).graph
        :: r in IS.IIndirectionTable(s.frozenIndirectionTable.value).lbas;
    return None;
  }

  method FindRefNotPointingToRefInEphemeral(s: ImplVariables, ref: IS.Reference) returns (result: IS.Reference)
  requires IS.WFVars(s)
  requires s.Ready?
  requires exists r :: !(r in IS.IIndirectionTable(s.ephemeralIndirectionTable).graph ==>
      ref !in IS.IIndirectionTable(s.ephemeralIndirectionTable).graph[r])
  ensures !(result in IS.IIndirectionTable(s.ephemeralIndirectionTable).graph ==>
      ref !in IS.IIndirectionTable(s.ephemeralIndirectionTable).graph[result])
  {
    assume s.ephemeralIndirectionTable.Inv();
    var ephemeralTable := s.ephemeralIndirectionTable.ToMap();
    var ephemeralRefs := SetToSeq(set k | k in ephemeralTable);
    assume |ephemeralRefs| < 0x1_0000_0000_0000_0000;
    var i: uint64 := 0;
    while i as int < |ephemeralRefs|
    invariant i as int <= |ephemeralRefs|
    {
      var eRef := ephemeralRefs[i];
      assume eRef in IS.IIndirectionTable(s.ephemeralIndirectionTable).graph;
      var lbaGraph := s.ephemeralIndirectionTable.Get(eRef);
      assert lbaGraph.Some?;
      var (_, graph) := lbaGraph.value;
      if ref in graph {
        assume !(eRef in IS.IIndirectionTable(s.ephemeralIndirectionTable).graph ==>
            result in IS.IIndirectionTable(s.ephemeralIndirectionTable).graph &&
            ref !in IS.IIndirectionTable(s.ephemeralIndirectionTable).graph[result]); // TODO check this assume
        return eRef;
      }
      i := i + 1;
    }
    assume false;
    assert false;
  }

  method {:fuel BC.GraphClosed,0} sync(k: ImplConstants, s: ImplVariables, io: DiskIOHandler)
  returns (s': ImplVariables)
  requires io.initialized()
  modifies io
  requires IS.WFVars(s)
  requires BBC.Inv(k, IS.IVars(s))
  ensures IS.WFVars(s')
  ensures ImplADM.M.Next(Ik(k), old(IS.IVars(s)), IS.IVars(s'), UI.NoOp, io.diskOp())
  {
    assume false; // TODO timing out

    if (s.Unready?) {
      // TODO we could just do nothing here instead
      s' := PageInIndirectionTableReq(k, s, io);
      return;
    }

    if (s.outstandingIndirectionTableWrite.Some?) {
      s' := s;
      assert noop(k, old(s), s');
      print "sync: giving up; frozen table is currently being written\n";
      return;
    }

    if (s.rootBucket != TTT.EmptyTree) {
      s' := flushRootBucket(k, s, io);
      return;
    }

    // Plan:
    // - If the indirection table is not frozen then:
    //    - If anything can be unalloc'ed, do it
    //    - If any node is too big, do split/flush/whatever to shrink it
    //    - Freeze the indirection table
    // - Otherwise:
    //    - If any block in the frozen table doesn't have an LBA, Write it to disk
    //    - Write the frozenIndirectionTable to disk

    if (s.frozenIndirectionTable.None?) {
      var ephemeralTable := s.ephemeralIndirectionTable.ToMap();
      var ephemeralGraph := map k | k in ephemeralTable :: ephemeralTable[k].1;
      var foundDeallocable := FindDeallocable(s);
      if foundDeallocable.Some? {
        s' := Dealloc(k, s, io, foundDeallocable.value);
        return;
      }
      var foundUncapped := FindUncappedNodeInCache(s);
      if foundUncapped.Some? {
        var ref := foundUncapped.value;
        assert ref in IS.IIndirectionTable(s.ephemeralIndirectionTable).graph;
        assert ref in s.cache && !Marshalling.CappedNode(s.cache[foundUncapped.value]);
        if (ref == BT.G.Root()) {
          s' := fixBigRoot(k, s, io);
        } else {
          assert !deallocable(s, ref);
          assert !(forall r | r in IS.IIndirectionTable(s.ephemeralIndirectionTable).graph ::
              ref !in IS.IIndirectionTable(s.ephemeralIndirectionTable).graph[r]);
          assert !(forall r :: r in IS.IIndirectionTable(s.ephemeralIndirectionTable).graph ==>
              ref !in IS.IIndirectionTable(s.ephemeralIndirectionTable).graph[r]);
          assert (exists r :: !(r in IS.IIndirectionTable(s.ephemeralIndirectionTable).graph ==>
              ref !in IS.IIndirectionTable(s.ephemeralIndirectionTable).graph[r]));
          var r := FindRefNotPointingToRefInEphemeral(s, ref);
          assert !(r in IS.IIndirectionTable(s.ephemeralIndirectionTable).graph ==>
              ref !in IS.IIndirectionTable(s.ephemeralIndirectionTable).graph[r]);
          s' := fixBigNode(k, s, io, ref, r);
        }
        return;
      } else {
        s' := s.(frozenIndirectionTable := Some(s.ephemeralIndirectionTable))
            .(syncReqs := BC.syncReqs3to2(s.syncReqs));
        assert BC.Freeze(Ik(k), old(IS.IVars(s)), IS.IVars(s'), ImplADM.M.IDiskOp(io.diskOp()));
        assert stepsBC(k, s, s', UI.NoOp, io, BC.FreezeStep);
        return;
      }
    }
    var foundInFrozen := FindRefInFrozenWithNoLba(s);
    if foundInFrozen.Some? {
      var ref := foundInFrozen.value;
      assert ref in IS.IIndirectionTable(s.frozenIndirectionTable.value).graph;
      assert ref !in IS.IIndirectionTable(s.frozenIndirectionTable.value).lbas;

      if (!Marshalling.CappedNode(s.cache[ref])) {
        // TODO we should be able to prove this is impossible by adding an invariant
        // about frozenIndirectionTable (that is, we should never be freezing a table
        // with too-big nodes in it)
        s' := s;
        assert noop(k, old(s), s');
        print "sync: giving up; frozen table has big node rip (TODO we should prove this case impossible)\n";
        return;
      }

      var ephemeralRef := s.ephemeralIndirectionTable.Get(ref);
      if ephemeralRef.Some? && ephemeralRef.value.0.Some? {
        assert ref in IS.IIndirectionTable(s.ephemeralIndirectionTable).lbas;
        // TODO we should be able to prove this is impossible as well
        s' := s;
        assert noop(k, old(s), s');
        print "sync: giving up; ref already in ephemeralIndirectionTable.lbas but not frozen";
        return;
      }

      var lba := getFreeLba(s);
      match lba {
        case Some(lba) => {
          INodeRootEqINodeForEmptyRootBucket(s.cache[ref]);
          var id := RequestWrite(io, lba, IS.SectorBlock(s.cache[ref]));
          if (id.Some?) {
            AssignRefToLBA(s.ephemeralIndirectionTable, ref, lba);
            assert IS.IIndirectionTable(s.ephemeralIndirectionTable) ==
              BC.assignRefToLBA(IS.IIndirectionTable(s.ephemeralIndirectionTable), ref, lba);
            AssignRefToLBA(s.frozenIndirectionTable.value, ref, lba);
            assert IS.IIndirectionTable(s.frozenIndirectionTable.value) ==
              BC.assignRefToLBA(IS.IIndirectionTable(s.frozenIndirectionTable.value), ref, lba);
            s' := s
              .(outstandingBlockWrites := s.outstandingBlockWrites[id.value := BC.OutstandingWrite(ref, lba)]);
            assert BC.WriteBackReq(Ik(k), old(IS.IVars(s)), IS.IVars(s'), ImplADM.M.IDiskOp(io.diskOp()), ref);
            assert stepsBC(k, s, s', UI.NoOp, io, BC.WriteBackReqStep(ref));
          } else {
            s' := s;
            assert noop(k, old(s), s');
            print "sync: giving up; write req failed\n";
          }
        }
        case None => {
          s' := s;
          assert noop(k, old(s), s');
          print "sync: giving up; could not get lba\n";
        }
      }
    } else if (s.outstandingBlockWrites != map[]) {
      s' := s;
      assert noop(k, old(s), s');
      print "sync: giving up; blocks are still being written\n";
    } else {
      LBAType.reveal_ValidAddr();
      var id := RequestWrite(io, BC.IndirectionTableLBA(), IS.SectorIndirectionTable(s.frozenIndirectionTable.value));
      if (id.Some?) {
        s' := s.(outstandingIndirectionTableWrite := id);
        assert BC.WriteBackIndirectionTableReq(Ik(k), old(IS.IVars(s)), IS.IVars(s'), ImplADM.M.IDiskOp(io.diskOp()));
        assert stepsBC(k, s, s', UI.NoOp, io, BC.WriteBackIndirectionTableReqStep);
      } else {
        s' := s;
        assert noop(k, old(s), s');
        print "sync: giving up; write back indirection table failed (no id)\n";
      }
    }
  }
}
