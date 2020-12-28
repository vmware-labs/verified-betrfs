include "BookkeepingImpl.i.dfy"
include "SplitModel.i.dfy"

module SplitImpl { 
  import opened IOImpl
  import opened BookkeepingImpl
  import opened StateBCImpl
  import opened NodeImpl
  import opened DiskOpImpl
  import SplitModel
  import CacheImpl

  import IT = IndirectionTable

  import opened Options
  import opened Maps
  import opened Sequences
  import opened Sets
  import opened LinearSequence_s
  import opened LinearSequence_i

  import opened BucketsLib
  import opened BucketWeights
  import opened Bounds
  import opened KeyType
  import opened BoundedPivotsLib

  import opened NativeTypes

  method computeValidSplitKey(cache: CacheImpl.MutCache, ref: BT.G.Reference,
    pivots: PivotTable, lpivot: Key, rpivot: Option<Key>)
  returns (b: bool)
  requires cache.Inv()
  requires cache.ptr(ref).Some?
  requires cache.I()[ref].pivotTable == pivots
  requires BT.WFNode(cache.I()[ref])
  ensures BT.ValidSplitKey(cache.I()[ref], lpivot, rpivot) == b
  {
    var len := |pivots| as uint64;
    var valid := ComputeBoundedKey(pivots, lpivot);
    if !valid {
      return false;
    }

    if rpivot.Some? {
      valid := ComputeValidLeftCutOffKey(pivots, rpivot.value);
      if !valid {
        return false;
      }
      var k := ComputeGetKey(pivots, 0);
      var c := BT.G.KeyspaceImpl.cmp(k, rpivot.value);
      if c >= 0 {
        return false;
      }
      c := BT.G.KeyspaceImpl.cmp(lpivot, rpivot.value);
      if c >= 0 {
        return false;
      }
    } else {
      if pivots[len - 1] != Keyspace.Max_Element {
        return false;
      }
    }

    return true;
  }

  method splitBookkeeping(s: ImplVariables, left_childref: BT.G.Reference,
    right_childref: BT.G.Reference, parentref: BT.G.Reference, 
    fparent_children: seq<BT.G.Reference>, shared left_child: Node, 
    shared right_child: Node, slot: uint64)
  requires Inv(s)
  requires 0 <= slot as int < |fparent_children|
  requires slot as int < MaxNumChildren()
  requires left_child.Inv()
  requires right_child.Inv()
  requires s.ready
  requires BookkeepingModel.ChildrenConditions(s.I(), left_child.children)
  requires BookkeepingModel.ChildrenConditions(s.I(), right_child.children)
  requires BookkeepingModel.ChildrenConditions(s.I(), Some(fparent_children))
  requires |fparent_children| < MaxNumChildren()
  requires |s.ephemeralIndirectionTable.I().graph| <= IT.MaxSize() - 3
  modifies s.lru.Repr
  modifies s.ephemeralIndirectionTable.Repr
  modifies s.blockAllocator.Repr
  ensures s.ready
  ensures s.W()
  ensures forall o | o in s.lru.Repr :: o in old(s.lru.Repr) || fresh(o)
  ensures forall o | o in s.ephemeralIndirectionTable.Repr :: o in old(s.ephemeralIndirectionTable.Repr) || fresh(o)
  ensures forall o | o in s.blockAllocator.Repr :: o in old(s.blockAllocator.Repr) || fresh(o)
  ensures s.I() == SplitModel.splitBookkeeping(old(s.I()), left_childref, right_childref, 
    parentref, fparent_children, left_child.I(), right_child.I(), slot as int)
  {
    SplitModel.reveal_splitBookkeeping();

    BookkeepingModel.lemmaChildrenConditionsPreservedWriteBookkeeping(s.I(), left_childref, left_child.children, right_child.children);
    BookkeepingModel.lemmaChildrenConditionsPreservedWriteBookkeeping(s.I(), left_childref, left_child.children, Some(fparent_children));
    BookkeepingModel.lemmaRefInGraphOfWriteBookkeeping(s.I(), left_childref, left_child.children);

    writeBookkeeping(s, left_childref, left_child.children);

    BookkeepingModel.lemmaChildrenConditionsPreservedWriteBookkeeping(s.I(), right_childref, right_child.children, Some(fparent_children));
    BookkeepingModel.lemmaRefInGraphOfWriteBookkeeping(s.I(), right_childref, right_child.children);
    BookkeepingModel.lemmaRefInGraphPreservedWriteBookkeeping(s.I(), right_childref, right_child.children, left_childref);

    writeBookkeeping(s, right_childref, right_child.children);

    BookkeepingModel.lemmaChildrenConditionsOfReplace1With2(s.I(), fparent_children, slot as int, left_childref, right_childref);

    var rep := Replace1with2(fparent_children, left_childref, right_childref, slot);
    writeBookkeeping(s, parentref, Some(rep));
  }

  method splitCacheChanges(s: ImplVariables, left_childref: BT.G.Reference,
      right_childref: BT.G.Reference, parentref: BT.G.Reference, slot: uint64, 
      num_children_left: uint64, pivot: Key, linear left_child: Node, linear right_child: Node)
  requires s.ready
  requires s.W()
  requires s.cache.ptr(parentref).Some?
  requires BT.WFNode(s.cache.I()[parentref])
  requires s.cache.ptr(parentref).value.I().children.Some?
  requires 0 <= slot as int < |s.cache.ptr(parentref).value.I().children.value|
  requires left_child.Inv()
  requires right_child.Inv()
  requires |s.cache.I()| <= 0x10000 - 2
  requires left_childref != parentref
  requires right_childref != parentref
  requires PivotInsertable(s.cache.I()[parentref].pivotTable, (slot+1) as int, pivot)
  modifies s.Repr()
  ensures s.W()
  ensures (forall o | o in s.Repr() :: o in old(s.Repr()) || fresh(o))
  ensures s.I() == SplitModel.splitCacheChanges(old(s.I()), left_childref, right_childref,
    parentref, slot as int, num_children_left as int, pivot, left_child.I(), right_child.I())
  ensures s.ready
  {
    SplitModel.reveal_splitCacheChanges();
    s.cache.Insert(left_childref, left_child);
    s.cache.Insert(right_childref, right_child);
    s.cache.SplitParent(parentref, slot as uint64, pivot, left_childref, right_childref);
  }

  method splitDoChanges(s: ImplVariables, linear child: Node, left_childref: BT.G.Reference,
      right_childref: BT.G.Reference, parentref: BT.G.Reference, fparent_pivots: PivotTable,
      fparent_children: seq<BT.G.Reference>, slot: uint64)
  requires s.ready
  requires Inv(s)
  requires child.Inv()
  requires BT.WFNode(child.I())
  requires s.cache.ptr(parentref).Some?
  requires BT.WFNode(s.cache.I()[parentref])
  requires fparent_pivots == s.cache.I()[parentref].pivotTable
  requires Some(fparent_children) == s.cache.I()[parentref].children
  requires 0 <= slot as int < |fparent_children|
  requires |fparent_children| < MaxNumChildren()
  requires |child.buckets| >= 2
  requires left_childref != parentref
  requires right_childref != parentref
  requires BookkeepingModel.ChildrenConditions(s.I(), Some(fparent_children))
  requires BookkeepingModel.ChildrenConditions(s.I(), child.children)
  requires |s.ephemeralIndirectionTable.I().graph| <= IT.MaxSize() - 3
  modifies s.Repr()
  ensures WellUpdated(s)
  ensures s.I() == SplitModel.splitDoChanges(old(s.I()), old(child.I()), left_childref,
    right_childref, parentref, fparent_children, slot as int)
  ensures s.ready
  {
    var len := lseq_length_as_uint64(child.buckets);
    var num_children_left := len / 2;
    var pivot := ComputeGetKey(child.pivotTable, num_children_left);
    
    SplitModel.reveal_splitDoChanges();

    var insertable := ComputePivotInsertable(fparent_pivots, slot+1, pivot);
    if insertable {
      SplitModel.lemmaChildrenConditionsSplitChild(s.I(), child.I(), num_children_left as int);

      linear var left_child := child.SplitChildLeft(num_children_left);
      linear var right_child := child.SplitChildRight(num_children_left);

      splitBookkeeping(s, left_childref, right_childref, parentref,
        fparent_children, left_child, right_child, slot as uint64);
      splitCacheChanges(s, left_childref, right_childref, parentref,
        slot as uint64, num_children_left as uint64, pivot, left_child, right_child);
    } else {
      print "giving up; split can't run because new pivots will not be strictly sorted";
    }
    var _ := FreeNode(child);
  }

  method splitChild(s: ImplVariables, parentref: BT.G.Reference, 
    childref: BT.G.Reference, slot: uint64, lbound: Key, ubound: Option<Key>,
    fparent_pivots: PivotTable, fparent_children: Option<seq<BT.G.Reference>>)
  requires s.ready
  requires Inv(s)
  requires s.cache.ptr(childref).Some?
  requires s.cache.ptr(parentref).Some?
  requires s.cache.I()[parentref].children.Some?
  requires fparent_pivots == s.cache.I()[parentref].pivotTable
  requires fparent_children == s.cache.I()[parentref].children
  requires 0 <= slot as int < |fparent_children.value|
  requires fparent_children.value[slot] == childref
  requires |fparent_children.value| < MaxNumChildren()
  requires BT.ValidSplitKey(s.cache.I()[childref], lbound, ubound)
  requires BookkeepingModel.ChildrenConditions(s.I(), fparent_children)
  requires BookkeepingModel.ChildrenConditions(s.I(), s.cache.I()[childref].children)
  requires |s.ephemeralIndirectionTable.I().graph| <= IT.MaxSize() - 3
  modifies s.Repr()
  ensures s.ready
  ensures WellUpdated(s)
  ensures s.I() == SplitModel.splitChild(old(s.I()), parentref, childref, slot as int, lbound, ubound)
  {
    SplitModel.reveal_splitChild();

    linear var child := s.cache.NodeCutOff(childref, lbound, ubound);
    assert child.I() == BT.CutoffNode(s.cache.I()[childref], lbound, ubound);
    SplitModel.lemmaChildrenConditionsCutoffNode(s.I(), s.cache.I()[childref], lbound, ubound);
    assert BT.WFNode(child.I());

    if (|child.pivotTable| as uint64 == 2) {
      // TODO there should be an operation which just
      // cuts off the node and doesn't split it.
      print "giving up; doSplit can't run because child pivots can't be splitted\n";
      var _ := FreeNode(child);
    } else {
      var len := lseq_length_as_uint64(child.buckets);
      var num_children_left := len / 2;
      var pivot := ComputeGetKey(child.pivotTable, num_children_left);

      BookkeepingModel.getFreeRefDoesntEqual(s.I(), parentref);

      var left_childref := getFreeRef(s);
      if left_childref.None? {
        print "giving up; doSplit can't allocate left_childref\n";
        var _ := FreeNode(child);
      } else {
        BookkeepingModel.getFreeRef2DoesntEqual(s.I(), left_childref.value, parentref);
        var right_childref := getFreeRef2(s, left_childref.value);
        if right_childref.None? {
          print "giving up; doSplit can't allocate right_childref\n";
          var _ := FreeNode(child);
        } else {
          splitDoChanges(s, child, left_childref.value, right_childref.value,
            parentref, fparent_pivots, fparent_children.value, slot as uint64);
        }
      }
    }
  }

  method doSplit(s: ImplVariables, parentref: BT.G.Reference, childref: BT.G.Reference, slot: uint64)
  requires s.ready
  requires Inv(s)
  requires s.cache.ptr(childref).Some?
  requires s.cache.ptr(parentref).Some?
  requires childref in s.ephemeralIndirectionTable.I().graph
  requires parentref in s.ephemeralIndirectionTable.I().graph
  requires s.cache.I()[parentref].children.Some?
  requires 0 <= slot as int < |s.cache.I()[parentref].children.value|
  requires s.cache.I()[parentref].children.value[slot] == childref
  requires |s.cache.I()[parentref].buckets| <= MaxNumChildren() - 1
  requires |s.ephemeralIndirectionTable.I().graph| <= IT.MaxSize() - 3
  modifies s.Repr()
  ensures WellUpdated(s)
  ensures s.ready
  ensures s.I() == SplitModel.doSplit(old(s.I()), parentref, childref, slot as int);
  {
    SplitModel.reveal_doSplit();

    if s.frozenIndirectionTable != null {
      var b := s.frozenIndirectionTable.HasEmptyLoc(parentref);
      if b {
        print "giving up; split can't run because frozen isn't written";
        return;
      }
    }

    ghost var fused_parent := s.cache.I()[parentref];
    ghost var fused_child := s.cache.I()[childref]; 
    var fparent_pivots, fparent_children := s.cache.GetNodeInfo(parentref);
    var fchild_pivots, _ := s.cache.GetNodeInfo(childref);

    var childlbound := KeyspaceImpl.cmp(fchild_pivots[0], fparent_pivots[slot]);
    var childubound := KeyspaceImpl.cmp(fparent_pivots[slot+1], 
      fchild_pivots[|fchild_pivots| as uint64 -1]);

    if childlbound > 0 || childubound > 0 {
      print "giving up; split can't run because splitted keys are not in bound";
      return;
    }

    BookkeepingModel.lemmaChildrenConditionsOfNode(s.I(), parentref);
    BookkeepingModel.lemmaChildrenConditionsOfNode(s.I(), childref);

    var lbound := ComputeGetKey(fparent_pivots, slot);
    var ubound := None;
    if fparent_pivots[slot+1].Element? {
      var ukey := ComputeGetKey(fparent_pivots, slot+1);
      ubound := Some(ukey);
    }
    assert lbound == BT.getlbound(fused_parent, slot as int);
    assert ubound == BT.getubound(fused_parent, slot as int);

    var childvalid := computeValidSplitKey(s.cache, childref, fchild_pivots, lbound, ubound);
    var parentvalid := computeValidSplitKey(s.cache, parentref, fparent_pivots, lbound, ubound);

    if childvalid && parentvalid {
      assert BT.ValidSplitKey(fused_parent, lbound, ubound);
      assert BT.ValidSplitKey(fused_child, lbound, ubound);
     
      splitChild(s, parentref, childref, slot, lbound, ubound, fparent_pivots, fparent_children);
    } else {
      print "giving up; split can't run because bounds checking failed";
    }
  }
}
