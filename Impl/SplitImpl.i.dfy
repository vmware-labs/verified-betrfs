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

  method computeValidSplitKey(shared cache: CacheImpl.LMutCache, ref: BT.G.Reference,
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

  method splitBookkeeping(linear inout s: ImplVariables, left_childref: BT.G.Reference,
    right_childref: BT.G.Reference, parentref: BT.G.Reference, 
    fparent_children: seq<BT.G.Reference>, shared left_child: Node, 
    shared right_child: Node, slot: uint64)
  requires old_s.BCInv()
  requires 0 <= slot as int < |fparent_children|
  requires slot as int < MaxNumChildren()
  requires left_child.Inv()
  requires right_child.Inv()
  requires old_s.Ready?
  requires BookkeepingModel.ChildrenConditions(old_s.IBlockCache(), left_child.children)
  requires BookkeepingModel.ChildrenConditions(old_s.IBlockCache(), right_child.children)
  requires BookkeepingModel.ChildrenConditions(old_s.IBlockCache(), Some(fparent_children))
  requires |fparent_children| < MaxNumChildren()
  requires |old_s.ephemeralIndirectionTable.I().graph| <= IT.MaxSize() - 3

  ensures s.Ready?
  ensures s.W()
  ensures s.IBlockCache() == SplitModel.splitBookkeeping(old_s.IBlockCache(), left_childref, right_childref, 
    parentref, fparent_children, left_child.I(), right_child.I(), slot as int)
  {
    SplitModel.reveal_splitBookkeeping();

    BookkeepingModel.lemmaChildrenConditionsPreservedWriteBookkeeping(s.IBlockCache(), left_childref, left_child.children, right_child.children);
    BookkeepingModel.lemmaChildrenConditionsPreservedWriteBookkeeping(s.IBlockCache(), left_childref, left_child.children, Some(fparent_children));
    BookkeepingModel.lemmaRefInGraphOfWriteBookkeeping(s.IBlockCache(), left_childref, left_child.children);

    writeBookkeeping(inout s, left_childref, left_child.children);

    BookkeepingModel.lemmaChildrenConditionsPreservedWriteBookkeeping(s.IBlockCache(), right_childref, right_child.children, Some(fparent_children));
    BookkeepingModel.lemmaRefInGraphOfWriteBookkeeping(s.IBlockCache(), right_childref, right_child.children);
    BookkeepingModel.lemmaRefInGraphPreservedWriteBookkeeping(s.IBlockCache(), right_childref, right_child.children, left_childref);

    writeBookkeeping(inout s, right_childref, right_child.children);

    BookkeepingModel.lemmaChildrenConditionsOfReplace1With2(s.IBlockCache(), fparent_children, slot as int, left_childref, right_childref);

    var rep := Replace1with2(fparent_children, left_childref, right_childref, slot);
    writeBookkeeping(inout s, parentref, Some(rep));
  }

  method splitCacheChanges(linear inout s: ImplVariables, left_childref: BT.G.Reference,
      right_childref: BT.G.Reference, parentref: BT.G.Reference, slot: uint64, 
      num_children_left: uint64, pivot: Key, linear left_child: Node, linear right_child: Node)
  requires old_s.Ready?
  requires old_s.W()
  requires old_s.cache.ptr(parentref).Some?
  requires BT.WFNode(old_s.cache.I()[parentref])
  requires old_s.cache.ptr(parentref).value.I().children.Some?
  requires 0 <= slot as int < |old_s.cache.ptr(parentref).value.I().children.value|
  requires left_child.Inv()
  requires right_child.Inv()
  requires |old_s.cache.I()| <= 0x10000 - 2
  requires left_childref != parentref
  requires right_childref != parentref
  requires PivotInsertable(old_s.cache.I()[parentref].pivotTable, (slot+1) as int, pivot)

  ensures s.W()
  ensures s.IBlockCache() == SplitModel.splitCacheChanges(old_s.IBlockCache(), left_childref, right_childref,
    parentref, slot as int, num_children_left as int, pivot, left_child.I(), right_child.I())
  ensures s.Ready?
  {
    SplitModel.reveal_splitCacheChanges();
    inout s.cache.Insert(left_childref, left_child);
    inout s.cache.Insert(right_childref, right_child);
    inout s.cache.SplitParent(parentref, slot as uint64, pivot, left_childref, right_childref);
  }
/*

  method splitDoChanges(linear inout s: ImplVariables, linear child: Node, left_childref: BT.G.Reference,
      right_childref: BT.G.Reference, parentref: BT.G.Reference, fparent_pivots: PivotTable,
      fparent_children: seq<BT.G.Reference>, slot: uint64)
  requires old_s.Ready?
  requires old_s.Inv()
  requires child.Inv()
  requires BT.WFNode(child.I())
  requires old_s.cache.ptr(parentref).Some?
  requires BT.WFNode(old_s.cache.I()[parentref])
  requires fparent_pivots == old_s.cache.I()[parentref].pivotTable
  requires Some(fparent_children) == old_s.cache.I()[parentref].children
  requires 0 <= slot as int < |fparent_children|
  requires |fparent_children| < MaxNumChildren()
  requires |child.buckets| >= 2
  requires left_childref != parentref
  requires right_childref != parentref
  requires BookkeepingModel.ChildrenConditions(old_s.IBlockCache(), Some(fparent_children))
  requires BookkeepingModel.ChildrenConditions(old_s.IBlockCache(), child.children)
  requires |old_s.ephemeralIndirectionTable.I().graph| <= IT.MaxSize() - 3
  ensures s.W()
  ensures s.IBlockCache() == SplitModel.splitDoChanges(old_s.IBlockCache(), old(child.I()), left_childref,
    right_childref, parentref, fparent_children, slot as int)
  ensures s.Ready?
  {
    var len := lseq_length_as_uint64(child.buckets);
    var num_children_left := len / 2;
    var pivot := ComputeGetKey(child.pivotTable, num_children_left);
    
    SplitModel.reveal_splitDoChanges();

    var insertable := ComputePivotInsertable(fparent_pivots, slot+1, pivot);
    if insertable {
      SplitModel.lemmaChildrenConditionsSplitChild(s.IBlockCache(), child.I(), num_children_left as int);

      linear var left_child := child.SplitChildLeft(num_children_left);
      linear var right_child := child.SplitChildRight(num_children_left);

      splitBookkeeping(inout s, left_childref, right_childref, parentref,
        fparent_children, left_child, right_child, slot as uint64);
      splitCacheChanges(inout s, left_childref, right_childref, parentref,
        slot as uint64, num_children_left as uint64, pivot, left_child, right_child);
    } else {
      print "giving up; split can't run because new pivots will not be strictly sorted";
    }
    var _ := FreeNode(child);
  }

  method splitChild(linear inout s: ImplVariables, parentref: BT.G.Reference, 
    childref: BT.G.Reference, slot: uint64, lbound: Key, ubound: Option<Key>,
    fparent_pivots: PivotTable, fparent_children: Option<seq<BT.G.Reference>>)
  requires old_s.Ready?
  requires old_s.Inv()
  requires old_s.cache.ptr(childref).Some?
  requires old_s.cache.ptr(parentref).Some?
  requires old_s.cache.I()[parentref].children.Some?
  requires fparent_pivots == old_s.cache.I()[parentref].pivotTable
  requires fparent_children == old_s.cache.I()[parentref].children
  requires 0 <= slot as int < |fparent_children.value|
  requires fparent_children.value[slot] == childref
  requires |fparent_children.value| < MaxNumChildren()
  requires BT.ValidSplitKey(old_s.cache.I()[childref], lbound, ubound)
  requires BookkeepingModel.ChildrenConditions(old_s.IBlockCache(), fparent_children)
  requires BookkeepingModel.ChildrenConditions(old_s.IBlockCache(), old_s.cache.I()[childref].children)
  requires |old_s.ephemeralIndirectionTable.I().graph| <= IT.MaxSize() - 3
  ensures s.Ready?
  ensures s.W()
  ensures s.IBlockCache() == SplitModel.splitChild(old_s.IBlockCache(), parentref, childref, slot as int, lbound, ubound)
  {
    SplitModel.reveal_splitChild();

    linear var child := s.cache.NodeCutOff(childref, lbound, ubound);
    assert child.I() == BT.CutoffNode(s.cache.I()[childref], lbound, ubound);
    SplitModel.lemmaChildrenConditionsCutoffNode(s.IBlockCache(), s.cache.I()[childref], lbound, ubound);
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

      BookkeepingModel.getFreeRefDoesntEqual(s.IBlockCache(), parentref);

      var left_childref := getFreeRef(s);
      if left_childref.None? {
        print "giving up; doSplit can't allocate left_childref\n";
        var _ := FreeNode(child);
      } else {
        BookkeepingModel.getFreeRef2DoesntEqual(s.IBlockCache(), left_childref.value, parentref);
        var right_childref := getFreeRef2(s, left_childref.value);
        if right_childref.None? {
          print "giving up; doSplit can't allocate right_childref\n";
          var _ := FreeNode(child);
        } else {
          splitDoChanges(inout s, child, left_childref.value, right_childref.value,
            parentref, fparent_pivots, fparent_children.value, slot as uint64);
        }
      }
    }
  }

  method doSplit(linear inout s: ImplVariables, parentref: BT.G.Reference, childref: BT.G.Reference, slot: uint64)
  requires old_s.Ready?
  requires old_s.Inv()
  requires old_s.cache.ptr(childref).Some?
  requires old_s.cache.ptr(parentref).Some?
  requires childref in old_s.ephemeralIndirectionTable.I().graph
  requires parentref in old_s.ephemeralIndirectionTable.I().graph
  requires old_s.cache.I()[parentref].children.Some?
  requires 0 <= slot as int < |old_s.cache.I()[parentref].children.value|
  requires old_s.cache.I()[parentref].children.value[slot] == childref
  requires |old_s.cache.I()[parentref].buckets| <= MaxNumChildren() - 1
  requires |old_s.ephemeralIndirectionTable.I().graph| <= IT.MaxSize() - 3
  ensures s.W()
  ensures s.Ready?
  ensures s.IBlockCache() == SplitModel.doSplit(old_s.IBlockCache(), parentref, childref, slot as int);
  {
    SplitModel.reveal_doSplit();
    var b := false;

    if s.frozenIndirectionTable.lSome? {
      b := s.frozenIndirectionTable.value.HasEmptyLoc(parentref);
    }

    if b {
      print "giving up; split can't run because frozen isn't written";
    } else {
      ghost var fused_parent := s.cache.I()[parentref];
      ghost var fused_child := s.cache.I()[childref]; 
      var fparent_pivots, fparent_children := s.cache.GetNodeInfo(parentref);
      var fchild_pivots, _ := s.cache.GetNodeInfo(childref);

      var childlbound := KeyspaceImpl.cmp(fchild_pivots[0], fparent_pivots[slot]);
      var childubound := KeyspaceImpl.cmp(fparent_pivots[slot+1], 
        fchild_pivots[|fchild_pivots| as uint64 -1]);

      if childlbound > 0 || childubound > 0 {
        print "giving up; split can't run because splitted keys are not in bound";
      } else {
        BookkeepingModel.lemmaChildrenConditionsOfNode(s.IBlockCache(), parentref);
        BookkeepingModel.lemmaChildrenConditionsOfNode(s.IBlockCache(), childref);

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
        
          splitChild(inout s, parentref, childref, slot, lbound, ubound, fparent_pivots, fparent_children);
        } else {
          print "giving up; split can't run because bounds checking failed";
        }
      }
    }
  }
  */
}
