include "BookkeepingImpl.i.dfy"
include "SplitModel.i.dfy"

module SplitImpl { 
  import opened IOImpl
  import opened BookkeepingImpl
  import SplitModel
  import opened StateImpl
  import opened NodeImpl
  import opened DiskOpImpl

  import opened Options
  import opened Maps
  import opened Sequences
  import opened Sets

  import opened BucketsLib
  import opened BucketWeights
  import opened Bounds
  import opened KeyType
  import PivotsLib

  import opened NativeTypes

  method splitBookkeeping(k: ImplConstants, s: ImplVariables, left_childref: BT.G.Reference, right_childref: BT.G.Reference, parentref: BT.G.Reference, fused_parent_children: seq<BT.G.Reference>, left_child: Node, right_child: Node, slot: uint64)
  requires Inv(k, s)
  requires 0 <= slot as int < |fused_parent_children|
  requires slot as int < MaxNumChildren()
  requires left_child.Inv()
  requires right_child.Inv()
  requires left_child.Repr !! s.Repr()
  requires right_child.Repr !! s.Repr()
  requires s.ready
  requires BookkeepingModel.ChildrenConditions(Ic(k), s.I(), left_child.children)
  requires BookkeepingModel.ChildrenConditions(Ic(k), s.I(), right_child.children)
  requires BookkeepingModel.ChildrenConditions(Ic(k), s.I(), Some(fused_parent_children))
  requires |fused_parent_children| < MaxNumChildren()
  requires |s.ephemeralIndirectionTable.I().graph| <= IndirectionTableModel.MaxSize() - 3
  modifies s.lru.Repr
  modifies s.ephemeralIndirectionTable.Repr
  modifies s.blockAllocator.Repr
  ensures s.ready
  ensures s.W()
  ensures forall o | o in s.lru.Repr :: o in old(s.lru.Repr) || fresh(o)
  ensures forall o | o in s.ephemeralIndirectionTable.Repr :: o in old(s.ephemeralIndirectionTable.Repr) || fresh(o)
  ensures forall o | o in s.blockAllocator.Repr :: o in old(s.blockAllocator.Repr) || fresh(o)
  ensures s.I() == SplitModel.splitBookkeeping(Ic(k), old(s.I()), left_childref, right_childref, parentref, fused_parent_children, left_child.I(), right_child.I(), slot as int);
  {
    SplitModel.reveal_splitBookkeeping();

    BookkeepingModel.lemmaChildrenConditionsPreservedWriteBookkeeping(Ic(k), s.I(), left_childref, left_child.children, right_child.children);
    BookkeepingModel.lemmaChildrenConditionsPreservedWriteBookkeeping(Ic(k), s.I(), left_childref, left_child.children, Some(fused_parent_children));
    BookkeepingModel.lemmaRefInGraphOfWriteBookkeeping(Ic(k), s.I(), left_childref, left_child.children);

    writeBookkeeping(k, s, left_childref, left_child.children);

    BookkeepingModel.lemmaChildrenConditionsPreservedWriteBookkeeping(Ic(k), s.I(), right_childref, right_child.children, Some(fused_parent_children));
    BookkeepingModel.lemmaRefInGraphOfWriteBookkeeping(Ic(k), s.I(), right_childref, right_child.children);
    BookkeepingModel.lemmaRefInGraphPreservedWriteBookkeeping(Ic(k), s.I(), right_childref, right_child.children, left_childref);

    writeBookkeeping(k, s, right_childref, right_child.children);

    BookkeepingModel.lemmaChildrenConditionsOfReplace1With2(Ic(k), s.I(), fused_parent_children, slot as int, left_childref, right_childref);

    var rep := Replace1with2(fused_parent_children, left_childref, right_childref, slot);
    writeBookkeeping(k, s, parentref, Some(rep));
  }

  method splitCacheChanges(s: ImplVariables, left_childref: BT.G.Reference,
      right_childref: BT.G.Reference, parentref: BT.G.Reference, slot: uint64, num_children_left: uint64, pivot: Key, left_child: Node, right_child: Node)
  requires s.ready
  requires s.W()
  requires s.cache.ptr(parentref).Some?
  requires IM.WFNode(s.cache.ptr(parentref).value.I())
  requires s.cache.ptr(parentref).value.I().children.Some?
  requires 0 <= slot as int < |s.cache.ptr(parentref).value.I().children.value|
  requires left_child.Inv()
  requires right_child.Inv()
  requires left_child.Repr !! s.Repr()
  requires right_child.Repr !! s.Repr()
  requires left_child.Repr !! right_child.Repr
  requires |s.cache.I()| <= 0x10000 - 2
  requires left_childref != parentref
  requires right_childref != parentref
  modifies s.Repr()
  modifies left_child.Repr // not really but it's easier to include this
  modifies right_child.Repr
  ensures s.W()
  ensures (forall o | o in s.Repr() :: o in old(s.Repr()) || o in old(left_child.Repr) || o in old(right_child.Repr) || fresh(o))
  ensures s.I() == SplitModel.splitCacheChanges(old(s.I()), left_childref, right_childref, parentref, slot as int, num_children_left as int, pivot, old(left_child.I()), old(right_child.I()))
  ensures s.ready
  {
    SplitModel.reveal_splitCacheChanges();
    s.cache.Insert(left_childref, left_child);
    s.cache.Insert(right_childref, right_child);
    s.cache.SplitParent(parentref, slot as uint64, pivot, left_childref, right_childref);
  }

  method splitDoChanges(k: ImplConstants, s: ImplVariables, child: Node,
      left_childref: BT.G.Reference, right_childref: BT.G.Reference, parentref: BT.G.Reference,
      fused_parent_children: seq<BT.G.Reference>, slot: uint64)
  requires Inv(k, s)
  requires child.Inv()

  requires s.ready
  requires parentref in s.cache.I()
  requires IM.WFNode(s.cache.I()[parentref]);
  requires IM.WFNode(child.I());
  requires s.cache.I()[parentref].children.Some?
  requires 0 <= slot as int < |s.cache.I()[parentref].children.value|
  requires 0 <= slot as int < |fused_parent_children|
  requires left_childref != parentref
  requires right_childref != parentref
  requires |child.buckets| >= 2
  requires BookkeepingModel.ChildrenConditions(Ic(k), s.I(), Some(fused_parent_children))
  requires BookkeepingModel.ChildrenConditions(Ic(k), s.I(), child.children)
  requires |fused_parent_children| < MaxNumChildren()
  requires |s.ephemeralIndirectionTable.I().graph| <= IndirectionTableModel.MaxSize() - 3

  modifies s.Repr()

  ensures WellUpdated(s)
  ensures s.I() == SplitModel.splitDoChanges(Ic(k), old(s.I()), old(child.I()), left_childref, right_childref, parentref, fused_parent_children, slot as int)
  ensures s.ready
  {
    var num_children_left := |child.buckets| as uint64 / 2;
    var pivot := child.pivotTable[num_children_left - 1];

    SplitModel.lemmaChildrenConditionsSplitChild(Ic(k), s.I(), child.I(), num_children_left as int);

    var left_child := child.SplitChildLeft(num_children_left as uint64);
    var right_child := child.SplitChildRight(num_children_left as uint64);

    splitBookkeeping(k, s, left_childref, right_childref, parentref, fused_parent_children, left_child, right_child, slot as uint64);
    splitCacheChanges(s, left_childref, right_childref, parentref, slot as uint64, num_children_left as uint64, pivot, left_child, right_child);

    SplitModel.reveal_splitDoChanges();
  }

  method doSplit(k: ImplConstants, s: ImplVariables, parentref: BT.G.Reference, childref: BT.G.Reference, slot: uint64)
  requires s.ready
  requires Inv(k, s)
  requires childref in s.ephemeralIndirectionTable.I().graph
  requires parentref in s.ephemeralIndirectionTable.I().graph
  requires s.cache.ptr(childref).Some?
  requires s.cache.ptr(parentref).Some?
  requires s.cache.I()[parentref].children.Some?
  requires 0 <= slot as int < |s.cache.I()[parentref].children.value|
  requires s.cache.I()[parentref].children.value[slot] == childref
  requires |s.cache.I()[parentref].buckets| <= MaxNumChildren() - 1
  requires |s.ephemeralIndirectionTable.I().graph| <= IndirectionTableModel.MaxSize() - 3
  modifies s.Repr()
  ensures WellUpdated(s)
  ensures s.ready
  ensures s.I() == SplitModel.doSplit(Ic(k), old(s.I()), parentref, childref, slot as int);
  {
    SplitModel.reveal_doSplit();

    if s.frozenIndirectionTable != null {
      var b := s.frozenIndirectionTable.HasEmptyLoc(parentref);
      if b {
        print "giving up; split can't run because frozen isn't written";
        return;
      }
    }

    var fused_parent_opt := s.cache.GetOpt(parentref);
    var fused_parent := fused_parent_opt.value;
    var fused_child_opt := s.cache.GetOpt(childref);
    var fused_child := fused_child_opt.value;

    BookkeepingModel.lemmaChildrenConditionsOfNode(Ic(k), s.I(), parentref);
    BookkeepingModel.lemmaChildrenConditionsOfNode(Ic(k), s.I(), childref);

    var lbound := (if slot > 0 then Some(fused_parent.pivotTable[slot - 1]) else None);
    var ubound := (if slot < |fused_parent.pivotTable| as uint64 then Some(fused_parent.pivotTable[slot]) else None);

    SplitModel.lemmaChildrenConditionsCutoffNode(Ic(k), s.I(), fused_child.I(), lbound, ubound);
    NodeModel.CutoffNodeCorrect(fused_child.I(), lbound, ubound);
    var child := NodeImpl.Node.CutoffNode(fused_child, lbound, ubound);
    assert IM.WFNode(child.I());

    if (|child.pivotTable| as uint64 == 0) {
      // TODO there should be an operation which just
      // cuts off the node and doesn't split it.
      print "giving up; doSplit can't run because child.pivots == 0\n";
      return;
    }

    BookkeepingModel.getFreeRefDoesntEqual(s.I(), parentref);

    var left_childref := getFreeRef(s);
    if left_childref.None? {
      print "giving up; doSplit can't allocate left_childref\n";
      return;
    }

    BookkeepingModel.getFreeRef2DoesntEqual(s.I(), left_childref.value, parentref);

    var right_childref := getFreeRef2(s, left_childref.value);
    if right_childref.None? {
      print "giving up; doSplit can't allocate right_childref\n";
      return;
    }

    splitDoChanges(k, s, child, left_childref.value, right_childref.value,
        parentref, fused_parent.children.value, slot as uint64);
  }
}
