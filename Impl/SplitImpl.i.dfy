// Copyright 2018-2021 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, and University of Washington
// SPDX-License-Identifier: BSD-2-Clause

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

  import opened BucketWeights
  import opened BucketImpl
  import opened Bounds
  import opened KeyType
  import opened BoundedPivotsLib
  import opened TranslationImpl

  import opened NativeTypes

  method computeSplitChildrenWeight(shared buckets: lseq<MutBucket>, num_children_left: uint64, len: uint64) returns (b: bool)
  requires MutBucket.InvLseq(buckets)
  requires 1 <= num_children_left as int < len as int == |buckets|
  ensures b == BT.SplitChildrenWeight(MutBucket.ILseq(buckets), num_children_left as int)
  {
    ghost var bs := MutBucket.ILseq(buckets);
    assert bs[num_children_left..] == bs[num_children_left..len];

    var succ, weight := MutBucket.tryComputeWeightOfSeq(buckets, 0, num_children_left);
    if !succ || weight > MaxTotalBucketWeightUint64() {
      return false;
    }

    succ, weight := MutBucket.tryComputeWeightOfSeq(buckets, num_children_left, len);
    return succ && weight <= MaxTotalBucketWeightUint64();
  }

  method {:timeLimitMultiplier 2} splitBookkeeping(linear inout s: ImplVariables, left_childref: BT.G.Reference,
    right_childref: BT.G.Reference, parentref: BT.G.Reference, 
    fparent_children: seq<BT.G.Reference>, shared left_child: Node, 
    shared right_child: Node, slot: uint64)
  requires old_s.Inv()
  requires 0 <= slot as int < |fparent_children|
  requires slot as int < MaxNumChildren()
  requires left_child.Inv()
  requires right_child.Inv()
  requires old_s.Ready?
  requires BookkeepingModel.ChildrenConditions(old_s.I(), left_child.children)
  requires BookkeepingModel.ChildrenConditions(old_s.I(), right_child.children)
  requires BookkeepingModel.ChildrenConditions(old_s.I(), Some(fparent_children))
  requires |fparent_children| < MaxNumChildren()
  requires |old_s.ephemeralIndirectionTable.I().graph| <= IT.MaxSize() - 3

  ensures s.Ready?
  ensures s.W()
  ensures s.I() == SplitModel.splitBookkeeping(old_s.I(), left_childref, right_childref, parentref, fparent_children, left_child.I(), right_child.I(), slot as int)
  ensures s.cache == old_s.cache
  ensures LruModel.I(s.lru.Queue()) == LruModel.I(old_s.lru.Queue()) + {left_childref, right_childref, parentref};
  ensures s.WriteAllocConditions()
  {
    SplitModel.reveal_splitBookkeeping();

    BookkeepingModel.lemmaChildrenConditionsPreservedWriteBookkeeping(s.I(), left_childref, left_child.children, right_child.children);
    BookkeepingModel.lemmaChildrenConditionsPreservedWriteBookkeeping(s.I(), left_childref, left_child.children, Some(fparent_children));
    BookkeepingModel.lemmaRefInGraphOfWriteBookkeeping(s.I(), left_childref, left_child.children);

    writeBookkeeping(inout s, left_childref, left_child.children);

    BookkeepingModel.lemmaChildrenConditionsPreservedWriteBookkeeping(s.I(), right_childref, right_child.children, Some(fparent_children));
    BookkeepingModel.lemmaRefInGraphOfWriteBookkeeping(s.I(), right_childref, right_child.children);
    BookkeepingModel.lemmaRefInGraphPreservedWriteBookkeeping(s.I(), right_childref, right_child.children, left_childref);

    writeBookkeeping(inout s, right_childref, right_child.children);

    BookkeepingModel.lemmaChildrenConditionsOfReplace1With2(s.I(), fparent_children, slot as int, left_childref, right_childref);

    var rep := Replace1with2(fparent_children, left_childref, right_childref, slot);
    writeBookkeeping(inout s, parentref, Some(rep));
  }

  method splitCacheChanges(linear inout s: ImplVariables, left_childref: BT.G.Reference,
      right_childref: BT.G.Reference, parentref: BT.G.Reference, slot: uint64, 
      num_children_left: uint64, pivot: Key, linear left_child: Node, linear right_child: Node)
  requires old_s.Ready?
  requires old_s.WriteAllocConditions()
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

  ensures s.Ready?
  ensures s.W()
  ensures s.I() == SplitModel.splitCacheChanges(old_s.I(), left_childref, right_childref,
    parentref, slot as int, num_children_left as int, pivot, left_child.I(), right_child.I())
  ensures s.cache.I().Keys == old_s.cache.I().Keys + {left_childref, right_childref, parentref}
  ensures s.lru == old_s.lru
  ensures s.WriteAllocConditions()
  {
    SplitModel.reveal_splitCacheChanges();
    inout s.cache.Insert(left_childref, left_child);
    inout s.cache.Insert(right_childref, right_child);
    inout s.cache.SplitParent(parentref, slot as uint64, pivot, left_childref, right_childref);

    ghost var s' := SplitModel.splitCacheChanges(old_s.I(), left_childref, right_childref,
    parentref, slot as int, num_children_left as int, pivot, left_child.I(), right_child.I());
    assert s.W();
    assert s' == s.I();
  }

  method splitDoChanges(linear inout s: ImplVariables, linear child: Node, left_childref: BT.G.Reference,
      right_childref: BT.G.Reference, parentref: BT.G.Reference, fparent_pivots: PivotTable,
      fparent_children: seq<BT.G.Reference>, slot: uint64)
  requires old_s.Ready?
  requires old_s.Inv()
  requires child.Inv()
  requires |child.pivotTable| < 0x4000_0000_0000_0000
  requires WFPivots(child.pivotTable)
  requires NumBuckets(child.pivotTable) == |child.buckets|
  requires |child.edgeTable| == |child.buckets| 
  requires child.children.Some? ==> |child.children.value| == |child.buckets|
  requires old_s.cache.ptr(parentref).Some?
  requires BT.WFNode(old_s.cache.I()[parentref])
  requires fparent_pivots == old_s.cache.I()[parentref].pivotTable
  requires Some(fparent_children) == old_s.cache.I()[parentref].children
  requires 0 <= slot as int < |fparent_children|
  requires |fparent_children| < MaxNumChildren()
  requires |child.buckets| >= 2
  requires left_childref != parentref
  requires right_childref != parentref
  requires BookkeepingModel.ChildrenConditions(old_s.I(), Some(fparent_children))
  requires BookkeepingModel.ChildrenConditions(old_s.I(), child.children)
  requires |old_s.ephemeralIndirectionTable.I().graph| <= IT.MaxSize() - 3

  ensures s.Ready?
  ensures s.W()
  ensures s.I() == SplitModel.splitDoChanges(old_s.I(), old(child.I()), left_childref, right_childref, parentref, fparent_children, slot as int)
  ensures s.WriteAllocConditions()
  ensures LruModel.I(s.lru.Queue()) == s.cache.I().Keys
  {
    var len := lseq_length_as_uint64(child.buckets);
    var num_children_left := len / 2;
    var pivot := ComputeGetKey(child.pivotTable, num_children_left);
    
    SplitModel.reveal_splitDoChanges();

    var insertable := ComputePivotInsertable(fparent_pivots, slot+1, pivot);
    if insertable {
      var boundedweight := computeSplitChildrenWeight(child.buckets, num_children_left, len);
      if boundedweight {
        SplitModel.lemmaChildrenConditionsSplitChild(s.I(), child.I(), num_children_left as int);

        linear var left_child, right_child := child.SplitChild(num_children_left);
        splitBookkeeping(inout s, left_childref, right_childref, parentref,
          fparent_children, left_child, right_child, slot as uint64);
        splitCacheChanges(inout s, left_childref, right_childref, parentref,
          slot as uint64, num_children_left as uint64, pivot, left_child, right_child);

        calc == {
          LruModel.I(s.lru.Queue());
          LruModel.I(old_s.lru.Queue()) + {left_childref, right_childref, parentref};
          old_s.cache.I().Keys + {left_childref, right_childref, parentref};
          s.cache.I().Keys;
        }
      } else {
        var _ := FreeNode(child);
        print "giving up; split can't run because new children will be overweight";
      }
    } else {
      var _ := FreeNode(child);
      print "giving up; split can't run because new pivots will not be strictly sorted";
    }
  }

  method doSplit(linear inout s: ImplVariables, parentref: BT.G.Reference, childref: BT.G.Reference, slot: uint64, refUpperBound: uint64)
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
  requires forall r | r in old_s.ephemeralIndirectionTable.graph :: r <= refUpperBound
  requires old_s.ephemeralIndirectionTable.refUpperBound == refUpperBound
  ensures s.W()
  ensures s.Ready?
  ensures s.I() == SplitModel.doSplit(old_s.I(), parentref, childref, slot as int, refUpperBound);
  ensures s.WriteAllocConditions()
  ensures LruModel.I(s.lru.Queue()) == s.cache.I().Keys
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
      var fparent_pivots, fparent_edges, fparent_children := s.cache.GetNodeInfo(parentref);
      var fchild_pivots, _, _ := s.cache.GetNodeInfo(childref);

      var inrange := ComputeParentKeysInChildRange(fparent_pivots, fparent_edges, fchild_pivots, slot);
      if !inrange {
        print "giving up; split can't run because splitted keys are not in bound";
      } else {
        var bucketsfit := fparent_edges[slot].None?;
        if fparent_edges[slot].Some? {
          var lcp := ComputePivotLcp(fparent_pivots[slot], fparent_pivots[slot+1]);
          bucketsfit := s.cache.NodeBucketsWillFitInPkv(childref, fparent_edges[slot].value, lcp);
        }

        if bucketsfit {
          BookkeepingModel.lemmaChildrenConditionsOfNode(s.I(), parentref);
          BookkeepingModel.lemmaChildrenConditionsOfNode(s.I(), childref);

          linear var child := s.cache.NodeRestrictAndTranslateChild(parentref, childref, slot);
          if (|child.pivotTable| as uint64 == 2) {
            // TODO there should be an operation which just
            // cuts off the node and doesn't split it.
            print "giving up; doSplit can't run because child pivots can't be splitted\n";
            var _ := FreeNode(child);
          } else {
            SplitModel.lemmaChildrenConditionsRestrictAndTranslateChild(s.I(), fused_parent, fused_child, slot as int);
            BookkeepingModel.getFreeRefDoesntEqual(s.I(), parentref, refUpperBound);

            var left_childref := getFreeRef(s);
            if left_childref.None? {
              print "giving up; doSplit can't allocate left_childref\n";
              var _ := FreeNode(child);
            } else {
              BookkeepingModel.getFreeRef2DoesntEqual(s.I(), left_childref.value, parentref, refUpperBound);
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
        } else {
          print "giving up; doSplit can't run because splitted children cannot be marshalled\n";
        }
      }
    }
  }

  method split(linear inout s: ImplVariables, parentref: BT.G.Reference, childref: BT.G.Reference, slot: uint64)
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
  requires old_s.totalCacheSize() <= MaxCacheSize() - 2

  ensures s.WFBCVars() && s.Ready?
  ensures IOModel.betree_next(old_s.I(), s.I())
  {
    var refUpperBound := s.ephemeralIndirectionTable.refUpperBound;
    old_s.ephemeralIndirectionTable.UpperBounded();
    SplitModel.doSplitCorrect(s.I(), parentref, childref, slot as int, refUpperBound);
    doSplit(inout s, parentref, childref, slot, refUpperBound);
  }
}
