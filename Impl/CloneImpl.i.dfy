// Copyright 2018-2021 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, and University of Washington
// SPDX-License-Identifier: BSD-2-Clause

include "CloneModel.i.dfy"
include "FlushPolicyImpl.i.dfy"
include "DiskOpImpl.i.dfy"
include "BookkeepingImpl.i.dfy"
include "MainDiskIOHandler.s.dfy"

module CloneImpl {
  import CloneModel
  import IOModel
  import opened NodeImpl
  import opened IOImpl
  import opened BookkeepingImpl
  import opened MainDiskIOHandler
  import opened InterpretationDiskOps
  import opened DiskOpImpl
  import opened StateBCImpl
  import opened ViewOp
  import opened DiskOpModel
  import opened FlushPolicyImpl
  import opened BoundedPivotsLib
  import opened KeyType
  import opened Bounds

  method doClone(linear inout s: ImplVariables, from: Key, to: Key) returns (success: bool)
  requires old_s.Inv() && old_s.Ready?
  requires BT.G.Root() in old_s.I().cache
  requires |old_s.ephemeralIndirectionTable.I().graph| <= IT.MaxSize() - 1
  ensures s.Ready?
  ensures s.W()
  ensures s.WriteAllocConditions() 
  ensures LruModel.I(s.lru.Queue()) == s.cache.I().Keys;
  ensures (s.I(), success) == CloneModel.doClone(old_s.I(), from, to)
  {
    CloneModel.reveal_doClone();
    var root := BT.G.Root();
    success := true;

    if s.frozenIndirectionTable.lSome? {
      var b := s.frozenIndirectionTable.value.HasEmptyLoc(root);
      if b {
        print "giving up; clone can't run because frozen isn't written";
        success := false;
      }
    }

    if success {
      var oldroot_pivots, _, oldroot_children := s.cache.GetNodeInfo(root);
      BookkeepingModel.lemmaChildrenConditionsOfNode(s.I(), root);

      var contains := ComputeContainsAllKeys(oldroot_pivots);
      if (to != [] && oldroot_children.Some? && contains) {
        linear var rootopt := s.cache.NodeCloneNewRoot(root, from, to);
        linear match rootopt {
          case lNone() => { success := false; }
          case lSome(node) => {
            CloneModel.lemmaChildrenConditionsCloneNewRoot(s.I(), s.I().cache[root], from, to);
            writeBookkeeping(inout s, root, node.children);
            inout s.cache.Overwrite(root, node);
            assert (s.I(), success) == CloneModel.doClone(old_s.I(), from, to);
          }
        }
      } else {
        success := false;
      }
    }
  }

  method clone(linear inout s: ImplVariables, io: DiskIOHandler, from: Key, to: Key) returns (success: bool)
  requires io.initialized()
  requires old_s.Inv() && old_s.Ready?
  modifies io
  ensures s.WFBCVars()
  ensures ValidDiskOp(diskOp(IIO(io)))
  ensures IDiskOp(diskOp(IIO(io))).jdop.NoDiskOp?
  ensures success ==>
    BBC.Next(old_s.I(), s.I(), IDiskOp(diskOp(IIO(io))).bdop, AdvanceOp(UI.CloneOp(BT.CloneMap(from, to)), true))
  ensures !success ==>
    IOModel.betree_next_dop(old_s.I(), s.I(), IDiskOp(diskOp(IIO(io))).bdop)
  {
    var indirectionTableSize := s.ephemeralIndirectionTable.GetSize();
    if (!(indirectionTableSize <= IT.MaxSizeUint64() - 3)) {
      assert IOModel.noop(old_s.I(), s.I());
      success := false;
    } else {
      var rootLookup := s.cache.InCache(BT.G.Root());
      if !rootLookup {
        if s.TotalCacheSize() <= MaxCacheSizeUint64() - 1 {
          PageInNodeReq(inout s, io, BT.G.Root());
          success := false;
        } else {
          print "insert: root not in cache, but cache is full\n";
          assert IOModel.noop(old_s.I(), s.I());
          success := false;
        }
      } else {
        CloneModel.doCloneCorrect(old_s.I(), from, to);
        success := doClone(inout s, from, to);
        assert (s.I(), success) == CloneModel.doClone(old_s.I(), from, to);
      }
    }
  }
}