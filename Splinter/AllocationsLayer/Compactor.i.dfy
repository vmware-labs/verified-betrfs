// Copyright 2018-2021 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, and University of Washington
// SPDX-License-Identifier: BSD-2-Clause

// include "../LikesAU.i.dfy"
// include "../Journal/MiniAllocator.i.dfy"   // tony: borrowing from Journal for now
include "../Betree/LinkedBranch.i.dfy"
include "../Betree/BranchSeq.i.dfy"
include "../Betree/OffsetMap.i.dfy"
include "MiniAllocator.i.dfy"
include "LikesAU.i.dfy"

module CompactorMod
{
  import opened LinkedBranchMod
  import opened BranchSeqMod
  import opened OffsetMapMod
  import opened MiniAllocatorMod
  import opened LikesAUMod
  import opened GenericDisk
  import opened Sequences

  type BranchDiskView = LinkedBranchMod.DiskView

// Transitions for each thread state machine, from the persective of the caller:
  //  Init(compact start), Internal, Commit, Abort
  datatype CompactThread = CompactThread(
    // Read-only inputs
    branchSeq: BranchSeq,
    offsetMap: OffsetMap,  // filter describing which keys from branchSeq should be preserved in output
    subdisk: BranchDiskView, // diskview containing exactly the part of the tree we are reading
    // Mutating outputs
    miniAllocator: MiniAllocator,
    output: LinkedBranch // root of the tree that we are building. Everything reachable from here is mini-allocated, disk here should be consistent with mini-allocator
  )
  
  datatype Variables = Variables(
    threads: seq<CompactThread>
  )
  {
    function Likes() : LikesAU {
      // Union of output.likes and subdisk.Keys (or traverse disk from branchSeq roots?)
      NoLikes()  // this is a placeholder
    }
  }

  datatype TransitionLabel =
    | Begin(branchSeq: BranchSeq, offsetMap: OffsetMap, subdisk: BranchDiskView)
    | Internal(allocs: seq<AU>)
    | Commit(branchSeq: BranchSeq, offsetMap: OffsetMap, subdisk: BranchDiskView, output: LinkedBranch)
    | Abort(deallocs: seq<AU>)  // allow us to abandon a compaction (even though in practice this is not necessary, via scheduler magic)

  datatype Step = 
    | BeginStep()
    | AllocStep(idx: nat)
    | BuildStep(idx: nat, addr: Address, newOutput: LinkedBranch)
    | CommitStep(idx: nat)
    | AbortStep(idx: nat)


  predicate Begin(v: Variables, v': Variables, lbl: TransitionLabel) {
    && lbl.Begin?
    && var newThread := CompactThread(
      lbl.branchSeq, 
      lbl.offsetMap, 
      lbl.subdisk, 
      EmptyMiniAllocator(), 
      LinkedBranch(GenericDisk.Address(0, 0), EmptyDisk())  //placeholder
      );
    && v' == v.(threads := v.threads + [newThread])
  }

  predicate Alloc(v: Variables, v': Variables, lbl: TransitionLabel, idx:nat) {
    && lbl.Internal?
    && var thread := v.threads[idx];
    && var thread' := thread.(miniAllocator := thread.miniAllocator.AddAUs(Set(lbl.allocs)));
    && v' == v.(threads := v.threads[ idx := thread'])
  }

  predicate Build(v: Variables, v': Variables, lbl: TransitionLabel, idx:nat, addr: Address, newOutput: LinkedBranch) {
    && lbl.Internal?
    && lbl.allocs == []
    && var thread := v.threads[idx];
    && thread.miniAllocator.CanAllocate(addr)
    && newOutput == thread.output // TODO: This is a placeholder for building the tree
    && var thread' := thread.(
      miniAllocator := thread.miniAllocator.Allocate(addr),
      output := newOutput 
    );
    && v' == v.(threads := v.threads[ idx := thread'])
  }

  predicate Commit(: Variables, v': Variables, lbl: TransitionLabel, idx:nat) {
    && lbl.Commit?
    && idx < |v.thread|
    && var thread := v.threads[idx];
    && lbl.branchSeq == thread.branchSeq
    && lbl.offsetMap == thread.offsetMap
    && lbl.subdisk == thread.subdisk
    && true // TODO: placeholder for thread.output is done
    && lbl.output == thread.output
    // reserved set should be same as output.repr, to mean that I used all the stuff I reserved
    && thread.miniAllocator.GetAllReserved() == thread.output.Representation()
    && v'.threads == remove(v.threads, idx)
  }
}