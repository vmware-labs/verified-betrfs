// Copyright 2018-2021 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, and University of Washington
// SPDX-License-Identifier: BSD-2-Clause

// include "../LikesAU.i.dfy"
// include "../Journal/MiniAllocator.i.dfy"   // tony: borrowing from Journal for now
include "../Betree/AllocationBranch.i.dfy"
include "../Betree/BranchSeq.i.dfy"
include "../Betree/OffsetMap.i.dfy"
include "MiniAllocator.i.dfy"
include "LikesAU.i.dfy"

module CompactorMod
{
  import opened AllocationBranchMod
  import opened BranchSeqMod
  import opened OffsetMapMod
  import opened MiniAllocatorMod
  import opened LikesAUMod
  import opened GenericDisk
  import opened Sequences

  type BranchDiskView = AllocationBranchMod.DiskView

  // label: addresses 

  // 


// Transitions for each thread state machine, from the persective of the caller:
  //  Init(compact start), Internal, Commit, Abort
  datatype CompactThread = CompactThread(
    // Read-only inputs
    branchSeq: BranchSeq,
    offsetMap: OffsetMap,  // filter describing which keys from branchSeq should be preserved in output
    subdisk: BranchDiskView, // diskview containing exactly the part of the tree we are reading
    // Mutating outputs
    miniAllocator: MiniAllocator,


    // all keys to the left of this (exclusive) have been copied to output
    // 
    nextKey: Element

    output: AllocationBranch // root of the tree that we are building. Everything reachable from here is mini-allocated, disk here should be consistent with mini-allocator
  ) {
    predicate WF() {
      && miniAllocator.WF()
      && output.Acyclic()
    }
  }
  
  datatype Variables = Variables(
    threads: seq<CompactThread>
  )
  {
    predicate WF() {
      forall i | 0 <= i < |threads| :: threads[i].WF()
    }

    function Likes() : LikesAU {
      // Union of output.likes and subdisk.Keys (or traverse disk from branchSeq roots?)
      NoLikes()  // this is a placeholder
    }
  }

  datatype TransitionLabel =
    | Begin(branchSeq: BranchSeq, offsetMap: OffsetMap, subdisk: BranchDiskView)
    | Internal(allocs: seq<AU>)
    | Commit(branchSeq: BranchSeq, offsetMap: OffsetMap, subdisk: BranchDiskView, output: AllocationBranch)
    | Abort(deallocs: seq<AU>)  // allow us to abandon a compaction (even though in practice this is not necessary, via scheduler magic)

  datatype Step = 
    | BeginStep()
    | AllocStep(idx: nat)
    | BuildStep(idx: nat, addr: Address, newOutput: AllocationBranch)
    | CommitStep(idx: nat)
    | AbortStep(idx: nat)


  predicate Begin(v: Variables, v': Variables, lbl: TransitionLabel) {
    && v.WF()
    && lbl.Begin?
    && var newThread := CompactThread(
      lbl.branchSeq, 
      lbl.offsetMap, 
      lbl.subdisk, 
      EmptyMiniAllocator(), 
      AllocationBranch(GenericDisk.Address(0, 0), EmptyDisk())  //TODO placeholder
      );
    && v' == v.(threads := v.threads + [newThread])
  }

  predicate Alloc(v: Variables, v': Variables, lbl: TransitionLabel, idx:nat) {
    && v.WF()
    && lbl.Internal?
    && idx < |v.threads|
    && var thread := v.threads[idx];
    && Set(lbl.allocs) !! thread.miniAllocator.allocs.Keys
    && var thread' := thread.(miniAllocator := thread.miniAllocator.AddAUs(Set(lbl.allocs)));
    && v' == v.(threads := v.threads[ idx := thread'])
  }

  // move to allocation branch
  datatype BranchLabel = 
    | BuildLabel(addrs: seq<Address>, inputStream: FlattenedBranch)

  predicate Build(v: Variables, v': Variables, lbl: TransitionLabel, idx:nat, 
    addr: Address, newOutput: AllocationBranch, newNextKey: Element) {
    && v.WF()
    && lbl.Internal?
    && idx < |v.threads|
    && lbl.allocs == []
    && var thread := v.threads[idx];
    && thread.miniAllocator.CanAllocate(addr)
    // nondeterministic transition on the tree
    // TODO: also take in a tree step so that we can update the tree
    // new label for updated tree data

    // lbl to branch
    // lbl: addresses, keys and values to insert
    // range comparison should be elements
    && Keys.lte(v.nextKey, newNextKey)
    && AllocationBranch.Next(v.output, newOutput, 
      BranchLabel.BuildLabel([addr], branchSeq.toFlattenBranch(v.nextKey, newNextKey)))

    && newOutput == thread.output // TODO: This is a placeholder for building the tree
    // incremental 
    // several input streams
    // key consumed based on input streams

    && var thread' := thread.(
      miniAllocator := thread.miniAllocator.Allocate(addr),
      output := newOutput 
    );
    && v' == v.(threads := v.threads[ idx := thread'])
  }

  predicate Commit(v: Variables, v': Variables, lbl: TransitionLabel, idx:nat) {
    && v.WF()
    && lbl.Commit?
    && idx < |v.threads|
    && var thread := v.threads[idx];
    && lbl.branchSeq == thread.branchSeq
    && lbl.offsetMap == thread.offsetMap
    && lbl.subdisk == thread.subdisk

    && v.nextKey == Element.max // 
    // representation is the same
    // && lbl.branchSeq.QueryFilteredEquiv(lbl.subdisk, lbl.offsetMap, lbl.output)
    // ^ needs an 
    
    // && true // TODO: placeholder for thread.output is done
    // && lbl.output == thread.output
    // reserved set should be same as output.repr, to mean that I used all the stuff I reserved
    && thread.miniAllocator.GetAllReserved() == thread.output.Representation()
    && v'.threads == remove(v.threads, idx)
  }


}