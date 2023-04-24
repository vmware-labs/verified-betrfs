// Copyright 2018-2021 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, and University of Washington
// SPDX-License-Identifier: BSD-2-Clause

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
  import opened Sets
  import opened KeyType
  import opened ValueMessage 
  import opened FlattenedBranchMod

  import AllocBranch = AllocationBranchMod
  import KeysImpl = Upperbounded_Lexicographic_Byte_Order_Impl
  import Keys = KeysImpl.Ord

  type Element = Keys.Element
  type BranchDiskView = AllocBranch.DiskView

  datatype CompactInput = CompactInput(
    branchSeq: BranchSeq,
    offsetMap: OffsetMap,  // filter describing which keys from branchSeq should be preserved in output
    subdisk: BranchDiskView // diskview containing exactly the part of the tree we are reading
  ) {
    predicate WF()
    {
      && offsetMap.WF()
      && subdisk.WF()
    }
  }

  // Transitions for each thread state machine, from the persective of the caller:
  //  Init(compact start), Internal, Commit, Abort
  datatype CompactThread = CompactThread(
    // Read-only inputs
    input: CompactInput,
    // Mutating outputs
    nextKey: Element,
    miniAllocator: MiniAllocator,
    output: AllocBranch.Variables
    // root of the tree that we are building
    // everything reachable from here is mini-allocated
    // disk here should be consistent with mini-allocator
  ) {
    predicate WF() {
      && input.WF()
      && miniAllocator.WF()
      && output.branch.Acyclic()
    }
  }
  
  datatype Variables = Variables(
    threads: seq<CompactThread>
  )
  {
    predicate WF() {
      forall i | 0 <= i < |threads| :: threads[i].WF()
    }

    predicate DisjointMiniAllocator()
    {
      && (forall idx1: nat, idx2:nat | idx1 < |threads| && idx2 < |threads| && idx1 != idx2 
        :: threads[idx1].miniAllocator.allocs.Keys !! threads[idx2].miniAllocator.allocs.Keys)
    }

    function AUs() : set<AU>
    {
      UnionSeqOfSets(seq(|threads|, i requires 0 <= i < |threads| => threads[i].miniAllocator.allocs.Keys))
    }
  }

  datatype TransitionLabel =
    | BeginLabel(input: CompactInput, aus: set<AU>) // initial AU allocated to compactor's mini allocator
    | InternalLabel(allocs: set<AU>)
    | CommitLabel(input: CompactInput, output: AllocBranch.AllocationBranch)
    | AbortLabel(deallocs: set<AU>)  // allow us to abandon a compaction (even though in practice this is not necessary, via scheduler magic)

  predicate Begin(v: Variables, v': Variables, lbl: TransitionLabel, addr: Address) {
    && v.WF()
    && lbl.BeginLabel?
    && var miniAllocator := EmptyMiniAllocator().AddAUs(lbl.aus);
    && miniAllocator.CanAllocate(addr)

    && var newThread := CompactThread(
        lbl.input,
        Element.Element([]),  // start with minkey
        miniAllocator.Allocate(addr),
        AllocBranch.Variables(EmptyAllocationBranch(addr))
      );
    && v' == v.(threads := v.threads + [newThread])
  }

  predicate Alloc(v: Variables, v': Variables, lbl: TransitionLabel, idx: nat) {
    && v.WF()
    && lbl.InternalLabel?
    && lbl.allocs != {}
    && idx < |v.threads|
    && var thread := v.threads[idx];
    // && lbl.allocs !! thread.miniAllocator.allocs.Keys

    && var thread' := thread.(miniAllocator := thread.miniAllocator.AddAUs(lbl.allocs));
    && v' == v.(threads := v.threads[ idx := thread'])
  }

  function CompactInputQueryFiltered(input: CompactInput, key: Key) : Message
    requires input.offsetMap.WF()
    decreases input.branchSeq.Length()
  {
    if |input.branchSeq.roots| == 0 then Update(NopDelta())
    else (
      var branch := AllocationBranch(input.branchSeq.roots[0], input.subdisk);
      var msg := 
        if branch.Acyclic() && key in input.offsetMap.FilterForBottom() 
        then branch.Query(key) else Update(NopDelta());
      
      var newInput := CompactInput(input.branchSeq.DropFirst(), input.offsetMap.Decrement(1), input.subdisk);
      Merge(CompactInputQueryFiltered(newInput, key), msg)
    )
  }

  predicate ValidBranchToInsert(thread: CompactThread, newNextKey: Element, branchToInsert: FlattenedBranch)
    requires thread.WF()
  {
    && branchToInsert.WF()
    && (|branchToInsert.keys| > 0 ==>
      && Keys.lte(thread.nextKey, Element.Element(branchToInsert.keys[0]))
      && Keys.lt(Element.Element(Last(branchToInsert.keys)), newNextKey))
    && (forall i:nat | i < |branchToInsert.keys| ::
      CompactInputQueryFiltered(thread.input, branchToInsert.keys[i]) == branchToInsert.msgs[i])
  }

  predicate Build(v: Variables, v': Variables, lbl: TransitionLabel, idx: nat, ptr: Pointer, 
    newOutput: AllocBranch.Variables, newNextKey: Element, branchToInsert: FlattenedBranch) {
    && v.WF()
    && lbl.InternalLabel?
    && lbl.allocs == {}
    && idx < |v.threads|
    && var thread := v.threads[idx];
    && Keys.lte(thread.nextKey, newNextKey)
    && (ptr.Some? ==> thread.miniAllocator.CanAllocate(ptr.value))
    && ValidBranchToInsert(thread, newNextKey, branchToInsert)

    // nondeterministic transition on the tree
    && AllocBranch.Next(thread.output, newOutput, AllocBranch.BuildLabel(ptr, branchToInsert))
    && var thread' := thread.(
      miniAllocator := if ptr.Some? 
        then thread.miniAllocator.Allocate(ptr.value) 
        else thread.miniAllocator,
      output := newOutput
    );
    && v' == v.(threads := v.threads[idx := thread'])
  }

  predicate Commit(v: Variables, v': Variables, lbl: TransitionLabel, idx:nat) {
    && v.WF()
    && lbl.CommitLabel?
    && idx < |v.threads|
    && var thread := v.threads[idx];
    && lbl.input == thread.input
    && thread.nextKey == Element.Max_Element 
    && thread.output.branch.Sealed() // everything in thread.ouput are reserved in mini allocator
    && thread.output.branch.GetSummary() == thread.miniAllocator.allocs.Keys // no AUs can magically disappear
    // && thread.output.branch.TightDiskView()

    && lbl.output == thread.output.branch
    && v'.threads == remove(v.threads, idx)
  }

  predicate Abort(v: Variables, v': Variables, lbl: TransitionLabel, idx:nat) {
    && v.WF()
    && lbl.AbortLabel?
    && idx < |v.threads|
    && var thread := v.threads[idx];
    && lbl.deallocs == thread.miniAllocator.allocs.Keys
    && v'.threads == remove(v.threads, idx)
  }

  predicate Init(v: Variables)
  {
    && v.threads == []
  }

 datatype Step = 
    | BeginStep(addr: Address)
    | AllocStep(idx: nat)
    | BuildStep(idx: nat, ptr: Pointer, newOutput: AllocBranch.Variables, newNextKey: Element, branchToInsert: FlattenedBranch)
    | CommitStep(idx: nat)
    | AbortStep(idx: nat)

  predicate NextStep(v: Variables, v': Variables, lbl: TransitionLabel, step: Step)
  {
    match step {
      case BeginStep(addr) => Begin(v, v', lbl, addr)
      case AllocStep(idx) => Alloc(v, v', lbl, idx)
      case BuildStep(idx, ptr, newOutput, newNextKey, branchToInsert) => Build(v, v', lbl, idx, ptr, newOutput, newNextKey, branchToInsert)
      case CommitStep(idx) => Commit(v, v', lbl, idx)
      case AbortStep(idx) => Abort(v, v', lbl, idx)
    }
  }

  predicate Next(v: Variables, v': Variables, lbl: TransitionLabel) {
    exists step: Step :: NextStep(v, v', lbl, step)
  }

  // lemmas

  lemma CompactBeginExtendsAU(v: Variables, v': Variables, lbl: TransitionLabel)
    requires Next(v, v', lbl)
    requires lbl.BeginLabel?
    ensures v'.AUs() == v.AUs() + lbl.aus
  {
    var threadsAUSeq := seq(|v.threads|, i requires 0 <= i < |v.threads| => v.threads[i].miniAllocator.allocs.Keys);
    var threadsAUSeq' := seq(|v'.threads|, i requires 0 <= i < |v'.threads| => v'.threads[i].miniAllocator.allocs.Keys);

    forall au | au in v.AUs() + lbl.aus
      ensures au in v'.AUs()
    {
      if au in v.AUs() {
        UnionSeqOfSetsSoundness(threadsAUSeq);
        var idx :| 0 <= idx < |threadsAUSeq| && au in threadsAUSeq[idx];
        assert threadsAUSeq[idx] == threadsAUSeq'[idx];
      } else if au in lbl.aus {
        assert au in Last(threadsAUSeq');
      }
    }

    forall au | au in v'.AUs()
      ensures au in v.AUs() + lbl.aus
    {
      UnionSeqOfSetsSoundness(threadsAUSeq');
      var idx :| 0 <= idx < |threadsAUSeq'| && au in threadsAUSeq'[idx];
      if idx < |threadsAUSeq| {
        assert threadsAUSeq[idx] == threadsAUSeq'[idx];
        assert au in v.AUs();
      } else {
        assert au in Last(threadsAUSeq');
        assert au in lbl.aus;
      }
    }
  }

  lemma CompactInternalExtendsAU(v: Variables, v': Variables, lbl: TransitionLabel)
    requires Next(v, v', lbl)
    requires lbl.InternalLabel?
    ensures v'.AUs() == v.AUs() + lbl.allocs
  {
    var threadsAUSeq := seq(|v.threads|, i requires 0 <= i < |v.threads| => v.threads[i].miniAllocator.allocs.Keys);
    var threadsAUSeq' := seq(|v'.threads|, i requires 0 <= i < |v'.threads| => v'.threads[i].miniAllocator.allocs.Keys);

    var step :| NextStep(v, v', lbl, step);
    if step.BuildStep? {
      assert lbl.allocs == {};
      assert v'.threads[step.idx].miniAllocator.allocs.Keys == v.threads[step.idx].miniAllocator.allocs.Keys;
      assert threadsAUSeq == threadsAUSeq';
    } else {
      assert step.AllocStep?;
      assert v'.threads[step.idx].miniAllocator.allocs.Keys == v.threads[step.idx].miniAllocator.allocs.Keys + lbl.allocs;

      forall au | au in v.AUs() + lbl.allocs
      ensures au in v'.AUs()
      {
        if au in v.AUs() {
          UnionSeqOfSetsSoundness(threadsAUSeq);
          var idx :| 0 <= idx < |threadsAUSeq| && au in threadsAUSeq[idx];
          assert threadsAUSeq[idx] <= threadsAUSeq'[idx];
        } else if au in lbl.allocs {
          assert au in threadsAUSeq'[step.idx];
        }
      }

      forall au | au in v'.AUs()
      ensures au in v.AUs() + lbl.allocs
      {
        UnionSeqOfSetsSoundness(threadsAUSeq');
        var idx :| 0 <= idx < |threadsAUSeq'| && au in threadsAUSeq'[idx];
        if idx == step.idx {
          assert au in threadsAUSeq[idx] + lbl.allocs;
        } else {
          assert threadsAUSeq[idx] == threadsAUSeq'[idx];
        }
      }
    }
  }

  lemma CompactCommitAUSubset(v: Variables, v': Variables, lbl: TransitionLabel)
    requires Next(v, v', lbl)
    requires lbl.CommitLabel?
    ensures v'.AUs() + lbl.output.GetSummary() == v.AUs()
  {
    // TODO
    var threadsAUSeq := seq(|v.threads|, i requires 0 <= i < |v.threads| => v.threads[i].miniAllocator.allocs.Keys);
    var threadsAUSeq' := seq(|v'.threads|, i requires 0 <= i < |v'.threads| => v'.threads[i].miniAllocator.allocs.Keys);
    
    var step :| NextStep(v, v', lbl, step);
    forall au | au in v'.AUs()
    ensures au in v.AUs()
    {
      UnionSeqOfSetsSoundness(threadsAUSeq');
      var idx :| 0 <= idx < |threadsAUSeq'| && au in threadsAUSeq'[idx];
      if idx < step.idx {
        assert threadsAUSeq[idx] == threadsAUSeq'[idx];
      } else {
        assert threadsAUSeq[idx+1] == threadsAUSeq'[idx];
      }
    }
  }
}