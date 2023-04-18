// Copyright 2018-2021 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, and University of Washington
// SPDX-License-Identifier: BSD-2-Clause

include "LinkedBetree.i.dfy"
include "BranchedBetree.i.dfy"
include "LinkedBranchRefinement.i.dfy"

module BranchedBetreeRefinement {
  import opened BoundedPivotsLib
  import LinkedBetree = LinkedBetreeMod
  import opened BranchedBetreeMod
  import LinkedBranchMod
  import LinkedBranchRefinement
  import PivotBranchMod
  import opened BranchSeqMod
  import opened LinkedBufferSeqMod
  import opened StampedMod
  import opened DomainMod
  import opened Upperbounded_Lexicographic_Byte_Order_Impl.Ord
  import opened BufferMod
  import opened KeyType
  import opened Sequences
  import opened GenericDisk
  import opened Maps
  import opened Sets

  import opened ValueMessage // test

  function ILbl(lbl: BranchedBetreeMod.TransitionLabel) : LinkedBetree.TransitionLabel
  {
    match lbl
      case QueryLabel(endLsn, key, value) => LinkedBetree.QueryLabel(endLsn, key, value)
      case PutLabel(puts) => LinkedBetree.PutLabel(puts)
      case QueryEndLsnLabel(endLsn) => LinkedBetree.QueryEndLsnLabel(endLsn)
      case FreezeAsLabel(stampedBetree) => LinkedBetree.FreezeAsLabel(
        if stampedBetree.value.WF()
        then IStampedBetree(stampedBetree)
        else IStampedBetree(EmptyImage())  // "silly" case, since we never interpret non-(WF+Valid) things
      )
      case InternalLabel() => LinkedBetree.InternalLabel()
  }

  // function ActiveBufferKeysForChild(node: BetreeNode, childIdx: nat, bufferIdx: nat) : iset<Key>
  //   requires node.WF()
  //   requires childIdx < |node.children|
  //   requires bufferIdx < node.branches.Length()
  // {
  //   if node.activeBufferRanges[childIdx] <= bufferIdx 
  //   then node.DomainRoutedToChild(childIdx).KeySet()
  //   else iset{}
  // }

  // function ActiveBufferKeys(node: BetreeNode, bufferIdx: nat) : iset<Key>
  //   requires node.WF()
  //   requires bufferIdx < node.branches.Length()
  // {
  //   iset k, i | 0 <= i < |node.children| && k in ActiveBufferKeysForChild(node, i, bufferIdx) :: k
  // }

  // function IBuffer(node: BetreeNode, branch: LinkedBranch, bufferIdx: nat) : Buffer
  //   requires node.WF()
  //   requires bufferIdx < node.branches.Length()
  //   requires branch.Acyclic()
  //   requires branch.AllKeysInRange()
  // {
  //   var buffer := branch.I().I();
  //   buffer.ApplyFilter(ActiveBufferKeys(node, bufferIdx))
  // }

  function IBranchSeq(node: BetreeNode) : BufferSeq
  {
    BufferSeq(node.branches.roots)
  }

  // function IBufferStack(node: BetreeNode, branches: Branches) : BufferStack
  //   requires node.WF()
  //   requires branches.WF()
  //   requires forall buffer | buffer in node.branches :: branches.ValidBranch(buffer)
  // {
  //   BufferStack( seq (node.branches.Length(), 
  //        i requires 0 <= i < node.branches.Length() => 
  //        IBuffer(node, branches.GetBranch(node.branches[i]), i)))
  // }

  // function IBufferStackPartial(node: BetreeNode, branches: Branches, start: nat, end: nat) : BufferStack
  //   requires node.WF()
  //   requires branches.WF()
  //   requires start <= end <= node.branches.Length()
  //   requires forall i | start <= i < end :: branches.ValidBranch(node.branches[i])
  // {
  //   BufferStack( seq (end-start, 
  //        i requires 0 <= i < end-start => 
  //        IBuffer(node, branches.GetBranch(node.branches[i+start]), i+start)))
  // }

  function IBranchedBetreeNode(node: BetreeNode) : (out: LinkedBetree.BetreeNode)
    requires node.WF()
    ensures out.WF()
  {
    LinkedBetree.BetreeNode(IBranchSeq(node), node.pivotTable, node.children, node.flushedOffsets)
  }

  function IBranch(root: Address, dv: BranchDiskView) : Buffer
    requires dv.ValidAddress(root)
  {
    var branch := LinkedBranchMod.LinkedBranch(root, dv);
    if branch.Acyclic() && branch.AllKeysInRange()
    then LinkedBranchRefinement.I(branch).I()
    else Buffer(map[])
  }

  function IBranchDiskView(dv: BranchDiskView) : (out: LinkedBufferSeqMod.BufferDiskView)
  {
    LinkedBufferSeqMod.BufferDiskView(map addr | addr in dv.entries :: IBranch(addr, dv))
  }

  function IDiskView(branched: BranchedBetree) : (out: LinkedBetree.DiskView)
    requires branched.WF()
    ensures out.WF()
  {
    var entries := branched.diskView.entries;
    var dv := LinkedBetree.DiskView( map addr | addr in entries :: IBranchedBetreeNode(entries[addr]));

    assert dv.HealthyChildPointers(); // trigger
    dv
  }

  function IBranchedBetree(branched: BranchedBetree) : (out: LinkedBetree.LinkedBetree)
    requires branched.WF()
    ensures out.WF()
  {
    LinkedBetree.LinkedBetree(branched.root, IDiskView(branched), IBranchDiskView(branched.branchDiskView))
  }

  function IStampedBetree(stampedBetree: StampedBetree) : (out: LinkedBetree.StampedBetree)
    requires stampedBetree.value.WF()
    ensures out.value.WF()
  {
    Stamped(IBranchedBetree(stampedBetree.value), stampedBetree.seqEnd)
  }

  // lemma IBranchedBetreeAcyclic(branched: BranchedBetree) 
  //   requires branched.Acyclic()
  //   requires branched.Valid()
  //   ensures IBranchedBetree(branched).Acyclic()
  // {
  //   assert IBranchedBetree(branched).ValidRanking(branched.TheRanking());
  // }

  function I(v: Variables) : (out: LinkedBetree.Variables)
    requires v.WF()
    // requires v.branched.WF()
  {
    LinkedBetree.Variables(v.memtable, IBranchedBetree(v.branched))
  }

  // // Interpretation functions for Path
  // function IPath(path: Path) : LinkedBetree.Path
  //   requires path.Valid()
  // {
  //   LinkedBetree.Path(IBranchedBetree(path.branched), path.key, path.depth) 
  // }

  // lemma TargetCommutesWithI(path: Path)
  //   requires path.Valid()
  //   ensures IPath(path).Valid()
  //   ensures IPath(path).Target() == IBranchedBetree(path.Target())
  //   decreases path.depth
  // {
  //   IBranchedBetreeAcyclic(path.branched);
  //   if 0 < path.depth {
  //     TargetCommutesWithI(path.Subpath());
  //   }
  // }

  // // Interpretation functions for Query receipts
  // function IReceiptLine(line: QueryReceiptLine) : (out: LinkedBetree.QueryReceiptLine)
  //   requires line.branched.WF()
  //   requires line.branched.Valid()
  // {
  //   LinkedBetree.QueryReceiptLine(IBranchedBetree(line.branched), line.result)
  // }

  //  function IReceipt(receipt: QueryReceipt) : (out: LinkedBetree.QueryReceipt)
  //   requires receipt.Valid()
  // {
  //   LinkedBetree.QueryReceipt(
  //     receipt.key, 
  //     IBranchedBetree(receipt.branched), 
  //     seq(|receipt.lines|, i requires 0<=i<|receipt.lines| => IReceiptLine(receipt.lines[i])))
  // }

  // lemma ActiveBuffersForKeyConsistent(node: BetreeNode, key: Key, start: nat)
  //   requires node.WF()
  //   requires node.KeyInDomain(key)
  //   requires start == node.ActiveBuffersForKey(key)
  //   ensures forall i:nat | i < start :: key !in ActiveBufferKeys(node, i)
  //   ensures forall i:nat | start <= i < node.branches.Length() :: key in ActiveBufferKeys(node, i)
  // {
  //   forall i:nat | start <= i < node.branches.Length()
  //     ensures key in ActiveBufferKeys(node, i)
  //   {
  //     var childIdx := Route(node.pivotTable, key);
  //     assert key in ActiveBufferKeysForChild(node, childIdx, i); // trigger
  //   }
  // }

  // lemma CompactBufferEquivStart(node: BetreeNode, branches: Branches, key: Key, start: nat, end: nat, count: nat)
  //   requires IBufferStackPartial.requires(node, branches, start, end)
  //   requires node.KeyInDomain(key)
  //   requires node.ActiveBuffersForKey(key) <= start
  //   requires start <= end <= node.branches.Length()
  //   requires start <= count <= end
  //   ensures IBufferStackPartial(node, branches, start, end).QueryUpTo(key, count-start) == branches.Query(key, node.branches[start..count])
  // {
  //   if start < count {
  //     var bs := IBufferStackPartial(node, branches, start, end);
  //     ActiveBuffersForKeyConsistent(node, key, node.ActiveBuffersForKey(key));
  //     assert Last(node.branches[start..count]) == node.branches[count-1];

  //     CompactBufferEquivStart(node, branches, key, start, end, count-1);
  //     assert DropLast(node.branches[start..count]) == node.branches[start..count-1];
  //     assert bs.QueryUpTo(key, count-start-1) == branches.Query(key, node.branches[start..count-1]);
  //     assert bs.QueryUpTo(key, count-start) == branches.Query(key, node.branches[start..count]);
  //   }
  // }

  // lemma CompactBufferEquivActive(node: BetreeNode, branches: Branches, key: Key, start: nat, end: nat, count: nat)
  //   requires IBufferStackPartial.requires(node, branches, start, end)
  //   requires node.KeyInDomain(key)
  //   requires node.ActiveBuffersForKey(key) > start
  //   requires start <= end <= node.branches.Length()
  //   requires start <= count <= end
  //   ensures var active := node.ActiveBuffersForKey(key);
  //     && var bs := IBufferStackPartial(node, branches, start, end);
  //     && (count < active ==> bs.QueryUpTo(key, count-start) == Update(NopDelta()))
  //     && (count >= active ==> bs.QueryUpTo(key, count-start) == branches.Query(key, node.branches[active..count]))
  // {
  //   if start < count {
  //     var active := node.ActiveBuffersForKey(key);
  //     ActiveBuffersForKeyConsistent(node, key, active);
  //     if active < count {
  //       var bs := IBufferStackPartial(node, branches, start, end);
  //       assert Last(node.branches[active..count]) == node.branches[count-1];

  //       CompactBufferEquivActive(node, branches, key, start, end, count-1);
  //       assert DropLast(node.branches[active..count]) == node.branches[active..count-1];
  //       assert bs.QueryUpTo(key, count-start-1) == branches.Query(key, node.branches[active..count-1]);
  //       assert bs.QueryUpTo(key, count-start) == branches.Query(key, node.branches[active..count]);
  //     } else {
  //       CompactBufferEquivActive(node, branches, key, start, end, count-1);
  //     }
  //   }
  // }

  // lemma QueryCommutesWithIBufferStack(node: BetreeNode, branches: Branches, key: Key, start: nat, count: nat)
  //   requires IBufferStack.requires(node, branches)
  //   requires node.KeyInDomain(key)
  //   requires count <= node.branches.Length()
  //   requires start == node.ActiveBuffersForKey(key)
  //   ensures count <= start ==> (IBufferStack(node, branches).QueryUpTo(key, count) == Update(NopDelta()))
  //   ensures start < count ==> (IBufferStack(node, branches).QueryUpTo(key, count) == branches.Query(key, node.branches[start..count]))
  // {
  //   ActiveBuffersForKeyConsistent(node, key, start);
  //   if start < count {
  //     var branch := branches.GetBranch(node.branches[count-1]);
  //     var msg := if branch.Query(key).Some? then branch.Query(key).value else Update(NopDelta());
  //     assert IBufferStack(node, branches).branches[count-1].Query(key) == msg;
  //     assert node.branches[start..count-1] == DropLast(node.branches[start..count]);
  //     QueryCommutesWithIBufferStack(node, branches, key, start, count-1);
  //   } else if 0 < count {
  //     QueryCommutesWithIBufferStack(node, branches, key, start, count-1);
  //   }
  // }

  // lemma QueryUpToEquivalent(a: BufferStack, b: BufferStack, key: Key, count: nat)
  //   requires count <= |a.branches|
  //   requires count <= |b.branches|
  //   requires forall i:nat | i < count :: a.branches[i].Query(key) == b.branches[i].Query(key)
  //   ensures a.QueryUpTo(key, count) == b.QueryUpTo(key, count)
  // {
  //   if count > 0 {
  //     QueryUpToEquivalent(a, b, key, count-1);
  //   }
  // }

  // lemma BufferStackQueryAdditive(left: BufferStack, right: BufferStack, key: Key, count: nat)
  //   requires count <= |left.branches| + |right.branches|
  //   ensures 
  //     && var out := BufferStack(left.branches + right.branches);
  //     && (count <= |left.branches| ==> out.QueryUpTo(key, count) == left.QueryUpTo(key, count))
  //     && (|left.branches| < count ==> out.QueryUpTo(key, count) == Merge(left.Query(key), right.QueryUpTo(key, count-|left.branches|)))
  // {
  //   var out := BufferStack(left.branches + right.branches);
  //   if count <= |left.branches| {
  //     QueryUpToEquivalent(out, left, key, count);
  //   } else {
  //     BufferStackQueryAdditive(left, right, key, count-1);
  //   }
  // }

  // lemma BufferStackQueryNotPresent(bs: BufferStack, k: Key, count: nat)
  //   requires count <= |bs.branches|
  //   requires forall b | b in bs.branches :: k !in b.mapp
  //   ensures bs.QueryUpTo(k, count) == Update(NopDelta())
  // {
  //   if count > 0 {
  //     BufferStackQueryNotPresent(bs, k, count-1);
  //   }
  // }

  // lemma IReceiptValid(receipt: QueryReceipt) 
  //   requires receipt.Valid()
  //   ensures IReceipt(receipt).Valid()
  // {
  //   var ireceipt := IReceipt(receipt);
  //   var key := receipt.key;

  //   IBranchedBetreeAcyclic(receipt.branched);

  //   forall i:nat | i < |ireceipt.lines|
  //     ensures ireceipt.lines[i].linked.Acyclic()
  //   {
  //     IBranchedBetreeAcyclic(receipt.lines[i].branched);
  //   }

  //   forall i:nat | i < |ireceipt.lines|-1 
  //     ensures ireceipt.Node(i).KeyInDomain(key)
  //     ensures ireceipt.ChildLinkedAt(i)
  //   {
  //     assert receipt.Node(i).KeyInDomain(key);  // trigger
  //     assert receipt.ChildLinkedAt(i);  // trigger
  //   }
  
  //   forall i:nat | i < |ireceipt.lines| - 1 
  //   ensures ireceipt.ResultLinkedAt(i)
  //   {
  //     assert receipt.ResultLinkedAt(i);  // trigger

  //     var branched := receipt.lines[i].branched;
  //     var key := ireceipt.key;
  //     var node := branched.Root();
  //     var start := node.ActiveBuffersForKey(key);

  //     assert node.branches[start..node.branches.Length()] == node.branches[start..]; //trigger
  //     QueryCommutesWithIBufferStack(node, branched.branches, key, start, node.branches.Length());
  //   }
  // }

  // // Interpretation functions for Steps
  // function IStepDefn(step: Step) : (out: LinkedBetree.Step)
  //   requires step.WF()
  // {
  //   match step {
  //     case QueryStep(receipt) => LinkedBetree.QueryStep(IReceipt(receipt))
  //     case PutStep() => LinkedBetree.PutStep()
  //     case QueryEndLsnStep() => LinkedBetree.QueryEndLsnStep()
  //     case FreezeAsStep() => LinkedBetree.FreezeAsStep()
  //     case InternalGrowStep(newRootAddr) => LinkedBetree.InternalGrowStep(newRootAddr)
  //     case InternalSplitStep(path, request, newAddrs, pathAddrs) => 
  //           LinkedBetree.InternalSplitStep(IPath(path), request, newAddrs, pathAddrs)
  //     case InternalFlushMemtableStep(newRootAddr, _) => LinkedBetree.InternalFlushMemtableStep(newRootAddr)
  //     case InternalFlushStep(path, childIdx, targetAddr, targetChildAddr, pathAddrs, _) =>
  //           LinkedBetree.InternalFlushStep(IPath(path), childIdx, targetAddr, targetChildAddr, pathAddrs)
  //     case InternalCompactStep(path, compactStart, compactEnd, compactedBranch, targetAddr, pathAddrs) => (
  //         var linked := IBranchedBetree(path.Target());
  //         var branches := linked.Root().branches.branches;
  //         var compactedBuffers := branches[..compactStart] + [compactedBranch.I().I()] + branches[compactEnd..];
  //         LinkedBetree.InternalCompactStep(IPath(path), BufferStack(compactedBuffers), targetAddr, pathAddrs))
  //     case InternalPruneBranchesStep(_) => LinkedBetree.InternalNoOpStep()
  //     case InternalNoOpStep() => LinkedBetree.InternalNoOpStep()
  //   }
  // }

  // lemma CompactedBranchEquivConsistentWithI(node: BetreeNode, branches: Branches, start: nat, end: nat, compact: LinkedBranch, k: Key)
  //   requires node.CompactedBranchEquivalence.requires(branches, start, end, compact)
  //   requires node.CompactedBranchEquivalence(branches, start, end, compact)
  //   ensures IBufferStackPartial(node, branches, start, end).Query(k) 
  //           == if compact.Query(k).Some? then compact.Query(k).value else Update(NopDelta())
  // {
  //   var result := if compact.Query(k).Some? then compact.Query(k).value else Update(NopDelta());
  //   var bufferstack := IBufferStackPartial(node, branches, start, end);

  //   if node.KeyInDomain(k) && node.ActiveBuffersForKey(k) < end {
  //     if node.ActiveBuffersForKey(k) <= start {
  //       CompactBufferEquivStart(node, branches, k, start, end, end);
  //     } else {
  //       CompactBufferEquivActive(node, branches, k, start, end, end);
  //     }
  //     assert bufferstack.Query(k) == result;
  //   } else {
  //     forall i | 0 <= i < |bufferstack.branches|
  //       ensures k !in bufferstack.branches[i].mapp 
  //     {
  //       if k in bufferstack.branches[i].mapp {
  //         var childIdx :| 0 <= childIdx < |node.children| && k in ActiveBufferKeysForChild(node, childIdx, i+start);
  //         reveal_IsStrictlySorted();
  //         lteTransitiveForall();
  //         assert false;
  //       }
  //     }
  //     BufferStackQueryNotPresent(bufferstack, k, end-start);
  //   }
  // }

  // lemma InternalCompactStepWF(step: Step) 
  //   requires step.WF()
  //   requires step.InternalCompactStep?
  //   ensures IStepDefn(step).WF()
  // {
  //   var istep := IStepDefn(step);
  //   var path := step.path;
  //   TargetCommutesWithI(path);
  //   assert istep.path.Valid();

  //   var linked := istep.path.Target();
  //   var branched := path.Target();
  //   var start := step.compactStart;
  //   var end := step.compactEnd;

  //   var linkedBuffers := linked.Root().branches.branches;
  //   var compactedBuffers := istep.compactedBuffers.branches;
  //   var delta := end - start - 1;

  //   var left := BufferStack(linkedBuffers[..start]);
  //   var left' := BufferStack(compactedBuffers[..start]);
  //   var middle := BufferStack(linkedBuffers[start..end]);
  //   var middle' := BufferStack([compactedBuffers[start]]);
  //   var right := BufferStack(linkedBuffers[end..]);
  //   var right' := BufferStack(compactedBuffers[start+1..]);

  //   assert left.branches + middle.branches == linkedBuffers[..end]; // trigger
  //   assert left'.branches + middle'.branches == compactedBuffers[..start+1]; // trigger
  //   assert linkedBuffers[..end] + right.branches == linkedBuffers; // trigger
  //   assert compactedBuffers[..start+1] + right'.branches == compactedBuffers; // trigger
  //   assert linkedBuffers[..|linkedBuffers|] == linkedBuffers; // trigger
  //   assert compactedBuffers[..|compactedBuffers|] == compactedBuffers; // trigger

  //   forall k | AnyKey(k)
  //     ensures linked.Root().branches.Query(k) == istep.compactedBuffers.Query(k) 
  //   {
  //     QueryUpToEquivalent(left, left', k, start);
  //     assert left.Query(k) == left'.Query(k);

  //     QueryUpToEquivalent(right, right', k, |right.branches|);
  //     assert right.Query(k) == right'.Query(k);

  //     var result := 
  //       if step.compactedBranch.Query(k).Some? 
  //       then step.compactedBranch.Query(k).value
  //       else Update(NopDelta());

  //     assert middle'.QueryUpTo(k, 0) == Update(NopDelta()); // trigger
  //     assert middle'.Query(k) == result;
  //     CompactedBranchEquivConsistentWithI(branched.Root(), branched.branches, start, end, step.compactedBranch, k);
  //     assert middle == IBufferStackPartial(branched.Root(), branched.branches, start, end); // trigger
  //     assert middle.Query(k) == result;

  //     BufferStackQueryAdditive(left, middle, k, end);
  //     BufferStackQueryAdditive(BufferStack(linkedBuffers[..end]), right, k, |linkedBuffers|);

  //     BufferStackQueryAdditive(left', middle', k, start+1);
  //     BufferStackQueryAdditive(BufferStack(compactedBuffers[..start+1]), right', k, |compactedBuffers|);
  //   }
  // }

  // lemma IStepWF(step: Step)
  //   requires IStepDefn.requires(step)
  //   ensures IStepDefn(step).WF()
  // {
  //   var istep := IStepDefn(step);
  //   match step {
  //     case QueryStep(receipt) => { IReceiptValid(receipt); }
  //     case InternalSplitStep(path, request, newAddrs, pathAddrs) => { TargetCommutesWithI(path); }
  //     case InternalFlushStep(path, childIdx, _, _, _, _) => { TargetCommutesWithI(path); }
  //     case InternalCompactStep(path, compactStart, compactEnd, compactedBranch, _, _) => { InternalCompactStepWF(step); }
  //     case _ =>    {  assert istep.WF(); }
  //   }
  // }

  // function IStep(step: Step) : (out: LinkedBetree.Step)
  //   requires step.WF()
  //   ensures out.WF()
  // {
  //   IStepWF(step);
  //   IStepDefn(step)
  // }

  // // Branch Functions and Lemmas

  // function BranchTightRanking(branch: LinkedBranch) : (out: Ranking)
  //   requires branch.Acyclic()
  //   ensures branch.ValidRanking(out)
  //   ensures out.Keys <= branch.ReachableAddrs()
  // {
  //   var ranking := branch.TheRanking();
  //   var tightRanking := MapRestrict(ranking, branch.ReachableAddrs());

  //   assert branch.ValidRanking(tightRanking) by
  //   {
  //     forall addr | addr in tightRanking && addr in branch.diskView.entries 
  //       ensures branch.diskView.NodeChildrenRespectsRank(tightRanking, addr)
  //     {
  //       BranchReachableAddrClosed(branch, ranking, addr);
  //       assert branch.diskView.NodeChildrenRespectsRank(tightRanking, addr);
  //     }
  //   }

  //   tightRanking
  // }

  // lemma BranchChildrenAreReachable(branch: LinkedBranch, ranking: Ranking)
  //   requires branch.WF()
  //   requires branch.Root().Index?
  //   requires branch.ValidRanking(ranking)
  //   ensures forall i | 0 <= i < |branch.Root().children| :: 
  //     branch.Root().children[i] in branch.ReachableAddrsUsingRanking(ranking)
  // {
  //   var numChildren := |branch.Root().children|;
  //   var subTreeAddrs := seq(numChildren, i requires 0 <= i < numChildren => 
  //     branch.ChildAtIdx(i).ReachableAddrsUsingRanking(ranking));

  //   forall i | 0 <= i < numChildren  
  //     ensures branch.Root().children[i] in branch.ReachableAddrsUsingRanking(ranking)
  //   {
  //     assert branch.Root().children[i] in subTreeAddrs[i];
  //   }
  // }

  // lemma BranchReachableAddrClosed(branch: LinkedBranch, ranking: Ranking, addr: Address)
  //   requires branch.WF()
  //   requires branch.ValidRanking(ranking)
  //   requires addr in branch.ReachableAddrsUsingRanking(ranking)
  //   ensures 
  //     var node := branch.diskView.entries[addr];
  //     && (node.Index? ==> (forall i | 0 <= i < |node.children| :: 
  //       node.children[i] in branch.ReachableAddrsUsingRanking(ranking)))
  //   decreases branch.GetRank(ranking)
  // {
  //   var node := branch.diskView.entries[addr];
  //   if node.Index? {
  //     if addr == branch.root {
  //       BranchChildrenAreReachable(branch, ranking);
  //     } else {
  //       var numChildren := |branch.Root().children|;
  //       var subTreeAddrs := seq(numChildren, i requires 0 <= i < numChildren => 
  //         branch.ChildAtIdx(i).ReachableAddrsUsingRanking(ranking));
        
  //       UnionSeqOfSetsSoundness(subTreeAddrs);
  //       var k :| 0 <= k < numChildren && addr in subTreeAddrs[k];
  //       BranchReachableAddrClosed(branch.ChildAtIdx(k), ranking, addr);
  //     }
  //   }
  // }

  // // TODO: no better way than repeating this code?
  // // linked's children are always in the reachable set
  // lemma BetreeChildrenAreReachable(branched: BranchedBetree, ranking: Ranking)
  //   requires branched.WF()
  //   requires branched.ValidRanking(ranking)
  //   requires branched.HasRoot()
  //   ensures
  //     forall i | 0 <= i < |branched.Root().children| && branched.Root().children[i].Some? ::
  //       branched.ChildAtIdx(i).root.value in branched.ReachableAddrsUsingRanking(ranking)
  // {
  //   var numChildren := |branched.Root().children|;
  //   var subTreeAddrs := seq(numChildren, i requires 0 <= i < numChildren => branched.ChildAtIdx(i).ReachableAddrsUsingRanking(ranking));
  //   forall i | 0 <= i < numChildren && branched.Root().children[i].Some?
  //   ensures branched.ChildAtIdx(i).root.value in branched.ReachableAddrsUsingRanking(ranking)
  //   {
  //     var childAddr := branched.ChildAtIdx(i).root.value;
  //     assert childAddr in subTreeAddrs[i];
  //   }
  // }

  // // TODO: no better way than repeating this code?
  // lemma BetreeReachableAddrClosed(branched: BranchedBetree, ranking: Ranking, addr: Address)
  //   requires branched.WF()
  //   requires branched.ValidRanking(ranking)
  //   requires branched.HasRoot()
  //   requires addr in branched.ReachableAddrsUsingRanking(ranking)
  //   ensures
  //     var node := branched.diskView.entries[addr];
  //     forall i | 0 <= i < |node.children| && node.children[i].Some? ::
  //       node.children[i].value in branched.ReachableAddrsUsingRanking(ranking)
  //   decreases branched.GetRank(ranking)
  // {
  //   if addr == branched.root.value {
  //     BetreeChildrenAreReachable(branched, ranking);
  //   } else {
  //     var numChildren := |branched.Root().children|;
  //     var subTreeAddrs := seq(numChildren, i requires 0 <= i < numChildren => branched.ChildAtIdx(i).ReachableAddrsUsingRanking(ranking));
  //     assert addr in Sets.UnionSeqOfSets(subTreeAddrs);
  //     Sets.UnionSeqOfSetsSoundness(subTreeAddrs);
  //     var k :| 0 <= k < numChildren && addr in subTreeAddrs[k];
  //     BetreeReachableAddrClosed(branched.ChildAtIdx(k), ranking, addr);
  //   }
  // }

  // lemma SameReachableAddrsForValidRankings (branch: LinkedBranch, r1: Ranking, r2: Ranking)
  //   requires branch.WF()
  //   requires branch.ValidRanking(r1)
  //   requires branch.ValidRanking(r2)
  //   ensures branch.ReachableAddrsUsingRanking(r1) == branch.ReachableAddrsUsingRanking(r2)
  //   decreases branch.GetRank(r1)
  // {
  //   if branch.HasRoot() && branch.Root().Index? {
  //     var node := branch.Root();
  //     var r1Addrs := seq(|node.children|, i requires 0 <= i < |node.children| =>
  //          branch.ChildAtIdx(i).ReachableAddrsUsingRanking(r1));
  //     var r2Addrs := seq(|node.children|, i requires 0 <= i < |node.children| =>
  //          branch.ChildAtIdx(i).ReachableAddrsUsingRanking(r2));

  //     forall i | 0 <= i < |node.children|
  //       ensures branch.ChildAtIdx(i).ReachableAddrsUsingRanking(r1) == 
  //         branch.ChildAtIdx(i).ReachableAddrsUsingRanking(r2) 
  //     {
  //       SameReachableAddrsForValidRankings(branch.ChildAtIdx(i), r1, r2);
  //     }

  //     assert r1Addrs == r2Addrs;
  //     UnionSeqOfSetsSoundness(r1Addrs);
  //     UnionSeqOfSetsSoundness(r2Addrs);
  //   }
  // }

  // predicate LinkedBranchDiskSubset(sub: LinkedBranch, full: LinkedBranch, ranking: Ranking)
  // {
  //   && sub.WF()
  //   && full.WF()
  //   && sub.ValidRanking(ranking)
  //   && full.ValidRanking(ranking)
  //   && sub.root == full.root
  //   && IsSubMap(sub.diskView.entries, full.diskView.entries)
  // }

  // lemma SameReachableAddrsForDiskSubset(sub: LinkedBranch, full: LinkedBranch, ranking: Ranking)
  //   requires LinkedBranchDiskSubset(sub, full, ranking)
  //   ensures sub.ReachableAddrsUsingRanking(ranking) == full.ReachableAddrsUsingRanking(ranking)
  //   decreases sub.GetRank(ranking)
  // {
  //   if sub.HasRoot() && sub.Root().Index? {
  //     var node := sub.Root();
  //     var subAddrs := seq(|node.children|, i requires 0 <= i < |node.children| =>
  //          sub.ChildAtIdx(i).ReachableAddrsUsingRanking(ranking));
  //     var fullAddrs := seq(|node.children|, i requires 0 <= i < |node.children| =>
  //          full.ChildAtIdx(i).ReachableAddrsUsingRanking(ranking));

  //     forall i | 0 <= i < |node.children|
  //       ensures sub.ChildAtIdx(i).ReachableAddrsUsingRanking(ranking) == 
  //         full.ChildAtIdx(i).ReachableAddrsUsingRanking(ranking) 
  //     {
  //       SameReachableAddrsForDiskSubset(sub.ChildAtIdx(i), full.ChildAtIdx(i), ranking);
  //     }

  //     assert subAddrs == fullAddrs;
  //     UnionSeqOfSetsSoundness(subAddrs);
  //     UnionSeqOfSetsSoundness(fullAddrs);
  //   }
  // }

  // lemma SameAllKeysInRangeForDiskSubSet(sub: LinkedBranch, full: LinkedBranch, ranking: Ranking)
  //   requires LinkedBranchDiskSubset(sub, full, ranking)
  //   requires sub.AllKeysInRangeInternal(ranking)
  //   ensures sub.AllKeys(ranking) == full.AllKeys(ranking)
  //   ensures full.AllKeysInRangeInternal(ranking)
  //   decreases sub.GetRank(ranking)
  // {
  //   var node := sub.Root();
  //   if node.Index?  {
  //     forall i | 0 <= i < |node.children|
  //       ensures full.ChildAtIdx(i).AllKeysInRangeInternal(ranking) 
  //       ensures sub.ChildAtIdx(i).AllKeys(ranking) == full.ChildAtIdx(i).AllKeys(ranking)
  //       ensures i < |node.children|-1 ==> full.AllKeysBelowBound(i, ranking)
  //       ensures 0 < i ==> full.AllKeysAboveBound(i, ranking)
  //     {
  //       SameAllKeysInRangeForDiskSubSet(sub.ChildAtIdx(i), full.ChildAtIdx(i), ranking);
  //       if i < |node.children|-1 {
  //         assert sub.AllKeysBelowBound(i, ranking); // trigger
  //       }
  //       if i > 0 {
  //         assert sub.AllKeysAboveBound(i, ranking); // trigger
  //       }
  //     }
  //   }
  // }

  // lemma SameAllKeysInRangeForValidRankings(branch: LinkedBranch, r1: Ranking, r2: Ranking)
  //   requires branch.WF()
  //   requires branch.ValidRanking(r1)
  //   requires branch.ValidRanking(r2)
  //   requires branch.AllKeysInRangeInternal(r1)
  //   ensures branch.AllKeys(r1) == branch.AllKeys(r2)
  //   ensures branch.AllKeysInRangeInternal(r2)
  //   decreases branch.GetRank(r1)
  // {
  //   var node := branch.Root();
  //   if node.Index? {
  //     forall i | 0 <= i < |node.children|
  //       ensures branch.ChildAtIdx(i).AllKeysInRangeInternal(r2) 
  //       ensures branch.ChildAtIdx(i).AllKeys(r1) == branch.ChildAtIdx(i).AllKeys(r2)
  //       ensures i < |node.children|-1 ==> branch.AllKeysBelowBound(i, r2)
  //       ensures 0 < i ==> branch.AllKeysAboveBound(i, r2)
  //     {
  //       SameAllKeysInRangeForValidRankings(branch.ChildAtIdx(i), r1, r2);
  //       if i < |node.children|-1 {
  //         assert branch.AllKeysBelowBound(i, r1); // trigger
  //       }
  //       if i > 0 {
  //         assert branch.AllKeysAboveBound(i, r1); // trigger
  //       }
  //     } 
  //   }
  // }
  
  // lemma AddBranchWF(branches: Branches, branch: LinkedBranch) 
  //   requires branches.AddBranch.requires(branch)
  //   ensures branches.AddBranch(branch).WF()
  // {
  //   var out := branches.AddBranch(branch);
  //   assert IsSubMap(branch.diskView.entries, out.diskView.entries); 

  //   forall r | r in out.roots
  //     ensures out.GetBranch(r).Acyclic()
  //     ensures out.GetBranch(r).AllKeysInRange()
  //     ensures r != branch.root ==> (out.GetBranch(r).ReachableAddrs() == branches.GetBranch(r).ReachableAddrs())
  //   {
  //     var branch := if r == branch.root then branch else branches.GetBranch(r);
  //     var outBranch := out.GetBranch(r);
      
  //     assert outBranch.ValidRanking(BranchTightRanking(branch)); // trigger
  //     SameAllKeysInRangeForValidRankings(branch, branch.TheRanking(), outBranch.TheRanking());
  //     SameAllKeysInRangeForDiskSubSet(branch, outBranch, outBranch.TheRanking());

  //     SameReachableAddrsForDiskSubset(branch, outBranch, outBranch.TheRanking());
  //     SameReachableAddrsForValidRankings(branch, outBranch.TheRanking(), branch.TheRanking());
  //   }

  //   var outBranch := out.GetBranch(branch.root);
  //   SameReachableAddrsForDiskSubset(branch, outBranch, outBranch.TheRanking());
  //   SameReachableAddrsForValidRankings(branch, outBranch.TheRanking(), branch.TheRanking());
  //   assert branch.ReachableAddrs() == outBranch.ReachableAddrs();
  // }
     
  // lemma RemoveBranchWF(branches: Branches, root: Address) 
  //   requires branches.RemoveBranch.requires(root)
  //   ensures branches.RemoveBranch(root).WF() 
  // {
  //   var out := branches.RemoveBranch(root);
  //   var branch := branches.GetBranch(root);

  //   assert (forall r | r in out.roots :: out.diskView.ValidAddress(r));

  //   // TODO: prove this, likely need to connect Reachable Addrs to nodes in diskView
  //   // this may require another predicate in WF that says things in diskview only reachable
  //   // addrs of something have reference of it

  //   // && diskView.WF() // ensures all nodes are connected // uh oh
  //   // && (forall root | root in roots :: GetBranch(root).Acyclic()) // uh oh 
  //   // && (forall root | root in roots :: GetBranch(root).AllKeysInRange()) // uhoh
  //   // && BranchesDisjoint()
  //   assume false;
  // }

  // lemma BetreeTightPreservesWF(branched: BranchedBetree, ranking: Ranking)
  //   requires branched.WF()
  //   requires branched.ValidRanking(ranking)
  //   ensures branched.BuildTightTree().WF()
  //   decreases branched.GetRank(ranking)
  // {
  //   forall addr | addr in branched.BuildTightTree().diskView.entries
  //   ensures branched.BuildTightTree().diskView.NodeHasNondanglingChildPtrs(branched.BuildTightTree().diskView.entries[addr])
  //   {
  //     BetreeReachableAddrClosed(branched, branched.TheRanking(), addr);
  //   }
  // }

  // // TODO: feels too much copy pasting
  // lemma BetreeTightRanking(branched: BranchedBetree, ranking: Ranking) returns (tightRanking : Ranking)
  //   requires branched.WF()
  //   requires branched.ValidRanking(ranking)
  //   ensures branched.diskView.entries.Keys <= tightRanking.Keys
  //   ensures branched.ValidRanking(tightRanking)
  // {
  //   tightRanking := map addr | addr in branched.diskView.entries && addr in ranking :: ranking[addr];
  // }

  // lemma ValidRankingAllTheWayDown(ranking: Ranking, path: Path)
  //   requires path.Valid()
  //   requires path.branched.ValidRanking(ranking)
  //   ensures 0 < path.depth ==> path.Subpath().branched.ValidRanking(ranking)
  //   ensures path.Target().ValidRanking(ranking)
  //   decreases path.depth
  // {
  //   if 0 < path.depth {
  //     ValidRankingAllTheWayDown(ranking, path.Subpath());
  //   }
  // }

  // // Inv properties for each step
  // lemma InvNextInternalGrowStep(v: Variables, v': Variables, lbl: TransitionLabel, step: Step)
  //   requires Inv(v)
  //   requires NextStep(v, v', lbl, step)
  //   requires step.InternalGrowStep?
  //   ensures v'.branched.Acyclic()
  // {
  //   var oldRanking := BetreeTightRanking(v.branched, v.branched.TheRanking());
  //   var newRanking;

  //   if v.branched.HasRoot() {
  //     var oldRootRank := oldRanking[v.branched.root.value];
  //     newRanking := oldRanking[step.newRootAddr := oldRootRank+1];
  //   } else {
  //     var newRootRank := if |oldRanking.Values| == 0 then 1 else SetMax(oldRanking.Values) + 1;
  //     newRanking := oldRanking[step.newRootAddr := newRootRank];
  //   }
  //   var newRoot := InsertGrowReplacement(v.branched, step.newRootAddr);
  //   BetreeTightPreservesWF(newRoot, newRanking);
  //   assert v'.branched.ValidRanking(newRanking); // witness
  // }

  // // TODO: wait a bit, too much same thing
  // lemma InvNextInternalSplitStep(v: Variables, v': Variables, lbl: TransitionLabel, step: Step)
  //   requires Inv(v)
  //   requires NextStep(v, v', lbl, step)
  //   requires step.InternalSplitStep?
  //   ensures Inv(v')
  // {
  //   var oldRanking := BetreeTightRanking(v.branched, v.branched.TheRanking());
  //   var replacement := step.path.Target().SplitParent(step.request, step.newAddrs);
  
  //   ValidRankingAllTheWayDown(oldRanking, step.path);
  //   // var rankingAfterReplacement := RankingAfterSplitReplacement(step.path.Target(), oldRanking, step.request, step.newAddrs);
  //   // var linkedAfterSubstitution := step.path.Substitute(replacement, step.pathAddrs);
  //   // var newRanking := RankingAfterSubstitution(replacement, rankingAfterReplacement, step.path, step.pathAddrs);
  //   // BuildTightPreservesWF(linkedAfterSubstitution, newRanking);
  //   // BuildTightMaintainsRankingValidity(linkedAfterSubstitution, newRanking);

  //   assume false;
  // }
  
  // lemma InvNextInternalFlushMemtableStep(v: Variables, v': Variables, lbl: TransitionLabel, step: Step)
  //   requires Inv(v)
  //   requires NextStep(v, v', lbl, step)
  //   requires step.InternalFlushMemtableStep?
  //   ensures v'.branched.Acyclic()
  // {
  //   var newRoot := InsertInternalFlushMemtableReplacement(v.branched, step.branch, step.newRootAddr);
  //   AddBranchWF(v.branched.branches, step.branch);
  //   assert newRoot.branches.WF();

  //   if v.branched.HasRoot() {
  //     var oldRanking := BetreeTightRanking(v.branched, v.branched.TheRanking());
  //     var oldRootRank := oldRanking[v.branched.root.value];
  //     var newRanking := oldRanking[step.newRootAddr := oldRootRank+1];  // witness
  //     BetreeTightPreservesWF(newRoot, newRanking);
  //     assert v'.branched.ValidRanking(newRanking);
  //   } else {
  //     var newRanking := map[step.newRootAddr := 0];  // witness
  //     BetreeTightPreservesWF(newRoot, newRanking);
  //     assert v'.branched.ValidRanking(newRanking);
  //   }
  // }

  // lemma InvNextInternalPruneBranches(v: Variables, v': Variables, lbl: TransitionLabel, step: Step)
  //   requires Inv(v)
  //   requires NextStep(v, v', lbl, step)
  //   requires step.InternalPruneBranchesStep?
  //   ensures Inv(v')
  // {
  //   RemoveBranchWF(v.branched.branches, step.rootToRemove);
  //   assert v'.branched.branches.WF();
  //   assert v'.branched.ValidRanking(v.branched.TheRanking());
  // }

  predicate RootCoversTotalDomain(branched: BranchedBetree)
    requires branched.WF()
  {
    branched.HasRoot() ==> branched.Root().MyDomain() == TotalDomain()
  }

  // // Properties a StampedBetree must carry from Freeze back to Init
  predicate InvBranchedBetree(branched: BranchedBetree)
  {
    && branched.Acyclic()
    && RootCoversTotalDomain(branched)
  }

  predicate Inv(v: Variables)
  {
    && InvBranchedBetree(v.branched)
    && v.WF()
  }

  lemma InvNext(v: Variables, v': Variables, lbl: TransitionLabel)
    requires Inv(v)
    requires Next(v, v', lbl)
    ensures Inv(v')
  {
    assume false;
    // var step: Step :| NextStep(v, v', lbl, step);
    // match step {
    //   case QueryStep(receipt) => {
    //     assert Inv(v');
    //   }
    //   case PutStep() => {
    //     assert Inv(v');
    //   }
    //   case QueryEndLsnStep() => {
    //     assert Inv(v');
    //   }
    //   case FreezeAsStep() => {
    //     assert Inv(v');
    //   }
    //   case InternalGrowStep(_) => {
    //     InvNextInternalGrowStep(v, v', lbl, step);
    //   }
    //   case InternalSplitStep(_, _, _, _) => {
    //     assume false;
    //     // InvNextInternalSplitStep(v, v', lbl, step);
    //   }
    //   case InternalFlushStep(_, _, _, _, _, _) => {
    //     assume false;
    //     // InvNextInternalFlushStep(v, v', lbl, step);
    //   }
    //   case InternalFlushMemtableStep(_,_) => {
    //     InvNextInternalFlushMemtableStep(v, v', lbl, step);
    //   }
    //   case InternalPruneBranchesStep(_) => {
    //     InvNextInternalPruneBranches(v, v', lbl, step);
    //   }
    //   case InternalCompactStep(_, _, _, _, _, _) => {
    //     // compact is a heavy one
    //     assume false;
    //     // InvNextInternalCompactStep(v, v', lbl, step);
    //   }
    //   case InternalNoOpStep() => {
    //     assert Inv(v');
    //   }
    // }
  }

  lemma NextRefines(v: Variables, v': Variables, lbl: TransitionLabel)
    requires Inv(v)
    requires Next(v, v', lbl)
    ensures Inv(v')
    ensures LinkedBetree.Next(I(v), I(v'), ILbl(lbl))
  {
    InvNext(v, v', lbl);
    assume false;
    // var step: Step :| NextStep(v, v', lbl, step);
    // match step {
    //   case QueryStep(receipt) => {
    //     assert PivotBetree.NextStep(I(v), I(v'), ILbl(lbl), IStep(step));
    //   }
    //   case PutStep() => {
    //     assert PivotBetree.NextStep(I(v), I(v'), ILbl(lbl), IStep(step));
    //   }
    //   case QueryEndLsnStep() => {
    //     assert PivotBetree.NextStep(I(v), I(v'), ILbl(lbl), IStep(step));
    //   }
    //   case FreezeAsStep() => {
    //     assert PivotBetree.NextStep(I(v), I(v'), ILbl(lbl), IStep(step));
    //   }
    //   case InternalGrowStep(_) => {
    //     InternalGrowStepRefines(v, v', lbl, step);
    //   }
    //   case InternalSplitStep(_, _, _, _) => {
    //     InternalSplitStepRefines(v, v', lbl, step);
    //   }
    //   case InternalFlushStep(_, _, _, _, _) => {
    //     InternalFlushStepRefines(v, v', lbl, step);
    //   }
    //   case InternalFlushMemtableStep(_) => {
    //     InternalFlushMemtableStepRefines(v, v', lbl, step);
    //   }
    //   case InternalCompactStep(_, _, _, _) => {
    //     InternalCompactStepRefines(v, v', lbl, step);
    //   }
    //   case InternalNoOpStep() => {
    //     assert PivotBetree.NextStep(I(v), I(v'), ILbl(lbl), IStep(step));
    //   }
    // }
  }
}