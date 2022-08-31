// Copyright 2018-2021 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, and University of Washington
// SPDX-License-Identifier: BSD-2-Clause

include "LinkedBetree.i.dfy"
include "BranchedBetree.i.dfy"

module BranchedBetreeRefinement {
  import opened BoundedPivotsLib
  import LinkedBetree = LinkedBetreeMod
  import opened BranchedBetreeMod
  import opened LinkedBranchMod
  import opened BranchesMod
  import opened StampedMod
  import opened DomainMod
  import opened Buffers
  import opened KeyType
  import opened Sequences

  import opened ValueMessage // test

  function ILbl(lbl: TransitionLabel) : LinkedBetree.TransitionLabel
  {
    match lbl
      case QueryLabel(endLsn, key, value) => LinkedBetree.QueryLabel(endLsn, key, value)
      case PutLabel(puts) => LinkedBetree.PutLabel(puts)
      case QueryEndLsnLabel(endLsn) => LinkedBetree.QueryEndLsnLabel(endLsn)
      case FreezeAsLabel(stampedBetree) => LinkedBetree.FreezeAsLabel(
        if stampedBetree.value.WF() && stampedBetree.value.Valid()
        then IStampedBetree(stampedBetree)
        else IStampedBetree(EmptyImage())  // "silly" case, since we never interpret non-(WF+Valid) things
      )
      case InternalAllocationsLabel(treeAddrs, _) => LinkedBetree.InternalAllocationsLabel(treeAddrs)
      case InternalLabel() => LinkedBetree.InternalLabel()
  }

  function ActiveBufferKeysForChild(node: BetreeNode, childIdx: nat, bufferIdx: nat) : iset<Key>
    requires node.WF()
    requires childIdx < |node.children|
    requires bufferIdx < |node.buffers|
  {
    if node.activeBufferRanges[childIdx] <= bufferIdx 
    then node.DomainRoutedToChild(childIdx).KeySet()
    else iset{}
  }

  function ActiveBufferKeys(node: BetreeNode, bufferIdx: nat) : iset<Key>
    requires node.WF()
    requires bufferIdx < |node.buffers|
  {
    iset k, i | 0 <= i < |node.children| && k in ActiveBufferKeysForChild(node, i, bufferIdx) :: k
  }

  function IBuffer(node: BetreeNode, branch: LinkedBranch, bufferIdx: nat) : Buffer
    requires node.WF()
    requires bufferIdx < |node.buffers|
    requires branch.Acyclic()
    requires branch.AllKeysInRange()
  {
    var buffer := branch.I().I();
    buffer.ApplyFilter(ActiveBufferKeys(node, bufferIdx))
  }

  function IBufferStack(node: BetreeNode, branches: Branches) : BufferStack
    requires node.WF()
    requires branches.WF()
    requires forall buffer | buffer in node.buffers :: branches.ValidBranch(buffer)
  {
    BufferStack( seq (|node.buffers|, 
         i requires 0 <= i < |node.buffers| => 
         IBuffer(node, branches.GetBranch(node.buffers[i]), i)))
  }

  function IBranchedBetreeNode(node: BetreeNode, branches: Branches) : (out: LinkedBetree.BetreeNode)
    requires node.WF()
    requires branches.WF()
    requires forall buffer | buffer in node.buffers :: branches.ValidBranch(buffer)
    ensures out.WF()
  {
    LinkedBetree.BetreeNode(IBufferStack(node, branches), node.pivotTable, node.children)
  }

  function IDiskView(branched: BranchedBetree) : (out: LinkedBetree.DiskView)
    requires branched.WF()
    requires branched.Valid()
    ensures out.WF()
  {
    var entries := branched.diskView.entries;
    var dv := LinkedBetree.DiskView( map addr | addr in entries ::
                IBranchedBetreeNode(entries[addr], branched.branches));

    assert dv.HealthyChildPointers(); // trigger
    dv
  }

  function IBranchedBetree(branched: BranchedBetree) : (out: LinkedBetree.LinkedBetree)
    requires branched.WF()
    requires branched.Valid()
    ensures out.WF()
  {
    LinkedBetree.LinkedBetree(branched.root, IDiskView(branched))
  }

  function IStampedBetree(stampedBetree: StampedBetree) : (out: LinkedBetree.StampedBetree)
    requires stampedBetree.value.WF()
    requires stampedBetree.value.Valid()
    ensures out.value.WF()
  {
    Stamped(IBranchedBetree(stampedBetree.value), stampedBetree.seqEnd)
  }

  lemma IBranchedBetreeAcyclic(branched: BranchedBetree) 
    requires branched.Acyclic()
    requires branched.Valid()
    ensures IBranchedBetree(branched).Acyclic()
  {
    assert IBranchedBetree(branched).ValidRanking(branched.TheRanking());
  }

  // Interpretation functions for Path
  function IPath(path: Path) : LinkedBetree.Path
    requires path.Valid()
  {
    LinkedBetree.Path(IBranchedBetree(path.branched), path.key, path.depth) 
  }

  lemma TargetCommutesWithI(path: Path)
    requires path.Valid()
    ensures IPath(path).Valid()
    ensures IPath(path).Target() == IBranchedBetree(path.Target())
    decreases path.depth
  {
    IBranchedBetreeAcyclic(path.branched);
    if 0 < path.depth {
      TargetCommutesWithI(path.Subpath());
    }
  }

  // Interpretation functions for Query receipts
  function IReceiptLine(line: QueryReceiptLine) : (out: LinkedBetree.QueryReceiptLine)
    requires line.branched.WF()
    requires line.branched.Valid()
  {
    LinkedBetree.QueryReceiptLine(IBranchedBetree(line.branched), line.result)
  }

   function IReceipt(receipt: QueryReceipt) : (out: LinkedBetree.QueryReceipt)
    requires receipt.Valid()
  {
    LinkedBetree.QueryReceipt(
      receipt.key, 
      IBranchedBetree(receipt.branched), 
      seq(|receipt.lines|, i requires 0<=i<|receipt.lines| => IReceiptLine(receipt.lines[i])))
  }

  lemma ActiveBuffersForKeyConsistent(node: BetreeNode, key: Key, start: nat)
    requires node.WF()
    requires node.KeyInDomain(key)
    requires start == node.ActiveBuffersForKey(key)
    ensures forall i:nat | i < start :: key !in ActiveBufferKeys(node, i)
    ensures forall i:nat | start <= i < |node.buffers| :: key in ActiveBufferKeys(node, i)
  {
    forall i:nat | start <= i < |node.buffers|
      ensures key in ActiveBufferKeys(node, i)
    {
      var childIdx := Route(node.pivotTable, key);
      assert key in ActiveBufferKeysForChild(node, childIdx, i); // trigger
    }
  }

  function BranchesBufferStack(branches: Branches, buffers: seq<Address>) : BufferStack
    requires branches.WF()
    requires (forall addr | addr in buffers :: branches.ValidBranch(addr))
  {
    BufferStack(seq (|buffers|, i requires 0 <= i < |buffers| => branches.GetBranch(buffers[i]).I().I()))
  }

  lemma BranchesBufferStackQueryConsistent(key: Key, branches: Branches, buffers: seq<Address>, count: nat)
    requires count <= |buffers|
    requires BranchesBufferStack.requires(branches, buffers)
    ensures BranchesBufferStack(branches, buffers).QueryUpTo(key, count) == branches.Query(key, buffers[..count])
  {
    if count > 0 {
      var bufferstack := BranchesBufferStack(branches, buffers);
      var branch := branches.GetBranch(buffers[count-1]);
      var msg := if branch.Query(key).Some? then branch.Query(key).value else Update(NopDelta());

      assert bufferstack.buffers[count-1].Query(key) == msg;
      assert buffers[..count-1] == DropLast(buffers[..count]);

      BranchesBufferStackQueryConsistent(key, branches, buffers, count-1);
    }
  }

  lemma IReceiptValid(receipt: QueryReceipt) 
    requires receipt.Valid()
    ensures IReceipt(receipt).Valid()
  {
    var ireceipt := IReceipt(receipt);
    var key := receipt.key;

    IBranchedBetreeAcyclic(receipt.branched);

    forall i:nat | i < |ireceipt.lines|
      ensures ireceipt.lines[i].linked.Acyclic()
    {
      IBranchedBetreeAcyclic(receipt.lines[i].branched);
    }

    forall i:nat | i < |ireceipt.lines|-1 
      ensures ireceipt.Node(i).KeyInDomain(key)
      ensures ireceipt.ChildLinkedAt(i)
    {
      assert receipt.Node(i).KeyInDomain(key);  // trigger
      assert receipt.ChildLinkedAt(i);  // trigger
    }
  
    forall i:nat | i < |ireceipt.lines| - 1 
    ensures ireceipt.ResultLinkedAt(i)
    {
      assert receipt.ResultLinkedAt(i);  // trigger
      
      var key := ireceipt.key;
      var branched := receipt.lines[i].branched;
      var linked := ireceipt.lines[i].linked;

      var node := branched.Root();
      var start := node.ActiveBuffersForKey(key);
      var activeBuffers := node.buffers[start..];
      var activeBufferStack := BranchesBufferStack(branched.branches, activeBuffers);

      assert activeBuffers[..|activeBuffers|] == activeBuffers;
      BranchesBufferStackQueryConsistent(key, branched.branches, activeBuffers, |activeBuffers|);
      assert activeBufferStack.Query(key) == branched.branches.Query(key, activeBuffers);

      var buffers := linked.Root().buffers;
      ActiveBuffersForKeyConsistent(node, key, start);

      var right := buffers.SliceRight(start);
      right.QueryUpToEquivalent(key, activeBufferStack, |right.buffers|);
      buffers.QueryEmptyLeft(key, start, |buffers.buffers|);

      assert ireceipt.ResultLinkedAt(i);  // trigger
    }
  }

  // Interpretation functions for Steps
  function IStepDefn(step: Step) : (out: LinkedBetree.Step)
    requires step.WF()
  {
    match step {
      case QueryStep(receipt) => LinkedBetree.QueryStep(IReceipt(receipt))
      case PutStep() => LinkedBetree.PutStep()
      case QueryEndLsnStep() => LinkedBetree.QueryEndLsnStep()
      case FreezeAsStep() => LinkedBetree.FreezeAsStep()
      case InternalGrowStep(newRootAddr) => LinkedBetree.InternalGrowStep(newRootAddr)
      case InternalSplitStep(path, request, newAddrs, pathAddrs) => 
            LinkedBetree.InternalSplitStep(IPath(path), request, newAddrs, pathAddrs)
      case InternalFlushMemtableStep(newRootAddr, _) => LinkedBetree.InternalFlushMemtableStep(newRootAddr)
      case InternalFlushStep(path, childIdx, targetAddr, targetChildAddr, pathAddrs, _) =>
            LinkedBetree.InternalFlushStep(IPath(path), childIdx, targetAddr, targetChildAddr, pathAddrs)
      case InternalCompactStep(path, compactStart, compactEnd, _, targetAddr, pathAddrs) => (
          var linked := IBranchedBetree(path.Target());
          var compactedBuffers := linked.Root().buffers.buffers[compactStart..compactEnd];
          LinkedBetree.InternalCompactStep(IPath(path), BufferStack(compactedBuffers), targetAddr, pathAddrs))
      case InternalPruneBranchesStep(_) => LinkedBetree.InternalNoOpStep()
      case InternalNoOpStep() => LinkedBetree.InternalNoOpStep()
    }
  }

  lemma IStepWF(step: Step)
    requires IStepDefn.requires(step)
    ensures IStepDefn(step).WF()
  {
    var istep := IStepDefn(step);
    match step {
      case QueryStep(receipt) => { IReceiptValid(receipt); }
      case InternalSplitStep(path, request, newAddrs, pathAddrs) => { TargetCommutesWithI(path); }
      case InternalFlushStep(path, childIdx, _, _, _, _) => { TargetCommutesWithI(path); }
      case InternalCompactStep(path, compactStart, compactEnd, compactedBranch, _, _) => { 
        TargetCommutesWithI(path);

        var linked := istep.path.Target();
        var branched := path.Target();
        var node := branched.Root();

        assert branched.branches == path.branched.branches;
        assert node.CompactedBranchEquivalence(branched.branches, compactStart, compactEnd, compactedBranch);
         
        // var compactedBranch := branched.Root().buffers[compactStart..compactEnd];
        
        assert IPath(path) == istep.path;
        assert IBranchedBetree(branched) == linked;
        
        forall k | AnyKey(k)
          ensures linked.Root().buffers.Query(k) == istep.compactedBuffers.Query(k) 
        {
          // ActiveBuffersForKeyConsistent(node, k, node.ActiveBuffersForKey(k));


    // ensures forall i:nat | i < start :: key !in ActiveBufferKeys(node, i)
    // ensures forall i:nat | start <= i < |node.buffers| :: key in ActiveBufferKeys(node, i)

          if node.KeyInDomain(k) && (compactStart <= node.ActiveBuffersForKey(k) < compactEnd) {
             
            assume linked.Root().buffers.Query(k) == branched.branches.Query(k, node.buffers[compactStart..compactEnd]);

            assume compactedBranch.Query(k).Some?;

            assume istep.compactedBuffers.Query(k) == compactedBranch.Query(k).value;

            assert branched.branches.Query(k, node.buffers[compactStart..compactEnd]) == compactedBranch.Query(k).value;


          } else {
            
            assume false;
          }


      

        //   assume linkedNode.buffers.Query(k) == 

        //   // we want to show linkednode buffers equivalent to the other buffers
        //   // and the compactedbuffers too 

        //   // ah nah that's not how you do it , I understand lol
        //   // forall i:nat | i < |linkedNode.buffers.buffers|
        //   //   ensures linkedNode.buffers.buffers[i].Query(k) == istep.compactedBuffers.buffers[i].Query(k)
        //   // {
          // assume false;
        //   // }

        //   // linkedNode.buffers.QueryUpToEquivalent(k, istep.compactedBuffers, |linkedNode.buffers.buffers|);
        }

        //   ensures forall i:nat |:: buffers[i].Query(key) == other.buffers[i].Query(key)

        // assume linkedNode.buffers.Equivalent(istep.compactedBuffers);

        // assume false; 


        // assert step.path.Target().Root().CompactedBranchEquivalence(v.branched.branches, step.compactStart, step.compactEnd, step.compactedBranch);
        // assert equivalence
        // assume istep.path.Target().Root().buffers.Equivalent(istep.compactedBuffers);
        // we need 

      //   IPathValid(step.path);
      //   TargetCommutesWithI(step.path);
        // assert istep.WF();  // case boilerplate
      }
      case _ =>    {  assert istep.WF(); }
    }
  }

  function IStep(step: Step) : (out: LinkedBetree.Step)
    requires step.WF()
    ensures out.WF()
  {
    IStepWF(step);
    IStepDefn(step)
  }


}