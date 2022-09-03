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
  import opened GenericDisk
  import opened Maps
  import opened Sets

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

  // Branch Functions and Lemmas

  function TightRanking(branch: LinkedBranch) : (out: Ranking)
    requires branch.Acyclic()
    ensures branch.ValidRanking(out)
    ensures out.Keys <= branch.ReachableAddrs()
  {
    var ranking := branch.TheRanking();
    var tightRanking := MapRestrict(ranking, branch.ReachableAddrs());

    assert branch.ValidRanking(tightRanking) by
    {
      forall addr | addr in tightRanking && addr in branch.diskView.entries 
        ensures branch.diskView.NodeChildrenRespectsRank(tightRanking, addr)
      {
        ReachableAddrClosed(branch, ranking, addr);
        assert branch.diskView.NodeChildrenRespectsRank(tightRanking, addr);
      }
    }

    tightRanking
  }

  lemma ChildrenAreReachable(branch: LinkedBranch, ranking: Ranking)
    requires branch.WF()
    requires branch.Root().Index?
    requires branch.ValidRanking(ranking)
    ensures forall i | 0 <= i < |branch.Root().children| :: 
      branch.Root().children[i] in branch.ReachableAddrsUsingRanking(ranking)
  {
    var numChildren := |branch.Root().children|;
    var subTreeAddrs := seq(numChildren, i requires 0 <= i < numChildren => 
      branch.ChildAtIdx(i).ReachableAddrsUsingRanking(ranking));

    forall i | 0 <= i < numChildren  
      ensures branch.Root().children[i] in branch.ReachableAddrsUsingRanking(ranking)
    {
      assert branch.Root().children[i] in subTreeAddrs[i];
    }
  }

  lemma ReachableAddrClosed(branch: LinkedBranch, ranking: Ranking, addr: Address)
    requires branch.WF()
    requires branch.ValidRanking(ranking)
    requires addr in branch.ReachableAddrsUsingRanking(ranking)
    ensures 
      var node := branch.diskView.entries[addr];
      && (node.Index? ==> (forall i | 0 <= i < |node.children| :: 
        node.children[i] in branch.ReachableAddrsUsingRanking(ranking)))
    decreases branch.GetRank(ranking)
  {
    var node := branch.diskView.entries[addr];
    if node.Index? {
      if addr == branch.root {
        ChildrenAreReachable(branch, ranking);
      } else {
        var numChildren := |branch.Root().children|;
        var subTreeAddrs := seq(numChildren, i requires 0 <= i < numChildren => 
          branch.ChildAtIdx(i).ReachableAddrsUsingRanking(ranking));
        
        UnionSeqOfSetsSoundness(subTreeAddrs);
        var k :| 0 <= k < numChildren && addr in subTreeAddrs[k];
        ReachableAddrClosed(branch.ChildAtIdx(k), ranking, addr);
      }
    }
  }

  predicate LinkedBranchDiskSubset(sub: LinkedBranch, full: LinkedBranch, ranking: Ranking)
  {
    && sub.WF()
    && full.WF()
    && sub.ValidRanking(ranking)
    && full.ValidRanking(ranking)
    && sub.root == full.root
    && IsSubMap(sub.diskView.entries, full.diskView.entries)
  }

  lemma ReachableAddrsForValidRanking(branch: LinkedBranch, r1: Ranking, r2: Ranking)
    requires branch.WF()
    requires branch.ValidRanking(r1)
    requires branch.ValidRanking(r2)
    ensures branch.ReachableAddrsUsingRanking(r1) == branch.ReachableAddrsUsingRanking(r2)
    decreases branch.GetRank(r1)
  {
    if branch.HasRoot() && branch.Root().Index? {
      var node := branch.Root();
      var r1Addrs := seq(|node.children|, i requires 0 <= i < |node.children| =>
           branch.ChildAtIdx(i).ReachableAddrsUsingRanking(r1));
      var r2Addrs := seq(|node.children|, i requires 0 <= i < |node.children| =>
           branch.ChildAtIdx(i).ReachableAddrsUsingRanking(r2));

      forall i | 0 <= i < |node.children|
        ensures branch.ChildAtIdx(i).ReachableAddrsUsingRanking(r1) == 
          branch.ChildAtIdx(i).ReachableAddrsUsingRanking(r2) 
      {
        ReachableAddrsForValidRanking(branch.ChildAtIdx(i), r1, r2);
      }

      assert r1Addrs == r2Addrs;
      UnionSeqOfSetsSoundness(r1Addrs);
      UnionSeqOfSetsSoundness(r2Addrs);
    }
  }


  lemma ReachableAddrsForDiskSubSet(sub: LinkedBranch, full: LinkedBranch, ranking: Ranking)
    requires LinkedBranchDiskSubset(sub, full, ranking)
    ensures sub.ReachableAddrsUsingRanking(ranking) == full.ReachableAddrsUsingRanking(ranking)
    decreases sub.GetRank(ranking)
  {
    if sub.HasRoot() && sub.Root().Index? {
      var node := sub.Root();
      var subAddrs := seq(|node.children|, i requires 0 <= i < |node.children| =>
           sub.ChildAtIdx(i).ReachableAddrsUsingRanking(ranking));
      var fullAddrs := seq(|node.children|, i requires 0 <= i < |node.children| =>
           full.ChildAtIdx(i).ReachableAddrsUsingRanking(ranking));

      forall i | 0 <= i < |node.children|
        ensures sub.ChildAtIdx(i).ReachableAddrsUsingRanking(ranking) == 
          full.ChildAtIdx(i).ReachableAddrsUsingRanking(ranking) 
      {
        ReachableAddrsForDiskSubSet(sub.ChildAtIdx(i), full.ChildAtIdx(i), ranking);
      }

      assert subAddrs == fullAddrs;
      UnionSeqOfSetsSoundness(subAddrs);
      UnionSeqOfSetsSoundness(fullAddrs);
    }
  }

  lemma AllKeysForDiskSubSet(sub: LinkedBranch, full: LinkedBranch, ranking: Ranking)
    requires LinkedBranchDiskSubset(sub, full, ranking)
    ensures sub.AllKeys(ranking) == full.AllKeys(ranking)
    decreases sub.GetRank(ranking)
  {
    var node := sub.Root();
    assert node == full.Root();

    if node.Index? {
      forall i | 0 <= i < |node.children|
        ensures sub.ChildAtIdx(i).AllKeys(ranking) == full.ChildAtIdx(i).AllKeys(ranking)
      {
        AllKeysForDiskSubSet(sub.ChildAtIdx(i), full.ChildAtIdx(i), ranking);
      }
    }
  }

  lemma AllKeysInRangeForDiskSubSet(sub: LinkedBranch, full: LinkedBranch, ranking: Ranking)
    requires LinkedBranchDiskSubset(sub, full, ranking)
    ensures sub.AllKeysInRangeInternal(ranking) ==> full.AllKeysInRangeInternal(ranking)
    decreases sub.GetRank(ranking)
  {
    var node := sub.Root();
    if node.Index? && sub.AllKeysInRangeInternal(ranking) {
      AllKeysForDiskSubSet(sub, full, ranking);

      forall i | 0 <= i < |node.children|
        ensures full.ChildAtIdx(i).AllKeysInRangeInternal(ranking) 
        ensures i < |node.children|-1 ==> full.AllKeysBelowBound(i, ranking)
        ensures 0 < i ==> full.AllKeysAboveBound(i, ranking)
      {
        AllKeysInRangeForDiskSubSet(sub.ChildAtIdx(i), full.ChildAtIdx(i), ranking);
        AllKeysForDiskSubSet(sub.ChildAtIdx(i), full.ChildAtIdx(i), ranking);

        if i < |node.children|-1 {
          assert sub.AllKeysBelowBound(i, ranking); // trigger
        }
        if i > 0 {
          assert sub.AllKeysAboveBound(i, ranking); // trigger
        }
      } 
    }
  }

  lemma AllKeysForValidRankings(branch: LinkedBranch, r1: Ranking, r2: Ranking)
    requires branch.WF()
    requires branch.ValidRanking(r1)
    requires branch.ValidRanking(r2)
    ensures branch.AllKeys(r1) == branch.AllKeys(r2)
    decreases branch.GetRank(r1)
  {
    if branch.Root().Index? {
      forall i | 0 <= i < |branch.Root().children|
        ensures branch.ChildAtIdx(i).AllKeys(r1) == branch.ChildAtIdx(i).AllKeys(r2)
      {
        AllKeysForValidRankings(branch.ChildAtIdx(i), r1, r2);
      }
    }
  }

  lemma AllKeysInRangeForValidRankings(branch: LinkedBranch, r1: Ranking, r2: Ranking)
    requires branch.WF()
    requires branch.ValidRanking(r1)
    requires branch.ValidRanking(r2)
    ensures branch.AllKeysInRangeInternal(r1) ==> branch.AllKeysInRangeInternal(r2)
    decreases branch.GetRank(r1)
  {
    var node := branch.Root();
    if node.Index? && branch.AllKeysInRangeInternal(r1) {
      AllKeysForValidRankings(branch, r1, r2);

      forall i | 0 <= i < |node.children|
        ensures branch.ChildAtIdx(i).AllKeysInRangeInternal(r2) 
        ensures i < |node.children|-1 ==> branch.AllKeysBelowBound(i, r2)
        ensures 0 < i ==> branch.AllKeysAboveBound(i, r2)
      {
        AllKeysInRangeForValidRankings(branch.ChildAtIdx(i), r1, r2);
        AllKeysForValidRankings(branch.ChildAtIdx(i), r1, r2);

        if i < |node.children|-1 {
          assert branch.AllKeysBelowBound(i, r1); // trigger
        }
        if i > 0 {
          assert branch.AllKeysAboveBound(i, r1); // trigger
        }
      } 
    }
  }
  
  lemma AddBranchWF(branches: Branches, newBranch: LinkedBranch) 
    requires branches.AddBranch.requires(newBranch)
    ensures branches.AddBranch(newBranch).WF()
  {
    var out := branches.AddBranch(newBranch);

    forall r | r in out.roots
      ensures out.GetBranch(r).Acyclic()
    {
      var b := if r == newBranch.root then newBranch else branches.GetBranch(r);
      assert out.GetBranch(r).ValidRanking(TightRanking(b));
    }

    assert IsSubMap(newBranch.diskView.entries, out.diskView.entries);

    var outBranch := out.GetBranch(newBranch.root);
    ReachableAddrsForDiskSubSet(newBranch, outBranch, TightRanking(newBranch));
    ReachableAddrsForValidRanking(newBranch, TightRanking(newBranch), newBranch.TheRanking());
    ReachableAddrsForValidRanking(outBranch, TightRanking(newBranch), outBranch.TheRanking());
    assert newBranch.ReachableAddrs() == outBranch.ReachableAddrs();

    AllKeysInRangeForValidRankings(newBranch, newBranch.TheRanking(), outBranch.TheRanking());
    AllKeysInRangeForDiskSubSet(newBranch, out.GetBranch(newBranch.root), outBranch.TheRanking());
    assert out.GetBranch(newBranch.root).AllKeysInRange();

    forall r | r in branches.roots
      ensures out.GetBranch(r).AllKeysInRange()
      ensures out.GetBranch(r).ReachableAddrs() == branches.GetBranch(r).ReachableAddrs()
    {
      var branch := branches.GetBranch(r);
      var outBranch := out.GetBranch(r);

      AllKeysInRangeForValidRankings(branch, branch.TheRanking(), outBranch.TheRanking());
      AllKeysInRangeForDiskSubSet(branch, outBranch, outBranch.TheRanking());

      ReachableAddrsForDiskSubSet(branch, outBranch, TightRanking(branch));
      ReachableAddrsForValidRanking(branch, TightRanking(branch), branch.TheRanking());
      ReachableAddrsForValidRanking(outBranch, TightRanking(branch), outBranch.TheRanking());
    }
  }
     
//      lemma RemoveBranchWF(root: Address) 
//       requires RemoveBranch.requires(root)
//       ensures RemoveBranch(root).WF() 
//     {
//       assume false;

//     }


}