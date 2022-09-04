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

  // function BranchesBufferStack(branches: Branches, buffers: seq<Address>) : BufferStack
  //   requires branches.WF()
  //   requires (forall addr | addr in buffers :: branches.ValidBranch(addr))
  // {
  //   BufferStack(seq (|buffers|, i requires 0 <= i < |buffers| => branches.GetBranch(buffers[i]).I().I()))
  // }

  // lemma BranchesBufferStackQueryConsistent(key: Key, branches: Branches, buffers: seq<Address>, count: nat)
  //   requires count <= |buffers|
  //   requires BranchesBufferStack.requires(branches, buffers)
  //   ensures BranchesBufferStack(branches, buffers).QueryUpTo(key, count) == branches.Query(key, buffers[..count])
  // {
  //   if count > 0 {
  //     var bufferstack := BranchesBufferStack(branches, buffers);
  //     var branch := branches.GetBranch(buffers[count-1]);
  //     var msg := if branch.Query(key).Some? then branch.Query(key).value else Update(NopDelta());

  //     assert bufferstack.buffers[count-1].Query(key) == msg;
  //     assert buffers[..count-1] == DropLast(buffers[..count]);

  //     BranchesBufferStackQueryConsistent(key, branches, buffers, count-1);
  //   }
  // }

  lemma QueryCommutesWithIBufferStack(node: BetreeNode, branches: Branches, key: Key, start: nat, count: nat)
    requires IBufferStack.requires(node, branches)
    requires node.KeyInDomain(key)
    requires count <= |node.buffers|
    requires start == node.ActiveBuffersForKey(key)
    ensures count <= start ==> (IBufferStack(node, branches).QueryUpTo(key, count) == Update(NopDelta()))
    ensures start < count ==> (IBufferStack(node, branches).QueryUpTo(key, count) == branches.Query(key, node.buffers[start..count]))
  {
    ActiveBuffersForKeyConsistent(node, key, start);
    if start < count {
      var branch := branches.GetBranch(node.buffers[count-1]);
      var msg := if branch.Query(key).Some? then branch.Query(key).value else Update(NopDelta());
      assert IBufferStack(node, branches).buffers[count-1].Query(key) == msg;
      assert node.buffers[start..count-1] == DropLast(node.buffers[start..count]);
      QueryCommutesWithIBufferStack(node, branches, key, start, count-1);
    } else if 0 < count {
      QueryCommutesWithIBufferStack(node, branches, key, start, count-1);
    }
  }

  lemma QueryUpToEquivalent(a: BufferStack, b: BufferStack, key: Key, count: nat)
    requires count <= |a.buffers|
    requires count <= |b.buffers|
    requires forall i:nat | i < count :: a.buffers[i].Query(key) == b.buffers[i].Query(key)
    ensures a.QueryUpTo(key, count) == b.QueryUpTo(key, count)
  {
    if count > 0 {
      QueryUpToEquivalent(a, b, key, count-1);
    }
  }

  lemma BufferStackQueryAdditive(left: BufferStack, right: BufferStack, key: Key, count: nat)
    requires count <= |left.buffers| + |right.buffers|
    ensures 
      && var out := BufferStack(left.buffers + right.buffers);
      && (count <= |left.buffers| ==> out.QueryUpTo(key, count) == left.QueryUpTo(key, count))
      && (|left.buffers| < count ==> out.QueryUpTo(key, count) == Merge(left.Query(key), right.QueryUpTo(key, count-|left.buffers|)))
  {
    var out := BufferStack(left.buffers + right.buffers);
    if count <= |left.buffers| {
      QueryUpToEquivalent(out, left, key, count);
    } else {
      BufferStackQueryAdditive(left, right, key, count-1);
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

      var branched := receipt.lines[i].branched;
      var key := ireceipt.key;
      var node := branched.Root();
      var start := node.ActiveBuffersForKey(key);

      assert node.buffers[start..|node.buffers|] == node.buffers[start..]; //trigger
      QueryCommutesWithIBufferStack(node, branched.branches, key, start, |node.buffers|);
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
      case InternalCompactStep(path, compactStart, compactEnd, compactedBranch, targetAddr, pathAddrs) => (
          var linked := IBranchedBetree(path.Target());
          var buffers := linked.Root().buffers.buffers;
          var compactedBuffers := buffers[..compactStart] + [compactedBranch.I().I()] + buffers[compactEnd..];
          LinkedBetree.InternalCompactStep(IPath(path), BufferStack(compactedBuffers), targetAddr, pathAddrs))
      case InternalPruneBranchesStep(_) => LinkedBetree.InternalNoOpStep()
      case InternalNoOpStep() => LinkedBetree.InternalNoOpStep()
    }
  }

  lemma InternalCompactStepWF(step: Step) 
    requires step.WF()
    requires step.InternalCompactStep?
    ensures IStepDefn(step).WF()
  {
    var istep := IStepDefn(step);
    var path := step.path;
    TargetCommutesWithI(path);
    assert istep.path.Valid();

    var linked := istep.path.Target();
    var branched := path.Target();
    var start := step.compactStart;
    var end := step.compactEnd;

    var linkedBuffers := linked.Root().buffers.buffers;
    var compactedBuffers := istep.compactedBuffers.buffers;
    var delta := end - start - 1;

    var left := BufferStack(linkedBuffers[..start]);
    var left' := BufferStack(compactedBuffers[..start]);
    var middle := BufferStack(linkedBuffers[start..end]);
    var middle' := BufferStack([compactedBuffers[start]]);
    var right := BufferStack(linkedBuffers[end..]);
    var right' := BufferStack(compactedBuffers[start+1..]);

    assert left.buffers + middle.buffers == linkedBuffers[..end]; // trigger
    assert left'.buffers + middle'.buffers == compactedBuffers[..start+1]; // trigger
    assert linkedBuffers[..end] + right.buffers == linkedBuffers; // trigger
    assert compactedBuffers[..start+1] + right'.buffers == compactedBuffers; // trigger
    assert linkedBuffers[..|linkedBuffers|] == linkedBuffers; // trigger
    assert compactedBuffers[..|compactedBuffers|] == compactedBuffers; // trigger

    forall k | AnyKey(k)
      ensures linked.Root().buffers.Query(k) == istep.compactedBuffers.Query(k) 
    {
      QueryUpToEquivalent(left, left', k, start);
      assert left.Query(k) == left'.Query(k);

      QueryUpToEquivalent(right, right', k, |right.buffers|);
      assert right.Query(k) == right'.Query(k);

      var result := 
        if step.compactedBranch.Query(k).Some? 
        then step.compactedBranch.Query(k).value
        else Update(NopDelta());

      assert middle'.QueryUpTo(k, 0) == Update(NopDelta()); // trigger
      assert middle'.Query(k) == result;
      assume middle.Query(k) == result; // TODO: prove
      
      // this is our condition: 
      // && (forall key | KeyInDomain(key) && ActiveBuffersForKey(key) < compactEnd ::
      //     && var result := if compactedBranch.Query(key).Some? then compactedBranch.Query(key).value else Update(NopDelta());
      //     && branches.Query(key, buffers[compactStart..compactEnd]) == result)
      // && (forall key | !KeyInDomain(key) || ActiveBuffersForKey(key) >= compactEnd :: compactedBranch.Query(key).None?)

      BufferStackQueryAdditive(left, middle, k, end);
      BufferStackQueryAdditive(BufferStack(linkedBuffers[..end]), right, k, |linkedBuffers|);

      BufferStackQueryAdditive(left', middle', k, start+1);
      BufferStackQueryAdditive(BufferStack(compactedBuffers[..start+1]), right', k, |compactedBuffers|);
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
      case InternalCompactStep(path, compactStart, compactEnd, compactedBranch, _, _) => { InternalCompactStepWF(step); }
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

  lemma SameReachableAddrsForValidRankings (branch: LinkedBranch, r1: Ranking, r2: Ranking)
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
        SameReachableAddrsForValidRankings(branch.ChildAtIdx(i), r1, r2);
      }

      assert r1Addrs == r2Addrs;
      UnionSeqOfSetsSoundness(r1Addrs);
      UnionSeqOfSetsSoundness(r2Addrs);
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

  lemma SameReachableAddrsForDiskSubset(sub: LinkedBranch, full: LinkedBranch, ranking: Ranking)
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
        SameReachableAddrsForDiskSubset(sub.ChildAtIdx(i), full.ChildAtIdx(i), ranking);
      }

      assert subAddrs == fullAddrs;
      UnionSeqOfSetsSoundness(subAddrs);
      UnionSeqOfSetsSoundness(fullAddrs);
    }
  }

  lemma SameAllKeysInRangeForDiskSubSet(sub: LinkedBranch, full: LinkedBranch, ranking: Ranking)
    requires LinkedBranchDiskSubset(sub, full, ranking)
    requires sub.AllKeysInRangeInternal(ranking)
    ensures sub.AllKeys(ranking) == full.AllKeys(ranking)
    ensures full.AllKeysInRangeInternal(ranking)
    decreases sub.GetRank(ranking)
  {
    var node := sub.Root();
    if node.Index?  {
      forall i | 0 <= i < |node.children|
        ensures full.ChildAtIdx(i).AllKeysInRangeInternal(ranking) 
        ensures sub.ChildAtIdx(i).AllKeys(ranking) == full.ChildAtIdx(i).AllKeys(ranking)
        ensures i < |node.children|-1 ==> full.AllKeysBelowBound(i, ranking)
        ensures 0 < i ==> full.AllKeysAboveBound(i, ranking)
      {
        SameAllKeysInRangeForDiskSubSet(sub.ChildAtIdx(i), full.ChildAtIdx(i), ranking);
        if i < |node.children|-1 {
          assert sub.AllKeysBelowBound(i, ranking); // trigger
        }
        if i > 0 {
          assert sub.AllKeysAboveBound(i, ranking); // trigger
        }
      }
    }
  }

  lemma SameAllKeysInRangeForValidRankings(branch: LinkedBranch, r1: Ranking, r2: Ranking)
    requires branch.WF()
    requires branch.ValidRanking(r1)
    requires branch.ValidRanking(r2)
    requires branch.AllKeysInRangeInternal(r1)
    ensures branch.AllKeys(r1) == branch.AllKeys(r2)
    ensures branch.AllKeysInRangeInternal(r2)
    decreases branch.GetRank(r1)
  {
    var node := branch.Root();
    if node.Index? {
      forall i | 0 <= i < |node.children|
        ensures branch.ChildAtIdx(i).AllKeysInRangeInternal(r2) 
        ensures branch.ChildAtIdx(i).AllKeys(r1) == branch.ChildAtIdx(i).AllKeys(r2)
        ensures i < |node.children|-1 ==> branch.AllKeysBelowBound(i, r2)
        ensures 0 < i ==> branch.AllKeysAboveBound(i, r2)
      {
        SameAllKeysInRangeForValidRankings(branch.ChildAtIdx(i), r1, r2);
        if i < |node.children|-1 {
          assert branch.AllKeysBelowBound(i, r1); // trigger
        }
        if i > 0 {
          assert branch.AllKeysAboveBound(i, r1); // trigger
        }
      } 
    }
  }
  
  lemma AddBranchWF(branches: Branches, branch: LinkedBranch) 
    requires branches.AddBranch.requires(branch)
    ensures branches.AddBranch(branch).WF()
  {
    var out := branches.AddBranch(branch);
    assert IsSubMap(branch.diskView.entries, out.diskView.entries); 

    forall r | r in out.roots
      ensures out.GetBranch(r).Acyclic()
      ensures out.GetBranch(r).AllKeysInRange()
      ensures r != branch.root ==> (out.GetBranch(r).ReachableAddrs() == branches.GetBranch(r).ReachableAddrs())
    {
      var branch := if r == branch.root then branch else branches.GetBranch(r);
      var outBranch := out.GetBranch(r);
      
      assert outBranch.ValidRanking(TightRanking(branch)); // trigger
      SameAllKeysInRangeForValidRankings(branch, branch.TheRanking(), outBranch.TheRanking());
      SameAllKeysInRangeForDiskSubSet(branch, outBranch, outBranch.TheRanking());

      SameReachableAddrsForDiskSubset(branch, outBranch, outBranch.TheRanking());
      SameReachableAddrsForValidRankings(branch, outBranch.TheRanking(), branch.TheRanking());
    }

    var outBranch := out.GetBranch(branch.root);
    SameReachableAddrsForDiskSubset(branch, outBranch, outBranch.TheRanking());
    SameReachableAddrsForValidRankings(branch, outBranch.TheRanking(), branch.TheRanking());
    assert branch.ReachableAddrs() == outBranch.ReachableAddrs();
  }
     
  lemma RemoveBranchWF(branches: Branches, root: Address) 
    requires branches.RemoveBranch.requires(root)
    ensures branches.RemoveBranch(root).WF() 
  {
    var out := branches.RemoveBranch(root);
    var branch := branches.GetBranch(root);

    assert (forall r | r in out.roots :: out.diskView.ValidAddress(r));
    // TODO: prove this, likely need to connect Reachable Addrs to nodes in diskView
    // this may require another predicate in WF that says things in diskview only reachable
    // addrs of something have reference of it

    // && diskView.WF() // ensures all nodes are connected // uh oh
    // && (forall root | root in roots :: GetBranch(root).Acyclic()) // uh oh 
    // && (forall root | root in roots :: GetBranch(root).AllKeysInRange()) // uhoh
    // && BranchesDisjoint()
    assume false;
  }
}