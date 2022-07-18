// Copyright 2018-2021 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, and University of Washington
// SPDX-License-Identifier: BSD-2-Clause

include "LinkedBetree.i.dfy"
include "../../lib/Base/SequencesOfMaps.i.dfy"
include "../../lib/Base/Sets.i.dfy"
include "Domain.i.dfy"

module LinkedBetreeRefinement {
  import opened Options
  import Mathematics
  import opened Sequences  // Set
  import opened Maps  // Set
  import opened Sets
  import opened SequencesOfMaps
  import opened KeyType
  import opened ValueMessage
  import opened MsgHistoryMod
  import opened LSNMod
  import opened Buffers
  import GenericDisk
  import opened BoundedPivotsLib
  import opened LinkedBetreeMod
  import opened StampedMod
  import PivotBetree
  import opened DomainMod
  import opened SplitRequestMod

  type Ranking = GenericDisk.Ranking

  lemma EmptyLinkedBtreeAcyclic()
    ensures EmptyLinkedBetree().Acyclic()
  {
    assert EmptyLinkedBetree().ValidRanking(map[]);
  }

  function ILbl(lbl: TransitionLabel) : PivotBetree.TransitionLabel
  {
    match lbl
      case QueryLabel(endLsn, key, value) => PivotBetree.QueryLabel(endLsn, key, value)
      case PutLabel(puts) => PivotBetree.PutLabel(puts)
      case QueryEndLsnLabel(endLsn) => PivotBetree.QueryEndLsnLabel(endLsn)
      case FreezeAsLabel(stampedBetree) => PivotBetree.FreezeAsLabel(
        if stampedBetree.value.WF() && stampedBetree.value.Acyclic()
        then IStampedBetree(stampedBetree)
        else
          EmptyLinkedBtreeAcyclic();
          IStampedBetree(EmptyImage())  // "silly" case, since we never interpret non-(WF+Acyclic) things
      )
      case InternalLabel() => PivotBetree.InternalLabel()
  }

  lemma ChildIdxCommutesWithI(linked: LinkedBetree, idx: nat, r: Ranking)
    requires linked.WF()
    requires linked.HasRoot()
    requires linked.ValidRanking(r)
    requires linked.Root().ValidChildIndex(idx)
    requires ILinkedBetreeNode(linked, r).ValidChildIndex(idx)
    ensures ILinkedBetreeNode(linked.ChildAtIdx(idx), r) == ILinkedBetreeNode(linked, r).children[idx]
  {}

  lemma ChildIdxAcyclic(linked: LinkedBetree, idx: nat)
    requires linked.Acyclic()
    requires linked.HasRoot()
    requires linked.Root().ValidChildIndex(idx)
    ensures linked.ChildAtIdx(idx).Acyclic();
  {
    var ranking := linked.TheRanking();  // witness
    assert linked.ChildAtIdx(idx).ValidRanking(ranking);
  }

  lemma ChildKeyAcyclic(linked: LinkedBetree, key: Key)
    requires linked.Acyclic()
    requires linked.HasRoot()
    requires linked.Root().KeyInDomain(key)
    ensures linked.ChildForKey(key).Acyclic()
  {
    var ranking := linked.TheRanking();  // witness
    assert linked.ChildForKey(key).ValidRanking(ranking);
  }

  lemma ILinkedWF(linked: LinkedBetree, ranking: Ranking)
    requires linked.Acyclic()
    requires linked.ValidRanking(ranking)
    ensures ILinkedBetree(linked).WF()
    decreases linked.GetRank(ranking)
  {
    if linked.HasRoot() {
      forall idx: nat | linked.Root().ValidChildIndex(idx)
      ensures ILinkedBetree(linked).children[idx].WF()
      {
        ChildIdxAcyclic(linked, idx);
        ILinkedWF(linked.ChildAtIdx(idx), ranking);
        ChildIdxCommutesWithI(linked, idx, linked.TheRanking());
      }
      ILinkedBetreeIgnoresRanking(linked, ranking, linked.TheRanking());
    }
  }

  // wrapper
  function ILinkedBetree(linked: LinkedBetree) : (out: PivotBetree.BetreeNode)
    requires linked.Acyclic()
    ensures out.WF()
  {
    ILinkedBetreeNode(linked, linked.TheRanking())
  }

  function IChildren(linked: LinkedBetree, ranking: Ranking) : seq<PivotBetree.BetreeNode>
    requires linked.WF()
    requires linked.HasRoot()
    requires linked.ValidRanking(ranking)
    decreases linked.GetRank(ranking), 0
  {
    var numChildren := |linked.Root().children|;
    seq(numChildren, i requires 0 <= i < numChildren => ILinkedBetreeNode(linked.ChildAtIdx(i), ranking))
  }

  function ILinkedBetreeNode(linked: LinkedBetree, ranking: Ranking) : (out: PivotBetree.BetreeNode)
    requires linked.WF()
    requires linked.ValidRanking(ranking)
    ensures out.WF()
    decreases linked.GetRank(ranking), 1
  {
    if linked.root.None?
    then PivotBetree.Nil
    else
      var node := linked.Root();
      var out := PivotBetree.BetreeNode(node.buffers, node.pivotTable, IChildren(linked, ranking));
      assert out.WF() by {
        forall i:nat |
            && out.ValidChildIndex(i)
            && out.children[i].BetreeNode?
            && out.children[i].LocalStructure()
          ensures out.children[i].MyDomain() == out.DomainRoutedToChild(i) {
           if node.children[i].None? {
            assert linked.ChildAtIdx(i).root.None?;  // trigger
            assert ILinkedBetreeNode(linked.ChildAtIdx(i), ranking).Nil?;  // trigger
            assert false;
           }
           assert out.DomainRoutedToChild(i) == node.DomainRoutedToChild(i);  // trigger
         }
      }
      out
  }

  function IPath(path: Path) : (out: PivotBetree.Path)
    requires path.linked.Acyclic()
    requires path.Valid()
  {
    PivotBetree.Path(ILinkedBetree(path.linked), path.key, path.depth)
  }

  predicate StepPathRootAcyclic(step: Step) {
    match step {
      case InternalSplitStep(path, _, _, _) =>
        path.linked.Acyclic()
      case InternalFlushStep(path, _, _, _, _) =>
        path.linked.Acyclic()
      case InternalCompactStep(path, _, _, _) =>
        path.linked.Acyclic()
      case _ => true
    }
  }

  function IReceiptLine(line: QueryReceiptLine) : PivotBetree.QueryReceiptLine
    requires line.linked.Acyclic()
  {
    PivotBetree.QueryReceiptLine(
      ILinkedBetree(line.linked),
      line.result
    )
  }

  function IReceipt(receipt: QueryReceipt) : (out: PivotBetree.QueryReceipt)
    requires receipt.Valid()
  {
    PivotBetree.QueryReceipt(
      receipt.key,
      ILinkedBetree(receipt.linked),
      seq(|receipt.lines|, i requires 0<=i<|receipt.lines| => IReceiptLine(receipt.lines[i]))
    )
  }

  function IStepDefn(step: Step) : (out: PivotBetree.Step)
    requires step.WF()
    requires StepPathRootAcyclic(step)
  {
     match step {
      case QueryStep(receipt) => PivotBetree.QueryStep(IReceipt(receipt))
      case PutStep() => PivotBetree.PutStep()
      case QueryEndLsnStep() => PivotBetree.QueryEndLsnStep()
      case FreezeAsStep() => PivotBetree.FreezeAsStep()
      case InternalGrowStep(_) => PivotBetree.InternalGrowStep()
      case InternalSplitStep(path, request, newAddrs, pathAddrs) =>
        PivotBetree.InternalSplitStep(IPath(path), request)
      case InternalFlushStep(path, childIdx, _, _, _) =>
        var out := PivotBetree.InternalFlushStep(IPath(path), childIdx);
        IPathValid(path);
        TargetCommutesWithI(path);
        out
      case InternalCompactStep(path, compactedBuffers, _, _) =>
        var out := PivotBetree.InternalCompactStep(IPath(path), compactedBuffers);
        IPathValid(path);
        TargetCommutesWithI(path);
        out
    }
  }

  lemma IStepWF(step: Step)
    requires IStepDefn.requires(step)
    ensures IStepDefn(step).WF()
  {
    var istep := IStepDefn(step);
    match step {
      case QueryStep(receipt) => { IReceiptValid(receipt); }
      case PutStep() => { assert istep.WF(); }
      case QueryEndLsnStep() => { assert istep.WF(); }
      case FreezeAsStep() => { assert istep.WF(); }
      case InternalGrowStep(_) => { assert istep.WF(); }
      case InternalSplitStep(path, request, newAddrs, pathAddrs) => {
        IPathValid(step.path);
        TargetCommutesWithI(step.path);

        assert istep.path.Target().CanSplitParent(istep.request) by {
          var target := step.path.Target();
          var ichild := istep.path.Target().children[request.childIdx];
          var child := target.ChildAtIdx(request.childIdx);
          assert ILinkedBetreeNode(target, target.TheRanking()).children[request.childIdx]
            == ILinkedBetreeNode(child, target.TheRanking());  // trigger
          assert ichild.children[0] == IChildren(child, target.TheRanking())[0];  // trigger

          if step.request.SplitLeaf? {
            assert IChildren(child, target.TheRanking())[0] == PivotBetree.Nil;  // trigger
          } else {
            forall i | 0 <= i < |ichild.children| ensures ichild.children[i].BetreeNode? {
              assert ichild.children[i] == ILinkedBetreeNode(child.ChildAtIdx(i), target.TheRanking()); // trigger
            }
          }
        }
        assert istep.WF();  // case boilerplate
      }
      case InternalFlushStep(path, childIdx, _, _, _) => {
        IPathValid(step.path);
        TargetCommutesWithI(step.path);
        assert istep.WF();  // case boilerplate
      }
      case InternalCompactStep(path, compactedBuffers, _, _) => {
        IPathValid(step.path);
        TargetCommutesWithI(step.path);
        assert istep.WF();  // case boilerplate
      }
    }
  }

  function IStep(step: Step) : (out: PivotBetree.Step)
    requires step.WF()
    requires StepPathRootAcyclic(step)
    ensures out.WF()
  {
    IStepWF(step);
    IStepDefn(step)
  }

  lemma TargetCommutesWithI(path: Path)
    requires path.Valid()
    requires path.linked.Acyclic()
    ensures path.Target().Acyclic()  //prereq
    ensures IPath(path).Valid()  // prereq
    ensures IPath(path).Target() == ILinkedBetree(path.Target())
    decreases path.depth
  {
    ValidRankingAllTheWayDown(path.linked.TheRanking(), path);
    IPathValid(path);
    if 0 < path.depth {
      TargetCommutesWithI(path.Subpath());
      SubpathCommutesWithIPath(path);
    }
  }

  lemma SubpathCommutesWithIPath(path: Path)
    requires path.Valid()
    requires 0 < path.depth
    requires path.linked.Acyclic()
    ensures path.Subpath().linked.Acyclic()  // prereq
    ensures IPath(path.Subpath()) == IPath(path).Subpath()
  {
    ValidRankingAllTheWayDown(path.linked.TheRanking(), path);
    ChildKeyCommutesWithI(path.linked, path.key);
  }

  lemma ChildKeyCommutesWithI(linked: LinkedBetree, key: Key)
    requires linked.Acyclic()
    requires linked.HasRoot()
    requires linked.Root().KeyInDomain(key)
    ensures linked.ChildForKey(key).Acyclic()  // prereq
    ensures ILinkedBetree(linked.ChildForKey(key)) == ILinkedBetree(linked).Child(key)
  {
    ChildKeyAcyclic(linked, key);
    if linked.ChildForKey(key).HasRoot() {
      calc {
        PivotBetree.BetreeNode(
            linked.ChildForKey(key).Root().buffers,
            linked.ChildForKey(key).Root().pivotTable,
            IChildren(linked.ChildForKey(key), linked.ChildForKey(key).TheRanking()));
        {
          IChildrenIgnoresRanking(linked.ChildForKey(key), linked.ChildForKey(key).TheRanking(), linked.TheRanking());
        }
        PivotBetree.BetreeNode(
            linked.ChildForKey(key).Root().buffers,
            linked.ChildForKey(key).Root().pivotTable,
            IChildren(linked.ChildForKey(key), linked.TheRanking()));
        PivotBetree.BetreeNode(
            linked.Root().buffers,
            linked.Root().pivotTable,
            IChildren(linked, linked.TheRanking())).Child(key);
      }
    } else {
      calc {  // trigger
        PivotBetree.Nil;
        PivotBetree.BetreeNode(linked.Root().buffers, linked.Root().pivotTable, IChildren(linked, linked.TheRanking())).Child(key);
      }
    }
  }

  lemma IndexinessCommutesWithI(linked: LinkedBetree)
    requires linked.WF()
    requires linked.Acyclic()
    requires linked.HasRoot()
    ensures linked.Root().IsIndex() ==> ILinkedBetree(linked).IsIndex()
    ensures linked.Root().IsLeaf() ==> ILinkedBetree(linked).IsLeaf()
  {
    var iroot := ILinkedBetree(linked);
    if linked.Root().IsIndex() {
      forall i | 0 <= i < |iroot.children| ensures iroot.children[i].BetreeNode? {
        assert iroot.children[i] == IChildren(linked, linked.TheRanking())[i];  // trigger
      }
    }
    if linked.Root().IsLeaf() {
      assert iroot.children[0] == IChildren(linked, linked.TheRanking())[0];  // trigger
      assert IChildren(linked, linked.TheRanking())[0].Nil?;  // trigger
    }
  }

  lemma IPathValid(path: Path)
    requires path.Valid()
    requires path.linked.Acyclic()
    ensures IPath(path).Valid()
    decreases path.depth
  {
    if 0 < path.depth {
      ValidRankingAllTheWayDown(path.linked.TheRanking(), path);
      IPathValid(path.Subpath());
      SubpathCommutesWithIPath(path);
      IndexinessCommutesWithI(path.linked);
    }
  }

  lemma IReceiptValid(receipt: QueryReceipt) 
    requires receipt.Valid()
    ensures IReceipt(receipt).Valid()
  {
    var ireceipt := IReceipt(receipt);
    var key := receipt.key;

    forall i:nat | i < |ireceipt.lines|-1 
    ensures ireceipt.lines[i].node.KeyInDomain(key)
    {
      assert receipt.Node(i).KeyInDomain(key);  // trigger
    }

    forall i:nat | i < |ireceipt.lines| - 1 
    ensures ireceipt.ChildLinkedAt(i)
    {
      assert receipt.Node(i).KeyInDomain(key);  // trigger
      ChildKeyAcyclic(receipt.lines[i].linked, key);
      ChildKeyCommutesWithI(receipt.lines[i].linked, key);
      assert receipt.ChildLinkedAt(i);  // trigger
    }

    forall i:nat | i < |ireceipt.lines| - 1 
    ensures ireceipt.ResultLinkedAt(i)
    {
      assert receipt.ResultLinkedAt(i);  // trigger
    }
  }

  lemma IChildrenIgnoresRanking(linked: LinkedBetree, r1: Ranking, r2: Ranking)
    requires linked.WF()
    requires linked.ValidRanking(r1)
    requires linked.ValidRanking(r2)
    requires linked.HasRoot()
    ensures IChildren(linked, r1) == IChildren(linked, r2)
    decreases linked.GetRank(r1), 0
  {
    var numChildren := |linked.Root().children|;
    forall i | 0 <= i < numChildren
    ensures ILinkedBetreeNode(linked.ChildAtIdx(i), r1) == ILinkedBetreeNode(linked.ChildAtIdx(i), r2){
      ILinkedBetreeIgnoresRanking(linked.ChildAtIdx(i), r1, r2);
    }
    assert IChildren(linked, r1) == IChildren(linked, r2);
  }

  lemma ILinkedBetreeIgnoresRanking(linked: LinkedBetree, r1: Ranking, r2: Ranking)
    requires linked.WF()
    requires linked.ValidRanking(r1)
    requires linked.ValidRanking(r2)
    ensures ILinkedBetreeNode(linked, r1) == ILinkedBetreeNode(linked, r2)
    decreases linked.GetRank(r1), 1
  {
    if linked.root.None? {
      assert ILinkedBetreeNode(linked, r1) == ILinkedBetreeNode(linked, r2);
    } else {
      IChildrenIgnoresRanking(linked, r1, r2);
      assert IChildren(linked, r1) == IChildren(linked, r2);
      assert ILinkedBetreeNode(linked, r1) == ILinkedBetreeNode(linked, r2);
    }
  }

  function IStampedBetree(stampedBetree: StampedBetree) : (out: PivotBetree.StampedBetree)
    requires stampedBetree.value.WF()
    requires stampedBetree.value.Acyclic()
    ensures out.value.WF()
  {
    Stamped(ILinkedBetree(stampedBetree.value), stampedBetree.seqEnd)
  }

  function I(v: Variables) : (out: PivotBetree.Variables)
    requires v.WF()
    requires v.linked.Acyclic()
  {
    PivotBetree.Variables(v.memtable, ILinkedBetree(v.linked))
  }

  predicate RootCoversTotalDomain(linked: LinkedBetree)
    requires linked.WF()
  {
    linked.HasRoot() ==> linked.Root().MyDomain() == TotalDomain()
  }

  // Properties a StampedBetree must carry from Freeze back to Init
  predicate InvLinkedBetree(linked:LinkedBetree)
  {
    && linked.WF()
    && linked.Acyclic()
    && RootCoversTotalDomain(linked)
  }

  predicate Inv(v: Variables)
  {
    && InvLinkedBetree(v.linked)
    && v.WF() // turns out not to add anything, but someday maybe it will?
  }

  function Repr(linked: LinkedBetree) : set<Address>
  {
    linked.diskView.entries.Keys
  }

  lemma SubstitutePreservesWF(replacement: LinkedBetree, path: Path, pathAddrs: PathAddrs, newLinked: LinkedBetree)
    requires replacement.WF()
    requires path.depth == |pathAddrs|
    requires path.Valid()
    requires SeqHasUniqueElems(pathAddrs)
    requires path.CanSubstitute(replacement, pathAddrs)
    requires path.linked.diskView.IsFresh(Set(pathAddrs))
    requires replacement.diskView.IsFresh(Set(pathAddrs))
    requires newLinked == path.Substitute(replacement, pathAddrs) // "var" for ensures...
    ensures newLinked.WF()
    ensures path.linked.diskView.IsSubsetOf(newLinked.diskView)
    ensures Repr(newLinked) <= Repr(path.linked) + Repr(replacement) + Set(pathAddrs)
    ensures newLinked.HasRoot()
    ensures newLinked.Root().MyDomain() == path.linked.Root().MyDomain()
    decreases path.depth
  {
    if 0 < path.depth {
      DiskViewDiff(replacement, path.Subpath(), pathAddrs[1..]);
      SubstitutePreservesWF(replacement, path.Subpath(), pathAddrs[1..], path.Subpath().Substitute(replacement, pathAddrs[1..]));
      var subtree := path.Subpath().Substitute(replacement, pathAddrs[1..]);
      var dv := path.Substitute(replacement, pathAddrs).diskView;
      forall addr | addr in dv.entries ensures dv.NodeHasLinkedChildren(dv.entries[addr]) {
        var node := dv.entries[addr];
        if addr == pathAddrs[0] {
          forall idx:nat | node.ValidChildIndex(idx) ensures dv.ChildLinked(node, idx) {
            assert path.linked.diskView.ChildLinked(path.linked.Root(), idx);  // trigger
          }
        }
      }
    }
  }

  predicate FreshRankingExtension(dv: DiskView, r1: Ranking, r2: Ranking)
  {
    && IsSubMap(r1, r2)
    && forall k | k in r2 && k !in r1 :: k !in dv.entries
  }

  lemma DiskViewDiff(replacement: LinkedBetree, path: Path, pathAddrs: PathAddrs)
    requires replacement.WF()
    requires path.depth == |pathAddrs|
    requires path.Valid()
    requires SeqHasUniqueElems(pathAddrs)
    requires path.linked.diskView.IsSubsetOf(replacement.diskView)
    requires path.CanSubstitute(replacement, pathAddrs)
    ensures Repr(path.Substitute(replacement, pathAddrs)) == Repr(replacement) + Set(pathAddrs)
    decreases path.depth
  {
    if 0 < path.depth {
      DiskViewDiff(replacement, path.Subpath(), pathAddrs[1..]);
      assert path.Substitute(replacement, pathAddrs).diskView.entries.Keys == replacement.diskView.entries.Keys + Set(pathAddrs);
    }
  }

  lemma RankingAfterSubstitution(replacement: LinkedBetree, ranking: Ranking, path: Path, pathAddrs: PathAddrs)
  returns (newRanking: Ranking)
    requires path.CanSubstitute(replacement, pathAddrs)
    requires path.linked.Acyclic()
    requires path.linked.root.value in ranking
    requires replacement.ValidRanking(ranking)
    requires SeqHasUniqueElems(pathAddrs)
    requires Set(pathAddrs) !! ranking.Keys
    requires path.linked.diskView.IsFresh(Set(pathAddrs))
    requires replacement.diskView.IsFresh(Set(pathAddrs))
    ensures path.Substitute(replacement, pathAddrs).WF()
    ensures path.Substitute(replacement, pathAddrs).ValidRanking(newRanking)
    ensures FreshRankingExtension(path.linked.diskView, ranking, newRanking)
    ensures newRanking.Keys == ranking.Keys + Sequences.Set(pathAddrs)
    decreases path.depth
  {
    SubstitutePreservesWF(replacement, path, pathAddrs, path.Substitute(replacement, pathAddrs));
    if path.depth == 0 {
      return ranking;
    } else {
      var subtree := path.Subpath().Substitute(replacement, pathAddrs[1..]);
      ValidRankingAllTheWayDown(path.linked.TheRanking(), path);
      var interRanking := RankingAfterSubstitution(replacement, ranking, path.Subpath(), pathAddrs[1..]); // intermediate
      var newNodeAddr := pathAddrs[0];
      var oldRootRank := interRanking[path.linked.root.value];
      var subtreeRank := if subtree.root.None? then 0 else interRanking[subtree.root.value];
      var newNodeRank := oldRootRank + subtreeRank + 1; // need to exceed oldRootRank and subtreeRank
      newRanking := interRanking[newNodeAddr := newNodeRank];

      var linked' := path.Substitute(replacement, pathAddrs);
      forall addr |
        && addr in newRanking
        && addr in linked'.diskView.entries
      ensures linked'.diskView.NodeChildrenRespectsRank(newRanking, addr)
      {
        DiskViewDiff(replacement, path, pathAddrs);
        if addr == newNodeAddr {
          var node := linked'.diskView.entries[addr];
          forall childIdx:nat | node.ValidChildIndex(childIdx) && node.children[childIdx].Some?
          ensures node.children[childIdx].value in newRanking
          ensures newRanking[node.children[childIdx].value] < newRanking[addr]
          {
            var newChildren := node.children[Route(node.pivotTable, path.key) := subtree.root];
            var subtreeSibling := newChildren[childIdx];  // trigger
          }
        }
      }
    }
  }

  lemma RankingAfterInsertCompactReplacement(target: LinkedBetree, compactedBuffers: BufferStack, ranking: Ranking, replacementAddr: Address)
  returns (newRanking: Ranking)
    requires target.WF()
    requires target.ValidRanking(ranking)
    requires target.HasRoot()
    requires target.diskView.IsFresh({replacementAddr})
    requires target.Root().buffers.Equivalent(compactedBuffers)
    ensures InsertCompactReplacement(target, compactedBuffers, replacementAddr).ValidRanking(newRanking)
    ensures newRanking.Keys == ranking.Keys + {replacementAddr}
    ensures target.ValidRanking(newRanking)   // newRanking is good for both the old and the new root
  {
    var oldTargetRank := ranking[target.root.value];
    newRanking := ranking[replacementAddr := oldTargetRank];
    assert target.diskView.ValidRanking(newRanking);
  }

  lemma InsertFlushReplacementLinkedChildren(target: LinkedBetree, childIdx: nat, targetAddr: Address, targetChildAddr: Address)
    requires target.WF()
    requires target.HasRoot()
    requires target.Root().OccupiedChildIndex(childIdx)
    requires target.diskView.IsFresh({targetAddr, targetChildAddr})
    requires targetAddr != targetChildAddr
    ensures InsertFlushReplacement(target, childIdx, targetAddr, targetChildAddr).WF()
  {
    var out := InsertFlushReplacement(target, childIdx, targetAddr, targetChildAddr);
    forall addr | addr in out.diskView.entries ensures out.diskView.NodeHasLinkedChildren(out.diskView.entries[addr]) {
      var node := out.diskView.entries[addr];
      if addr == targetAddr {
        forall idx:nat | node.ValidChildIndex(idx) ensures out.diskView.ChildLinked(node, idx) {
          if idx != childIdx {
            assert target.diskView.ChildLinked(target.Root(), idx);  // trigger
          }
        }
      }
    }
  }

  lemma RankingAfterInsertFlushReplacement(target: LinkedBetree, ranking: Ranking, childIdx: nat, targetAddr: Address, targetChildAddr: Address)
  returns (newRanking: Ranking)
    requires target.WF()
    requires target.ValidRanking(ranking)
    requires target.HasRoot()
    requires target.Root().OccupiedChildIndex(childIdx)
    requires target.diskView.IsFresh({targetAddr, targetChildAddr})
    requires targetAddr != targetChildAddr
    ensures InsertFlushReplacement(target, childIdx, targetAddr, targetChildAddr).WF()
    ensures InsertFlushReplacement(target, childIdx, targetAddr, targetChildAddr).ValidRanking(newRanking)
    ensures newRanking.Keys == ranking.Keys + {targetAddr, targetChildAddr}
    ensures target.ValidRanking(newRanking)   // newRanking is good for both the old and the new root
  {
    var oldTargetRank := ranking[target.root.value];
    var oldChildRank := ranking[target.Root().children[childIdx].value];
    newRanking := ranking[targetAddr := oldTargetRank][targetChildAddr := oldChildRank];
    assert target.diskView.ValidRanking(newRanking);
    InsertFlushReplacementLinkedChildren(target, childIdx, targetAddr, targetChildAddr);
  }

  lemma ValidRankingAllTheWayDown(ranking: Ranking, path: Path)
    requires path.Valid()
    requires path.linked.ValidRanking(ranking)
    ensures 0 < path.depth ==> path.Subpath().linked.ValidRanking(ranking)
    ensures path.Target().ValidRanking(ranking)
    decreases path.depth
  {
    if 0 < path.depth {
      ValidRankingAllTheWayDown(ranking, path.Subpath());
    }
  }

  predicate RankingIsTight(dv: DiskView, ranking: Ranking) {
    ranking.Keys <= dv.entries.Keys
  }

  // Create a valid ranking that is a subset of the diskview. Note that diskview is allowed to
  // have things that are not in the diskview
  lemma BuildTightRanking(linked: LinkedBetree, ranking: Ranking) returns (tightRanking : Ranking)
    requires linked.WF()
    requires linked.ValidRanking(ranking)
    ensures RankingIsTight(linked.diskView, tightRanking)
    ensures linked.ValidRanking(tightRanking)
  {
    tightRanking := map addr | addr in linked.diskView.entries && addr in ranking :: ranking[addr];
  }

  lemma InsertGrowReplacementNewRanking(linked: LinkedBetree, oldRanking: Ranking, newRootAddr: Address) returns (newRanking: Ranking)
    requires linked.WF()
    requires RootCoversTotalDomain(linked)
    requires linked.ValidRanking(oldRanking)
    requires RankingIsTight(linked.diskView, oldRanking)
    requires linked.diskView.IsFresh({newRootAddr})
    ensures InsertGrowReplacement(linked, newRootAddr).BuildTightTree().WF()
    ensures InsertGrowReplacement(linked, newRootAddr).BuildTightTree().ValidRanking(newRanking)
    ensures newRanking.Keys == oldRanking.Keys + {newRootAddr}
    ensures IsSubMap(oldRanking, newRanking);
  {
    if linked.HasRoot() {
      var oldRootRank := oldRanking[linked.root.value];
      newRanking := oldRanking[newRootAddr := oldRootRank+1];
    } else {
      var newRootRank := if |oldRanking.Values| == 0 then 1 else SetMax(oldRanking.Values) + 1;
      newRanking := oldRanking[newRootAddr := newRootRank];
    }
    var newRoot := InsertGrowReplacement(linked, newRootAddr);
    BuildTightPreservesWF(newRoot, newRanking);
  }

  lemma InvNextInternalGrowStep(v: Variables, v': Variables, lbl: TransitionLabel, step: Step)
    requires Inv(v)
    requires NextStep(v, v', lbl, step)
    requires step.InternalGrowStep?
    ensures v'.linked.Acyclic()
  {
    var oldRanking := BuildTightRanking(v.linked, v.linked.TheRanking());
    var newRanking := InsertGrowReplacementNewRanking(v.linked, oldRanking, step.newRootAddr);  // witness
  }

  lemma InvNextInternalCompactStep(v: Variables, v': Variables, lbl: TransitionLabel, step: Step)
    requires Inv(v)
    requires NextStep(v, v', lbl, step)
    requires step.InternalCompactStep?
    requires v.linked.diskView.IsFresh(Set(step.pathAddrs))
    ensures v'.linked.Acyclic()
  {
    var oldRanking := BuildTightRanking(v.linked, v.linked.TheRanking());
    ValidRankingAllTheWayDown(oldRanking, step.path);
    var replacement := InsertCompactReplacement(step.path.Target(), step.compactedBuffers, step.targetAddr);
    var rankingAfterReplacement := RankingAfterInsertCompactReplacement(step.path.Target(), step.compactedBuffers, oldRanking, step.targetAddr);
    var newRanking := RankingAfterSubstitution(replacement, rankingAfterReplacement, step.path, step.pathAddrs);
    var linkedAfterSubstitution := step.path.Substitute(replacement, step.pathAddrs);
    BuildTightMaintainsRankingValidity(linkedAfterSubstitution, newRanking);
    BuildTightPreservesWF(linkedAfterSubstitution, newRanking);
  }

  lemma InvNextInternalFlushStep(v: Variables, v': Variables, lbl: TransitionLabel, step: Step)
    requires Inv(v)
    requires NextStep(v, v', lbl, step)
    requires step.InternalFlushStep?
    ensures v'.linked.Acyclic()
  {
    var oldRanking := BuildTightRanking(v.linked, v.linked.TheRanking());
    ValidRankingAllTheWayDown(oldRanking, step.path);
    var replacement := InsertFlushReplacement(step.path.Target(), step.childIdx, step.targetAddr, step.targetChildAddr);
    var rankingAfterReplacement := RankingAfterInsertFlushReplacement(step.path.Target(), oldRanking, step.childIdx, step.targetAddr, step.targetChildAddr);
    var newRanking := RankingAfterSubstitution(replacement, rankingAfterReplacement, step.path, step.pathAddrs);
    var linkedAfterSubstitution := step.path.Substitute(replacement, step.pathAddrs);
    BuildTightMaintainsRankingValidity(linkedAfterSubstitution, newRanking);
    BuildTightPreservesWF(linkedAfterSubstitution, newRanking);
  }

  lemma RankingAfterSplitReplacement(target: LinkedBetree, ranking: Ranking, request: SplitRequest, newAddrs: SplitAddrs)
  returns (newRanking: Ranking)
    requires target.WF()
    requires target.ValidRanking(ranking)
    requires target.HasRoot()
    requires target.diskView.IsFresh(newAddrs.Repr())
    requires newAddrs.HasUniqueElems()
    requires target.CanSplitParent(request)
    ensures target.SplitParent(request, newAddrs).WF()
    ensures target.SplitParent(request, newAddrs).ValidRanking(newRanking)
    ensures newRanking.Keys == ranking.Keys + newAddrs.Repr()
    ensures target.ValidRanking(newRanking)   // newRanking is good for both the old and the new root
  {
    var oldTargetRank := ranking[target.root.value];
    var oldChildRank := ranking[target.Root().children[request.childIdx].value];
    newRanking := ranking[newAddrs.left := oldChildRank][newAddrs.right := oldChildRank][newAddrs.parent := oldTargetRank];
    assert target.diskView.ValidRanking(newRanking);
    target.SplitParentCanSubstitute(request, newAddrs);  // split target preserves WF
    var target' := target.SplitParent(request, newAddrs);
    forall addr | && addr in newRanking && addr in target'.diskView.entries
      ensures target'.diskView.NodeChildrenRespectsRank(newRanking, addr)
    {
      if addr == newAddrs.parent {
        var node := target'.diskView.entries[addr];
        forall childIdx:nat | node.ValidChildIndex(childIdx) && node.children[childIdx].Some?
          ensures node.children[childIdx].value in newRanking  // ranking is closed
          ensures newRanking[node.children[childIdx].value] < newRanking[addr]  // decreases
        {
          if request.childIdx < childIdx {
            assert target.Root().children[childIdx-1].value in newRanking;
            assert node.children[childIdx].value in newRanking;
            assert newRanking[node.children[childIdx].value] < newRanking[addr];
          }
        }
        assert target'.diskView.NodeChildrenRespectsRank(newRanking, addr);
      } else if addr == newAddrs.left {
        assert target'.diskView.NodeChildrenRespectsRank(newRanking, addr);
      } else if addr == newAddrs.right {
        assert target'.diskView.NodeChildrenRespectsRank(newRanking, addr);
      } else {
        assert target'.diskView.NodeChildrenRespectsRank(newRanking, addr);
      }
    }
    assert target.SplitParent(request, newAddrs).ValidRanking(newRanking);
  }

  lemma InvNextInternalSplitStep(v: Variables, v': Variables, lbl: TransitionLabel, step: Step)
    requires Inv(v)
    requires NextStep(v, v', lbl, step)
    requires step.InternalSplitStep?
    ensures Inv(v')
  {
    var oldRanking := BuildTightRanking(v.linked, v.linked.TheRanking());
    var replacement := step.path.Target().SplitParent(step.request, step.newAddrs);
    ValidRankingAllTheWayDown(oldRanking, step.path);
    var rankingAfterReplacement := RankingAfterSplitReplacement(step.path.Target(), oldRanking, step.request, step.newAddrs);
    var linkedAfterSubstitution := step.path.Substitute(replacement, step.pathAddrs);
    var newRanking := RankingAfterSubstitution(replacement, rankingAfterReplacement, step.path, step.pathAddrs);
    BuildTightPreservesWF(linkedAfterSubstitution, newRanking);
    BuildTightMaintainsRankingValidity(linkedAfterSubstitution, newRanking);
  }

  lemma ReachableAddrIgnoresRanking(linked: LinkedBetree, r1: Ranking, r2: Ranking)
    requires linked.WF()
    requires linked.ValidRanking(r1)
    requires linked.ValidRanking(r2)
    ensures linked.ReachableAddrsUsingRanking(r1) == linked.ReachableAddrsUsingRanking(r2)
    decreases linked.GetRank(r1)
  {
    if linked.HasRoot() {
      forall i | 0 <= i < |linked.Root().children|
      ensures linked.ChildAtIdx(i).ReachableAddrsUsingRanking(r1) == linked.ChildAtIdx(i).ReachableAddrsUsingRanking(r2)
      {
        ReachableAddrIgnoresRanking(linked.ChildAtIdx(i), r1, r2);
      }
      var numChildren := |linked.Root().children|;
      var children1 := seq(numChildren, i requires 0 <= i < numChildren => linked.ChildAtIdx(i).ReachableAddrsUsingRanking(r1));
      var children2 := seq(numChildren, i requires 0 <= i < numChildren => linked.ChildAtIdx(i).ReachableAddrsUsingRanking(r2));
      assert children1 == children2;  // trigger
    }
  }

  lemma BuildTightMaintainsRankingValidity(linked: LinkedBetree, ranking: Ranking)
    requires linked.WF()
    requires linked.ValidRanking(ranking)
    ensures linked.BuildTightTree().WF()
    ensures linked.BuildTightTree().ValidRanking(ranking)
    decreases linked.GetRank(ranking)
  {
    BuildTightPreservesWF(linked, ranking);
  }

  lemma DiskSubsetImpliesIdenticalInterpretationsWithRanking(small: LinkedBetree, big: LinkedBetree, ranking: Ranking)
    requires small.WF() && big.WF()
    requires small.ValidRanking(ranking)
    requires big.ValidRanking(ranking)
    requires small.root == big.root
    requires small.diskView.IsSubsetOf(big.diskView)
    ensures ILinkedBetreeNode(small, ranking) == ILinkedBetreeNode(big, ranking)
    decreases small.GetRank(ranking)
  {
    if small.root.Some? {
      forall i | 0 <= i < |small.Root().children|
      ensures ILinkedBetreeNode(small.ChildAtIdx(i), ranking) == ILinkedBetreeNode(big.ChildAtIdx(i), ranking)
      {
        DiskSubsetImpliesIdenticalInterpretationsWithRanking(small.ChildAtIdx(i), big.ChildAtIdx(i), ranking);
      }
      assert ILinkedBetreeNode(small, ranking) == ILinkedBetreeNode(big, ranking); // trigger
    }
  }

  lemma DiskSubsetImpliesIdenticalInterpretations(small: LinkedBetree, big: LinkedBetree)
    requires small.WF() && big.WF()
    requires small.root == big.root
    requires small.diskView.IsSubsetOf(big.diskView)
    requires big.Acyclic()
    ensures small.Acyclic()
    ensures ILinkedBetree(small) == ILinkedBetree(big)
  {
    assert small.ValidRanking(big.TheRanking());  // trigger
    ILinkedBetreeIgnoresRanking(small, small.TheRanking(), big.TheRanking());
    DiskSubsetImpliesIdenticalInterpretationsWithRanking(small, big, big.TheRanking());
  }

  lemma DiskSubsetImpliesRankingValidity(small: LinkedBetree, big: LinkedBetree, ranking: Ranking)
    requires small.WF() && big.WF()
    requires big.ValidRanking(ranking)
    requires small.root == big.root
    requires small.diskView.IsSubsetOf(big.diskView)
    ensures small.ValidRanking(ranking)
    decreases small.GetRank(ranking)
  {}

  lemma BuildTightPreservesInterpretation(linked: LinkedBetree)
    requires linked.Acyclic()
    ensures linked.BuildTightTree().WF()  // prereq
    ensures linked.BuildTightTree().ValidRanking(linked.TheRanking())  // prereq
    ensures ILinkedBetree(linked) == ILinkedBetree(linked.BuildTightTree())
  {
    var ranking := linked.TheRanking();
    BuildTightPreservesWF(linked, ranking);
    BuildTightMaintainsRankingValidity(linked, ranking);
    DiskSubsetImpliesIdenticalInterpretationsWithRanking(linked.BuildTightTree(), linked, ranking);
    ILinkedBetreeIgnoresRanking(linked.BuildTightTree(), ranking, linked.BuildTightTree().TheRanking());
  }

  lemma BuildTightPreservesChildInterpretation(linked: LinkedBetree, idx: nat, ranking: Ranking)
    requires linked.WF()
    requires linked.ValidRanking(ranking)
    requires linked.HasRoot()
    requires linked.Root().ValidChildIndex(idx)
    ensures linked.BuildTightTree().WF()  // prereq
    ensures linked.BuildTightTree().Root().ValidChildIndex(idx)  // prereq
    ensures ILinkedBetreeNode(linked.ChildAtIdx(idx), ranking) == ILinkedBetreeNode(linked.BuildTightTree().ChildAtIdx(idx), ranking)
  {
    BuildTightPreservesWF(linked, ranking);
    calc {
      ILinkedBetreeNode(linked.ChildAtIdx(idx), ranking);
      ILinkedBetreeNode(linked, ranking).children[idx];
        { DiskSubsetImpliesIdenticalInterpretationsWithRanking(linked.BuildTightTree(), linked, ranking); }
      ILinkedBetreeNode(linked.BuildTightTree(), ranking).children[idx];
      ILinkedBetreeNode(linked.BuildTightTree().ChildAtIdx(idx), ranking);
    }
  }

  lemma ReachableAddrRankingValidity(linked: LinkedBetree, ranking: Ranking, addr: Address)
    requires linked.WF()
    requires linked.ValidRanking(ranking)
    requires addr in linked.ReachableAddrsUsingRanking(ranking)
    ensures LinkedBetree(Pointer.Some(addr), linked.diskView).ValidRanking(ranking)
    decreases linked.GetRank(ranking)
  {
     if addr != linked.root.value {  // otherwise addr points to linked and it's trivial
      var numChildren := |linked.Root().children|;
      var subTreeAddrs := seq(numChildren, i requires 0 <= i < numChildren => linked.ChildAtIdx(i).ReachableAddrsUsingRanking(ranking));
      assert addr in Sets.UnionSeqOfSets(subTreeAddrs);
      Sets.UnionSeqOfSetsSoundness(subTreeAddrs);
      var k :| 0 <= k < numChildren && addr in subTreeAddrs[k];
      ReachableAddrRankingValidity(linked.ChildAtIdx(k), ranking, addr);
    }
  }

  // linked's children are always in the reachable set
  lemma ChildrenAreReachable(linked: LinkedBetree, ranking: Ranking)
    requires linked.WF()
    requires linked.ValidRanking(ranking)
    requires linked.HasRoot()
    ensures
      forall i | 0 <= i < |linked.Root().children| && linked.Root().children[i].Some? ::
        linked.ChildAtIdx(i).root.value in linked.ReachableAddrsUsingRanking(ranking)
  {
    var numChildren := |linked.Root().children|;
    var subTreeAddrs := seq(numChildren, i requires 0 <= i < numChildren => linked.ChildAtIdx(i).ReachableAddrsUsingRanking(ranking));
    forall i | 0 <= i < numChildren && linked.Root().children[i].Some?
    ensures linked.ChildAtIdx(i).root.value in linked.ReachableAddrsUsingRanking(ranking)
    {
      var childAddr := linked.ChildAtIdx(i).root.value;
      assert childAddr in subTreeAddrs[i];
    }
  }

  // For any address in the reachable set, the children of the node at that location
  // are also in the reacheable set
  lemma ReachableAddrClosed(linked: LinkedBetree, ranking: Ranking, addr: Address)
    requires linked.WF()
    requires linked.ValidRanking(ranking)
    requires linked.HasRoot()
    requires addr in linked.ReachableAddrsUsingRanking(ranking)
    ensures
      var node := linked.diskView.entries[addr];
      forall i | 0 <= i < |node.children| && node.children[i].Some? ::
        node.children[i].value in linked.ReachableAddrsUsingRanking(ranking)
    decreases linked.GetRank(ranking)
  {
    if addr == linked.root.value {
      ChildrenAreReachable(linked, ranking);
    } else {
      var numChildren := |linked.Root().children|;
      var subTreeAddrs := seq(numChildren, i requires 0 <= i < numChildren => linked.ChildAtIdx(i).ReachableAddrsUsingRanking(ranking));
      assert addr in Sets.UnionSeqOfSets(subTreeAddrs);
      Sets.UnionSeqOfSetsSoundness(subTreeAddrs);
      var k :| 0 <= k < numChildren && addr in subTreeAddrs[k];
      ReachableAddrClosed(linked.ChildAtIdx(k), ranking, addr);
    }
  }

  lemma BuildTightPreservesWF(linked: LinkedBetree, ranking: Ranking)
    requires linked.WF()
    requires linked.ValidRanking(ranking)
    ensures linked.BuildTightTree().WF()
    decreases linked.GetRank(ranking)
  {
    forall addr | addr in linked.BuildTightTree().diskView.entries
    ensures linked.BuildTightTree().diskView.NodeHasNondanglingChildPtrs(linked.BuildTightTree().diskView.entries[addr])
    {
      ReachableAddrClosed(linked, linked.TheRanking(), addr);
    }
  }

  lemma InvNext(v: Variables, v': Variables, lbl: TransitionLabel)
    requires Inv(v)
    requires Next(v, v', lbl)
    ensures Inv(v')
  {
    var step: Step :| NextStep(v, v', lbl, step);
    match step {
      case QueryStep(receipt) => {
        assert Inv(v');
      }
      case PutStep() => {
        assert Inv(v');
      }
      case QueryEndLsnStep() => {
        assert Inv(v');
      }
      case FreezeAsStep() => {
        assert Inv(v');
      }
      case InternalGrowStep(_) => {
        InvNextInternalGrowStep(v, v', lbl, step);
        assert Inv(v');
      }
      case InternalSplitStep(_, _, _, _) => {
        InvNextInternalSplitStep(v, v', lbl, step);
      }
      case InternalFlushStep(_, _, _, _, _) => {
        InvNextInternalFlushStep(v, v', lbl, step);
      }
      case InternalCompactStep(_, _, _, _) => {
        InvNextInternalCompactStep(v, v', lbl, step);
      }
    }
  }

  lemma FreshEntryToDiskDoesNotChangeInterpretation(linked: LinkedBetree, linked': LinkedBetree, ranking: Ranking, newAddr: Address, newVal: BetreeNode)
    requires linked.WF() && linked'.WF()
    requires linked.ValidRanking(ranking)
    requires linked'.ValidRanking(ranking)
    requires linked.diskView.IsFresh({newAddr})
    requires linked'.diskView == linked.diskView.ModifyDisk(newAddr, newVal)
    ensures ILinkedBetreeNode(linked, ranking)
      == ILinkedBetreeNode(LinkedBetree(linked.root, linked'.diskView), ranking)
    decreases linked.GetRank(ranking)
  {
    if linked.root.Some? {
      var numChildren := |linked.Root().children|;
      forall i | 0 <= i < numChildren
      ensures  ILinkedBetreeNode(linked.ChildAtIdx(i), ranking)
          == ILinkedBetreeNode(LinkedBetree(linked.ChildAtIdx(i).root, linked'.diskView), ranking)
      {
        FreshEntryToDiskDoesNotChangeInterpretation(linked.ChildAtIdx(i), linked', ranking, newAddr, newVal);
      }
    assert ILinkedBetreeNode(linked, ranking)
      == ILinkedBetreeNode(LinkedBetree(linked.root, linked'.diskView), ranking);  // trigger
    }
  }

  lemma InitRefines(v: Variables, stampedBetree: StampedBetree)
    requires Init(v, stampedBetree)
    requires InvLinkedBetree(stampedBetree.value)
    ensures Inv(v)
    ensures PivotBetree.Init(I(v), IStampedBetree(stampedBetree))
  {
    ILinkedWF(v.linked, v.linked.TheRanking());
  }


  lemma InternalGrowStepRefines(v: Variables, v': Variables, lbl: TransitionLabel, step: Step)
    requires Inv(v)
    requires v.linked.Acyclic()
    requires NextStep(v, v', lbl, step)
    requires step.InternalGrowStep?
    ensures Inv(v')  // prereq
    ensures PivotBetree.NextStep(I(v), I(v'), ILbl(lbl), IStep(step))
  {
    InvNext(v, v', lbl);
    var tr := BuildTightRanking(v.linked, v.linked.TheRanking());
    var growReplacementRanking := InsertGrowReplacementNewRanking(v.linked, tr, step.newRootAddr);
    var r' := v'.linked.TheRanking();
    calc {
      ILinkedBetree(v'.linked).children[0];
      ILinkedBetreeNode(v'.linked, r').children[0];
      ILinkedBetreeNode(v'.linked.ChildAtIdx(0), r');
      {
        ILinkedBetreeIgnoresRanking(v'.linked.ChildAtIdx(0), growReplacementRanking, r');
      }
      ILinkedBetreeNode(
        InsertGrowReplacement(v.linked, step.newRootAddr).BuildTightTree().ChildAtIdx(0),
        growReplacementRanking);
        {
          BuildTightPreservesChildInterpretation(InsertGrowReplacement(v.linked, step.newRootAddr), 0, growReplacementRanking);
        }
      ILinkedBetreeNode(InsertGrowReplacement(v.linked, step.newRootAddr).ChildAtIdx(0), growReplacementRanking);
        {
          FreshEntryToDiskDoesNotChangeInterpretation(
            v.linked,
            InsertGrowReplacement(v.linked, step.newRootAddr),
            growReplacementRanking,
            step.newRootAddr,
            BetreeNode(BufferStack([]), TotalPivotTable(), [v.linked.root])
          );
        }
      ILinkedBetreeNode(v.linked, growReplacementRanking);
      {
        ILinkedBetreeIgnoresRanking(v.linked, v.linked.TheRanking(), growReplacementRanking);
      }
      ILinkedBetree(v.linked);
    }
    assert I(v').root.children == [I(v).root];
  }

  // Theorem: Substitute does not change children nodes that is not on the route
  // idx is the child index not on the path of substitution
  // ranking is the new ranking after substitution
  lemma SubstituteNonModifiedChildren(path: Path, replacement: LinkedBetree, pathAddrs: PathAddrs, idx: nat, ranking: Ranking)
    requires path.Valid()
    requires path.linked.Acyclic()
    requires path.CanSubstitute(replacement, pathAddrs)
    requires path.Substitute(replacement, pathAddrs).WF()
    requires path.Substitute(replacement, pathAddrs).ValidRanking(ranking)
    requires path.Substitute(replacement, pathAddrs).HasRoot()
    requires path.linked.diskView.IsFresh(Set(pathAddrs))
    requires 0 < path.depth
    requires 0 <= idx < |path.linked.Root().children|
    requires idx != Route(path.linked.Root().pivotTable, path.key)  // idx is the child index not on the path of substitution
    requires path.linked.diskView.IsSubsetOf(path.Substitute(replacement, pathAddrs).diskView)
    ensures path.linked.ChildAtIdx(idx).Acyclic()  //prereq to ILinkedBetree(path.linked.ChildAtIdx(idx)
    ensures |path.Substitute(replacement, pathAddrs).Root().children| == |path.linked.Root().children|
    ensures ILinkedBetreeNode(path.Substitute(replacement, pathAddrs).ChildAtIdx(idx), ranking)
                  == ILinkedBetree(path.linked.ChildAtIdx(idx));
  {
    ChildIdxAcyclic(path.linked, idx);
    var node := path.linked.Root();
    var subtree := path.Subpath().Substitute(replacement, pathAddrs[1..]);
    var newChildren := node.children[Route(node.pivotTable, path.key) := subtree.root];
    var newNode := BetreeNode(node.buffers, node.pivotTable, newChildren);
    var newDiskView := subtree.diskView.ModifyDisk(pathAddrs[0], newNode);
    assert path.Substitute(replacement, pathAddrs).diskView == newDiskView;  // sanity check
    calc {
      ILinkedBetreeNode(path.Substitute(replacement, pathAddrs).ChildAtIdx(idx), ranking);
      ILinkedBetreeNode(LinkedBetree(node.children[idx], newDiskView), ranking);
        {
          DiskSubsetImpliesRankingValidity(path.linked.ChildAtIdx(idx), LinkedBetree(node.children[idx], newDiskView), ranking);
          DiskSubsetImpliesIdenticalInterpretationsWithRanking(path.linked.ChildAtIdx(idx), LinkedBetree(node.children[idx], newDiskView), ranking);
        }
      ILinkedBetreeNode(LinkedBetree(node.children[idx], path.linked.diskView), ranking);
        { ILinkedBetreeIgnoresRanking(path.linked.ChildAtIdx(idx), ranking, path.linked.ChildAtIdx(idx).TheRanking()); }
      ILinkedBetree(path.linked.ChildAtIdx(idx));
    }
  }

  lemma SubstituteCommutesWithI(replacement: LinkedBetree, replacementRanking: Ranking, path: Path, pathAddrs: PathAddrs)
    requires path.Valid()
    requires path.linked.WF()
    requires path.linked.ValidRanking(replacementRanking)
    requires path.CanSubstitute(replacement, pathAddrs)
    requires replacement.WF()
    requires replacement.ValidRanking(replacementRanking);
    requires path.linked.root.value in replacementRanking
    requires SeqHasUniqueElems(pathAddrs)
    requires Set(pathAddrs) !! replacementRanking.Keys
    requires path.linked.diskView.IsFresh(Set(pathAddrs))
    requires replacement.diskView.IsFresh(Set(pathAddrs))
    requires path.linked.diskView.IsSubsetOf(path.Substitute(replacement, pathAddrs).diskView)
    ensures path.Substitute(replacement, pathAddrs).Acyclic()  // prereq to ILinkedBetree
    ensures IPath(path).Valid()  // prereq to IPath(path).Substitute
    ensures IPath(path).ValidReplacement(ILinkedBetree(replacement))
    ensures ILinkedBetree(path.Substitute(replacement, pathAddrs))
        == IPath(path).Substitute(ILinkedBetree(replacement))
    decreases path.depth
  {
    IPathValid(path);
    if 0 < path.depth {
      var rankingAfterSubst := RankingAfterSubstitution(replacement, replacementRanking, path, pathAddrs);
      ILinkedBetreeIgnoresRanking(path.Substitute(replacement, pathAddrs), path.Substitute(replacement, pathAddrs).TheRanking(), rankingAfterSubst);
      TargetCommutesWithI(path);  // Look down into target to discover MyDomain()s match in I-land
      assert |ILinkedBetree(path.Substitute(replacement, pathAddrs)).children|
        == |IPath(path).Substitute(ILinkedBetree(replacement)).children|;  // need to trigger this

      forall i | 0 <= i < |ILinkedBetree(path.Substitute(replacement, pathAddrs)).children|
      ensures ILinkedBetree(path.Substitute(replacement, pathAddrs)).children[i]
          == IPath(path).Substitute(ILinkedBetree(replacement)).children[i]
      {
        if i == Route(path.linked.Root().pivotTable, path.key) {
          ChildIdxAcyclic(path.Substitute(replacement, pathAddrs), i);
          ChildIdxCommutesWithI(path.Substitute(replacement, pathAddrs), i, path.Substitute(replacement, pathAddrs).TheRanking());
          ILinkedBetreeIgnoresRanking(
          path.Substitute(replacement, pathAddrs).ChildAtIdx(i),
          path.Substitute(replacement, pathAddrs).TheRanking(),
          path.Substitute(replacement, pathAddrs).ChildAtIdx(i).TheRanking());
          SubstitutePreservesWF(replacement, path.Subpath(), pathAddrs[1..], path.Subpath().Substitute(replacement, pathAddrs[1..]));
          ValidRankingAllTheWayDown(path.linked.TheRanking(), path);
          var big := LinkedBetree(path.Subpath().Substitute(replacement, pathAddrs[1..]).root, path.Substitute(replacement, pathAddrs).diskView);
          var small := LinkedBetree(path.Subpath().Substitute(replacement, pathAddrs[1..]).root, path.Subpath().Substitute(replacement, pathAddrs[1..]).diskView);
          SubstitutePreservesWF(replacement, path.Subpath(), pathAddrs[1..], path.Subpath().Substitute(replacement, pathAddrs[1..]));
          DiskViewDiff(replacement, path, pathAddrs);
          DiskViewDiff(replacement, path.Subpath(), pathAddrs[1..]);
          DiskSubsetImpliesRankingValidity(small, big, big.TheRanking());
          DiskSubsetImpliesIdenticalInterpretationsWithRanking(small, big, big.TheRanking());
          ILinkedBetreeIgnoresRanking(small, small.TheRanking(), big.TheRanking());
          SubstituteCommutesWithI(replacement, replacementRanking, path.Subpath(), pathAddrs[1..]);
          SubpathCommutesWithIPath(path);
        } else {
          var r := path.Substitute(replacement, pathAddrs).TheRanking();
          SubstituteNonModifiedChildren(path, replacement, pathAddrs, i, r);
          ILinkedBetreeIgnoresRanking(path.linked.ChildAtIdx(i), path.linked.ChildAtIdx(i).TheRanking(), path.linked.TheRanking());
          ChildIdxCommutesWithI(path.linked, i, path.linked.TheRanking());
        }
      }
    }
  }

  // Generate a ranking for the Compaction replacement LinkedBetree
  lemma CompactionReplacementRanking(target: LinkedBetree, targetRanking: Ranking, compactedBuffers: BufferStack, replacementAddr: Address)
  returns (replacementRanking: Ranking)
    requires target.WF()
    requires target.ValidRanking(targetRanking)
    requires target.HasRoot()
    requires target.Root().buffers.Equivalent(compactedBuffers)
    requires replacementAddr !in targetRanking
    requires target.diskView.IsFresh({replacementAddr})
    ensures InsertCompactReplacement(target, compactedBuffers, replacementAddr).ValidRanking(replacementRanking)
    ensures InsertCompactReplacement(target, compactedBuffers, replacementAddr).Acyclic()
    ensures replacementRanking.Keys == targetRanking.Keys + {replacementAddr}
    ensures IsSubMap(targetRanking, replacementRanking)
    ensures target.ValidRanking(replacementRanking)
  {
    var targetRank := targetRanking[target.root.value];
    replacementRanking := targetRanking[replacementAddr := targetRank];
    assert InsertCompactReplacement(target, compactedBuffers, replacementAddr).ValidRanking(replacementRanking);  // trigger
    assert target.ValidRanking(replacementRanking);
  }

  lemma CompactionCommutesWithI(target: LinkedBetree, targetRanking: Ranking, compactedBuffers: BufferStack, replacementAddr: Address)
    requires target.WF()
    requires target.ValidRanking(targetRanking)
    requires target.HasRoot()
    requires target.Root().buffers.Equivalent(compactedBuffers)
    requires replacementAddr !in targetRanking
    requires target.diskView.IsFresh({replacementAddr})
    ensures InsertCompactReplacement(target, compactedBuffers, replacementAddr).Acyclic()  // prereq
    ensures ILinkedBetree(InsertCompactReplacement(target, compactedBuffers, replacementAddr))
      == PivotBetree.CompactedNode(ILinkedBetree(target), compactedBuffers);
  {
    var r := CompactionReplacementRanking(target, targetRanking, compactedBuffers, replacementAddr);
    var replacement := InsertCompactReplacement(target, compactedBuffers, replacementAddr);

    // need to trigger this
    assert |ILinkedBetree(replacement).children|
      == |PivotBetree.CompactedNode(ILinkedBetree(target), compactedBuffers).children|;

    forall i | 0 <= i < |ILinkedBetree(replacement).children|
    ensures ILinkedBetree(replacement).children[i] == PivotBetree.CompactedNode(ILinkedBetree(target), compactedBuffers).children[i]
    {
      var root := target.Root();
      var newRoot := BetreeNode(compactedBuffers, root.pivotTable, root.children);
      var newDiskView := target.diskView.ModifyDisk(replacementAddr, newRoot);
      calc{
        ILinkedBetree(replacement).children[i];
        ILinkedBetreeNode(replacement, replacement.TheRanking()).children[i];
        ILinkedBetreeNode(LinkedBetree(target.Root().children[i], newDiskView), replacement.TheRanking());
          {
            var small := target.ChildAtIdx(i);
            var big := LinkedBetree(target.Root().children[i], newDiskView);
            DiskSubsetImpliesIdenticalInterpretationsWithRanking(small, big, replacement.TheRanking());
          }
        ILinkedBetreeNode(target.ChildAtIdx(i), replacement.TheRanking());
          { ILinkedBetreeIgnoresRanking(target.ChildAtIdx(i), replacement.TheRanking(), r); }
        ILinkedBetreeNode(target, r).children[i];
          { ILinkedBetreeIgnoresRanking(target, target.TheRanking(), r); }
        ILinkedBetree(target).children[i];
        PivotBetree.CompactedNode(ILinkedBetree(target), compactedBuffers).children[i];
      }
    }
  }

  // If path root is a subdisk of replacement, and pathAddrs are fresh, then path root
  // must be a subdisk of the output of Substitute
  lemma FreshSubstitutionImpliesSubdisk(path: Path, replacement: LinkedBetree, pathAddrs: PathAddrs)
    requires path.CanSubstitute(replacement, pathAddrs)
    requires path.linked.diskView.IsSubsetOf(replacement.diskView)
    requires replacement.diskView.IsFresh(Set(pathAddrs))
    ensures path.linked.diskView.IsSubsetOf(path.Substitute(replacement, pathAddrs).diskView)
    decreases path.depth
  {
    if 0 < path.depth {
      FreshSubstitutionImpliesSubdisk(path.Subpath(), replacement, pathAddrs[1..]);
    }
  }

  lemma InternalCompactStepRefines(v: Variables, v': Variables, lbl: TransitionLabel, step: Step)
    requires Inv(v)
    requires v.linked.Acyclic()
    requires NextStep(v, v', lbl, step)
    requires step.InternalCompactStep?
    ensures Inv(v')  // prereq
    ensures PivotBetree.NextStep(I(v), I(v'), ILbl(lbl), IStep(step))
  {
    InvNext(v, v', lbl);
    var istep := IStep(step);
    var replacement := InsertCompactReplacement(step.path.Target(), step.compactedBuffers, step.targetAddr);
    var tightRootRanking := BuildTightRanking(step.path.linked, step.path.linked.TheRanking());
    ValidRankingAllTheWayDown(tightRootRanking, step.path);
    var replacementRanking := CompactionReplacementRanking(step.path.Target(), tightRootRanking, step.compactedBuffers, step.targetAddr);
    calc {
      ILinkedBetree(step.path.Substitute(replacement, step.pathAddrs).BuildTightTree());
        { BuildTightPreservesInterpretation(step.path.Substitute(replacement, step.pathAddrs)); }
      ILinkedBetree(step.path.Substitute(replacement, step.pathAddrs));
        {
          FreshSubstitutionImpliesSubdisk(step.path, replacement, step.pathAddrs);
          SubstituteCommutesWithI(replacement, replacementRanking, step.path, step.pathAddrs);
        }
      istep.path.Substitute(ILinkedBetree(replacement));
        { CompactionCommutesWithI(step.path.Target(), tightRootRanking, step.compactedBuffers, step.targetAddr); }
      istep.path.Substitute(PivotBetree.CompactedNode(ILinkedBetree(step.path.Target()), step.compactedBuffers));
        { TargetCommutesWithI(step.path); }
      istep.path.Substitute(PivotBetree.CompactedNode(istep.path.Target(), istep.compactedBuffers));
    }
  }

  lemma FlushCommutesWithI(step: Step, replacementRanking: Ranking)
    // TODO(jonh): replace most of these requires with step.Valid()?
    requires step.WF()
    requires step.InternalFlushStep?
    requires step.path.Target().Acyclic()
    requires step.path.Target().ValidRanking(replacementRanking)
    requires step.path.Target().Root().OccupiedChildIndex(step.childIdx)
    requires InsertFlushReplacement(step.path.Target(), step.childIdx, step.targetAddr, step.targetChildAddr).WF()
    requires InsertFlushReplacement(step.path.Target(), step.childIdx, step.targetAddr, step.targetChildAddr).ValidRanking(replacementRanking)
    requires step.path.Target().diskView.IsFresh({step.targetAddr, step.targetChildAddr})
    ensures ILinkedBetree(InsertFlushReplacement(step.path.Target(), step.childIdx, step.targetAddr, step.targetChildAddr))
      == ILinkedBetree(step.path.Target()).Flush(step.childIdx)
  {
    var replacement := InsertFlushReplacement(step.path.Target(), step.childIdx, step.targetAddr, step.targetChildAddr);
    // trigger
    assert ILinkedBetree(replacement).pivotTable == ILinkedBetree(step.path.Target()).Flush(step.childIdx).pivotTable;
    forall i | 0 <= i < |ILinkedBetree(replacement).children|
    ensures ILinkedBetree(replacement).children[i] == ILinkedBetree(step.path.Target()).Flush(step.childIdx).children[i]
    {
      ILinkedBetreeIgnoresRanking(step.path.Target(), step.path.Target().TheRanking(), replacementRanking);
      ILinkedBetreeIgnoresRanking(replacement, replacement.TheRanking(), replacementRanking);
      ChildIdxAcyclic(replacement, i);
      var target := step.path.Target();
      if i == step.childIdx {
        var root := target.Root();
        var keepKeys := AllKeys() - root.DomainRoutedToChild(step.childIdx).KeySet();
        var keptBuffers := root.buffers.ApplyFilter(keepKeys);
        var movedBuffers := root.buffers.ApplyFilter(root.DomainRoutedToChild(step.childIdx).KeySet());
        // BetreeNode of the new child, to be stored at targetChildAddr in the diskview
        var subroot := target.diskView.Get(root.children[step.childIdx]);
        var subroot' := BetreeNode(subroot.buffers.PushBufferStack(movedBuffers), subroot.pivotTable, subroot.children);
        // BetreeNode of the new root, to be stored at targetAddr in the diskview
        var children' := root.children[step.childIdx := Pointer.Some(step.targetChildAddr)];
        var root' := BetreeNode(keptBuffers, root.pivotTable, children');

        var dv' := target.diskView.ModifyDisk(step.targetAddr, root').ModifyDisk(step.targetChildAddr, subroot');
        
        calc {
          ILinkedBetree(replacement).children[i];
          ILinkedBetreeNode(replacement.ChildAtIdx(i), replacementRanking);
          PivotBetree.BetreeNode(subroot.buffers.PushBufferStack(movedBuffers), subroot.pivotTable, IChildren(replacement.ChildAtIdx(i), replacementRanking));
          {
            forall k | 0 <= k < |IChildren(target.ChildAtIdx(i), replacementRanking)|
            ensures IChildren(target.ChildAtIdx(i), replacementRanking)[k] 
                  == IChildren(replacement.ChildAtIdx(i), replacementRanking)[k]
            {
              DiskSubsetImpliesIdenticalInterpretationsWithRanking(target.ChildAtIdx(i).ChildAtIdx(k), replacement.ChildAtIdx(i).ChildAtIdx(k), replacementRanking);
            }
            // trigger
            assert IChildren(replacement.ChildAtIdx(i), replacementRanking) == IChildren(target.ChildAtIdx(i), replacementRanking);
          }
          PivotBetree.BetreeNode(subroot.buffers.PushBufferStack(movedBuffers), subroot.pivotTable, IChildren(target.ChildAtIdx(i), replacementRanking));
          ILinkedBetreeNode(target.ChildAtIdx(i), replacementRanking).PushBufferStack(movedBuffers);
          ILinkedBetree(target).Flush(step.childIdx).children[i];
        }
      } else {
        DiskSubsetImpliesIdenticalInterpretationsWithRanking(target.ChildAtIdx(i), replacement.ChildAtIdx(i), replacementRanking);
      }
    }
  }

  // Generate a ranking for the Flush replacement LinkedBetree
  lemma FlushReplacementRanking(target: LinkedBetree, targetRanking: Ranking, childIdx:nat, targetAddr: Address, targetChildAddr: Address)
  returns (replacementRanking: Ranking)
    requires target.WF()
    requires target.ValidRanking(targetRanking)
    requires RankingIsTight(target.diskView, targetRanking)
    requires target.HasRoot()
    requires target.Root().OccupiedChildIndex(childIdx)
    requires targetAddr !in targetRanking 
    requires targetChildAddr !in targetRanking
    requires target.diskView.IsFresh({targetAddr, targetChildAddr})
    requires InsertFlushReplacement(target, childIdx, targetAddr, targetChildAddr).WF()
    ensures InsertFlushReplacement(target, childIdx, targetAddr, targetChildAddr).ValidRanking(replacementRanking)
    ensures replacementRanking.Keys == targetRanking.Keys + {targetAddr, targetChildAddr}
    ensures IsSubMap(targetRanking, replacementRanking)
    ensures target.ValidRanking(replacementRanking)
  {
    var oldRootRanking := targetRanking[target.root.value];
    var oldChildRanking := targetRanking[target.ChildAtIdx(childIdx).root.value];
    replacementRanking := targetRanking[targetAddr := oldRootRanking][targetChildAddr := oldChildRanking];
  }

  lemma InternalFlushStepRefines(v: Variables, v': Variables, lbl: TransitionLabel, step: Step)
    requires Inv(v)
    requires Inv(v')  // prereq
    requires NextStep(v, v', lbl, step)
    requires step.InternalFlushStep?
    ensures PivotBetree.NextStep(I(v), I(v'), ILbl(lbl), IStep(step))
  {
    var istep := IStep(step);
    var replacement := InsertFlushReplacement(step.path.Target(), step.childIdx, step.targetAddr, step.targetChildAddr);
    var targetRanking := BuildTightRanking(step.path.linked, step.path.linked.TheRanking());
    ValidRankingAllTheWayDown(targetRanking, step.path);
    var replacementRanking := FlushReplacementRanking(step.path.Target(), targetRanking, step.childIdx, step.targetAddr, step.targetChildAddr); 
    FreshSubstitutionImpliesSubdisk(step.path, replacement, step.pathAddrs);
    BuildTightPreservesInterpretation(step.path.Substitute(replacement, step.pathAddrs));
    SubstituteCommutesWithI(replacement, replacementRanking, step.path, step.pathAddrs);
    FlushCommutesWithI(step, replacementRanking);
    TargetCommutesWithI(step.path);
  }

  predicate HasChild(linked: LinkedBetree, idx: nat)
  {
    && linked.WF()
    && linked.HasRoot()
    && linked.Root().ValidChildIndex(idx)
  }

  lemma IdenticalChildrenCommutesWithI(linked: LinkedBetree, idx: nat, linked': LinkedBetree, idx': nat, ranking': Ranking)
    requires HasChild(linked, idx)
    requires HasChild(linked', idx')
    requires linked.ValidRanking(ranking')
    requires linked'.ValidRanking(ranking')
    requires linked.diskView.IsSubsetOf(linked'.diskView)
    requires linked.Root().children[idx] == linked'.Root().children[idx']
    ensures linked.Acyclic()  // prereq
    ensures ILinkedBetree(linked).children[idx] == ILinkedBetree(linked').children[idx']
  {
    ChildIdxCommutesWithI(linked, idx, linked.TheRanking());
    ILinkedBetreeIgnoresRanking(linked.ChildAtIdx(idx), linked.TheRanking(), ranking');
    DiskSubsetImpliesIdenticalInterpretationsWithRanking(linked.ChildAtIdx(idx), linked'.ChildAtIdx(idx'), ranking');
    ILinkedBetreeIgnoresRanking(linked'.ChildAtIdx(idx'), linked'.TheRanking(), ranking');
    ChildIdxCommutesWithI(linked', idx', linked'.TheRanking());
  }

  lemma SplitCommutesWithI(step: Step)
    requires step.WF()
    requires step.InternalSplitStep?
    requires step.path.Target().Acyclic()
    requires step.path.Target().diskView.IsFresh(step.newAddrs.Repr())
    requires step.path.Target().CanSplitParent(step.request)
    ensures step.path.Target().SplitParent(step.request, step.newAddrs).Acyclic()
    ensures ILinkedBetree(step.path.Target()).SplitParentDefn.requires(step.request)
    ensures ILinkedBetree(step.path.Target().SplitParent(step.request, step.newAddrs)) == ILinkedBetree(step.path.Target()).SplitParent(step.request)
  {
    var rankingAfterReplacement := RankingAfterSplitReplacement(step.path.Target(), step.path.Target().TheRanking(), step.request, step.newAddrs);
    var splitIdx := step.request.childIdx;
    var target := step.path.Target();
    var child := target.ChildAtIdx(splitIdx);
    target.SplitParentCanSubstitute(step.request, step.newAddrs);  // split target preserves WF
    var itarget := ILinkedBetree(step.path.Target());
    var ichild := itarget.children[step.request.childIdx];
    assert PivotBetree.WFChildren(itarget.children);  // trigger
    ChildIdxAcyclic(target, splitIdx);
    ChildIdxCommutesWithI(target, splitIdx, target.TheRanking());
    ILinkedBetreeIgnoresRanking(child, target.TheRanking(), child.TheRanking());
    IndexinessCommutesWithI(child);

    var target' := target.SplitParent(step.request, step.newAddrs);
    var itarget' := itarget.SplitParent(step.request);
    forall idx:nat | itarget'.ValidChildIndex(idx)
      ensures ILinkedBetree(target').children[idx] == itarget'.children[idx]
    {
      var oldChild := target.ChildAtIdx(step.request.childIdx);
      var (newLeftChild, newRightChild) := if step.request.SplitLeaf? then oldChild.Root().SplitLeaf(step.request.splitKey) else oldChild.Root().SplitIndex(step.request.childPivotIdx);

      var ioldChild := itarget.children[step.request.childIdx];
      var (inewLeftChild, inewRightChild) := if step.request.SplitLeaf? then ioldChild.SplitLeaf(step.request.splitKey) else ioldChild.SplitIndex(step.request.childPivotIdx);
    
      var ranking' := RankingAfterSplitReplacement(target, target.TheRanking(), step.request, step.newAddrs);
      if idx < splitIdx {
        IdenticalChildrenCommutesWithI(target, idx, target', idx, ranking');
      } else if splitIdx == idx {
        // All the left grandchildren match.
        forall cidx:nat | inewLeftChild.ValidChildIndex(cidx)
          ensures ILinkedBetreeNode(LinkedBetree(Some(step.newAddrs.left), target'.diskView), ranking').children[cidx] == inewLeftChild.children[cidx]
        {
          ILinkedBetreeIgnoresRanking(target, ranking', target.TheRanking());
          ChildIdxCommutesWithI(target, step.request.childIdx, ranking');
          var oldGrandchildPtr := oldChild.Root().children[cidx];
          var newGrandchildPtr := LinkedBetree(Some(step.newAddrs.left), target'.diskView).Root().children[cidx];
          DiskSubsetImpliesIdenticalInterpretationsWithRanking(
              LinkedBetree(oldGrandchildPtr, oldChild.diskView),
              LinkedBetree(newGrandchildPtr, target'.diskView),
              ranking');
        }
        ILinkedBetreeIgnoresRanking(target'.ChildAtIdx(idx), target'.TheRanking(), ranking');
        ChildIdxCommutesWithI(target', idx, target'.TheRanking());
      } else if splitIdx + 1 == idx {
        // All the right grandchildren match.
        if step.request.SplitIndex? {
          forall cidx:nat | inewRightChild.ValidChildIndex(cidx)
            ensures ILinkedBetreeNode(LinkedBetree(Some(step.newAddrs.right), target'.diskView), ranking').children[cidx] == inewRightChild.children[cidx]
          {
            ILinkedBetreeIgnoresRanking(target, ranking', target.TheRanking());
            ChildIdxCommutesWithI(target, step.request.childIdx, ranking');
            var oldGrandchildPtr := oldChild.Root().children[cidx + step.request.childPivotIdx];
            var newGrandchildPtr := LinkedBetree(Some(step.newAddrs.right), target'.diskView).Root().children[cidx];
            DiskSubsetImpliesIdenticalInterpretationsWithRanking(
                LinkedBetree(oldGrandchildPtr, oldChild.diskView),
                LinkedBetree(newGrandchildPtr, target'.diskView),
                ranking');
          }
        } else {
          assert IChildren(LinkedBetree(Some(step.newAddrs.right), target'.diskView), ranking')[0] == PivotBetree.Nil;  // trigger
        }
        ILinkedBetreeIgnoresRanking(target'.ChildAtIdx(idx), target'.TheRanking(), ranking');
        ChildIdxCommutesWithI(target', idx, target'.TheRanking());
      } else {
        IdenticalChildrenCommutesWithI(target, idx-1, target', idx, ranking');
      }
    }
    assert ILinkedBetree(target').children == itarget'.children;  // trigger extensionality
  }

  lemma InternalSplitStepRefines(v: Variables, v': Variables, lbl: TransitionLabel, step: Step)
    requires Inv(v)
    requires Inv(v')  // prereq
    requires NextStep(v, v', lbl, step)
    requires step.InternalSplitStep?
    ensures PivotBetree.NextStep(I(v), I(v'), ILbl(lbl), IStep(step))
  {
    var istep := IStep(step);
    // TODO(jonh): lots of duplication with InvNextInternalSplitStep
    var oldRanking := BuildTightRanking(v.linked, v.linked.TheRanking());
    var replacement := step.path.Target().SplitParent(step.request, step.newAddrs);
    ValidRankingAllTheWayDown(oldRanking, step.path);
    var replacementRanking := RankingAfterSplitReplacement(step.path.Target(), oldRanking, step.request, step.newAddrs);
    FreshSubstitutionImpliesSubdisk(step.path, replacement, step.pathAddrs);
    SubstituteCommutesWithI(replacement, replacementRanking, step.path, step.pathAddrs);
    //assert istep.path.Target() == ILinkedBetree(step.path.Target());
    SplitCommutesWithI(step);
    TargetCommutesWithI(step.path);
    BuildTightPreservesInterpretation(step.path.Substitute(replacement, step.pathAddrs));
    // assert PivotBetree.InternalSplit(I(v), I(v'), ILbl(lbl), IStep(step));
  }

  lemma NextRefines(v: Variables, v': Variables, lbl: TransitionLabel)
    requires Inv(v)
    requires Next(v, v', lbl)
    ensures v'.WF()
    ensures Inv(v')
    ensures PivotBetree.Next(I(v), I(v'), ILbl(lbl))
  {
    InvNext(v, v', lbl);
    var step: Step :| NextStep(v, v', lbl, step);
    match step {
      case QueryStep(receipt) => {
        assert PivotBetree.NextStep(I(v), I(v'), ILbl(lbl), IStep(step));
      }
      case PutStep() => {
        assert PivotBetree.NextStep(I(v), I(v'), ILbl(lbl), IStep(step));
      }
      case QueryEndLsnStep() => {
        assert PivotBetree.NextStep(I(v), I(v'), ILbl(lbl), IStep(step));
      }
      case FreezeAsStep() => {
        assert PivotBetree.NextStep(I(v), I(v'), ILbl(lbl), IStep(step));
      }
      case InternalGrowStep(_) => {
        InternalGrowStepRefines(v, v', lbl, step);
      }
      case InternalSplitStep(_, _, _, _) => {
        InternalSplitStepRefines(v, v', lbl, step);
      }
      case InternalFlushStep(_, _, _, _, _) => {
        InternalFlushStepRefines(v, v', lbl, step);
      }
      case InternalCompactStep(_, _, _, _) => {
        InternalCompactStepRefines(v, v', lbl, step);
      }
    }
  }
}
