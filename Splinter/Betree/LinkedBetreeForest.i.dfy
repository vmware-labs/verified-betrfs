// Copyright 2018-2021 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, and University of Washington
// SPDX-License-Identifier: BSD-2-Clause

include "PivotBetree.i.dfy"
include "../../lib/Buckets/BoundedPivotsLib.i.dfy"
include "../Journal/GenericDisk.i.dfy"
include "Domain.i.dfy"
include "LinkedForest.i.dfy"

// TODO:
// This module deals with 
// 1. Concretize buffer implementation with Forest (seqs of B+ tree)
// 2. Filter should be implicitly tracked by pivot table (no more apply filters)
//    - In LinkedBetree we did not restrict the range of splitted child
// 3. Track active buffers for each child, as we don't want to visit a buffer that is flushed to a child already

// Naming: BranchedBetree? 
module LinkedBetreeForest
{
  import opened BoundedPivotsLib
  import opened DomainMod
  import opened GenericDisk
  import opened KeyType
  import opened LSNMod
  import opened MemtableMod
  import opened MsgHistoryMod
  import opened Options
  import opened Sequences
  import opened StampedMod
  import opened Upperbounded_Lexicographic_Byte_Order_Impl
  import opened Upperbounded_Lexicographic_Byte_Order_Impl.Ord
  import opened ValueMessage
  import opened Maps
  import TotalKMMapMod
  
  import LF = LinkedForestMod
  import LB = LinkedBranchMod

  type Pointer = GenericDisk.Pointer
  type Address = GenericDisk.Address
  type StampedBetree = Stamped<LinkedBetree>
  type StampedForest = Stamped<LF.LinkedForest> // TODO: revisit after marshall layer 

  function EmptyLinkedBetree() : (out: LinkedBetree)
  {
    LinkedBetree(None, EmptyDisk())
  }

  function EmptyImage() : StampedBetree
  {
    Stamped(EmptyLinkedBetree(), 0)
  }

  type Element = Upperbounded_Lexicographic_Byte_Order_Impl.Ord.Element

  datatype TransitionLabel =
      QueryLabel(endLsn: LSN, key: Key, value: Value)
    | PutLabel(puts: MsgHistory)
    | QueryEndLsnLabel(endLsn: LSN)
    | FreezeAsLabel(linkedBetree: StampedBetree, forest: StampedForest)
    | InternalLabel()


  datatype BetreeNode = BetreeNode(
    // bundle's filter apply to multiple branches
    buffers: seq<Address>, // Forest Disk
    pivotTable: PivotTable,
    children: seq<Pointer>, // Betree Disk
    activeBufferRanges: seq<nat>  // parallel DS to children array, each entry stores the start of active buffer range for the corresponding child
  ) {
    predicate WF() {
      && WFPivots(pivotTable)
      && |children| == NumBuckets(pivotTable)
      && |children| == |activeBufferRanges|
      && (forall i | i < |activeBufferRanges| :: activeBufferRanges[i] <= |buffers|)
    }

    // predicate 

    predicate ValidChildIndex(childIdx: nat)
    {
      && BetreeNode?
      && childIdx < NumBuckets(pivotTable)
    }

    predicate OccupiedChildIndex(childIdx: nat)
      requires WF()
    {
      && ValidChildIndex(childIdx)
      && children[childIdx].Some?
    }

    function PushBufferStack(addr: Address) : (out: BetreeNode)
      requires WF()
      ensures out.WF()
    {
      BetreeNode(buffers + [addr], pivotTable, children, activeBufferRanges)
    }

    // TODO: doesn't belong here anymore because we can no longer just reach into things now
    // function ApplyFilter(filter: Domain) : (out: BetreeNode)
    //   requires WF()
    //   ensures out.WF()
    // {
    //   BetreeNode(buffers.ApplyFilter(filter.KeySet()), pivotTable, children)
    // }

    function ChildDomain(childIdx: nat) : (out: Domain)
      requires WF()
      requires BetreeNode?
      requires ValidChildIndex(childIdx)
      ensures out.WF()
    {
      var out := Domain(pivotTable[childIdx], pivotTable[childIdx+1]);
      reveal_IsStrictlySorted();
      out.reveal_SaneKeys(); 
      out
    }

    predicate KeyInDomain(key: Key)
    {
      && WF()
      && BetreeNode?
      && BoundedKey(pivotTable, key)
    }

    function ChildPtr(key: Key) : Pointer
      requires KeyInDomain(key)
    {
      children[Route(pivotTable, key)]
    }

    function ChildBufferRange(key: Key) : (i: nat)
      requires KeyInDomain(key)
    {
      activeBufferRanges[Route(pivotTable, key)]
    }
  }

  // PivotTable constructor for a total domain
  function TotalPivotTable() : PivotTable
  {
    [TotalDomain().start, TotalDomain().end]
  }

  // BetreeNode constructor for empty node
  function EmptyRoot(domain: Domain) : (out: BetreeNode)
    requires domain.WF()
    requires domain.Domain?
    ensures out.WF()
  {
    var pivotTable := [domain.start, domain.end];
    domain.reveal_SaneKeys();  /* jonh suspicious lt leak */
    assert Keyspace.IsStrictlySorted(pivotTable) by { reveal_IsStrictlySorted(); }  /* jonh suspicious lt leak */
    BetreeNode([], pivotTable, [None], [0])
  }

  datatype DiskView = DiskView(entries: map<Address, BetreeNode>) 
  {
    // TODO(jonh): some duplication with LinkedJournal.DiskView; refactor into library superclassish thing?
    // Or a generic with GenericDisk.DiskView<T>?
    // BetreeNodes are WF()
    predicate EntriesWF() 
    {
      (forall addr | addr in entries :: entries[addr].WF())
    }

    predicate IsNondanglingPointer(ptr: Pointer)
    {
      ptr.Some? ==> ptr.value in entries
    }

    predicate NodeHasNondanglingChildPtrs(node: BetreeNode)
    {
      node.BetreeNode? ==>
      (forall idx:nat | idx < |node.children| :: IsNondanglingPointer(node.children[idx]))
    }

    predicate NoDanglingPointers()  // i.e. disk is closed wrt to all the pointers in the nodes on disk
    {
      (forall addr | addr in entries :: NodeHasNondanglingChildPtrs(entries[addr]))
    }

    predicate WF()
    {
      && EntriesWF()
      && NoDanglingPointers()
    }   

    function Get(ptr: Pointer) : BetreeNode
      // requires WF()
      requires IsNondanglingPointer(ptr)
      requires ptr.Some?
    {
      entries[ptr.value]
    }

    // buffer not in entries, it belongs to a different disk
    predicate BufferInNode(buffer: Address)
    {
      (exists addr :: addr in entries && entries[addr].BetreeNode? && buffer in entries[addr].buffers)
    }

    function Buffers() : iset<Address>
    {
      iset buffer:Address | BufferInNode(buffer)
    }

    predicate AgreesWithDisk(other: DiskView)
    {
      MapsAgree(entries, other.entries)
    }

    predicate IsSubsetOf(other: DiskView)
    {
      && entries.Keys <= other.entries.Keys 
      && AgreesWithDisk(other)
    }

    // The node at this address has child pointers that respect ranking
    predicate NodeChildrenRespectsRank(ranking: Ranking, addr: Address)
      requires WF()
      requires addr in entries
      requires addr in ranking
    {
      && var node := entries[addr];
      && (forall childIdx:nat | node.ValidChildIndex(childIdx) && node.children[childIdx].Some? ::
        && node.children[childIdx].value in ranking  // ranking is closed
        && ranking[node.children[childIdx].value] < ranking[addr]  // decreases
      )
    }

    // Together with NodeChildrenRespectsRank, this says that ranking is closed
    predicate ValidRanking(ranking: Ranking) 
      requires WF()
    {
      forall addr | 
        && addr in ranking 
        && addr in entries 
      ::
        NodeChildrenRespectsRank(ranking, addr)
    }

    predicate IsFresh(addrs: set<Address>) {
      addrs !! entries.Keys
    } 

    function {:opaque} MergeDisk(other: DiskView) : (out: DiskView)
      // ensure result is sound -- keys and their values must come from one of these places
      ensures forall addr | addr in out.entries 
        :: || (addr in entries && out.entries[addr] == entries[addr])
           || (addr in other.entries && out.entries[addr] == other.entries[addr])
      // ensure result is complete -- result must contain all the keys
      ensures entries.Keys <= out.entries.Keys
      ensures other.entries.Keys <= out.entries.Keys
    {
      DiskView.DiskView(MapUnion(entries, other.entries))
    }
  }

  function EmptyDisk() : DiskView {
    DiskView.DiskView(map[])
  }

  function {:opaque} MergeDiskViews(diskViews: seq<DiskView>) : (out: DiskView)
    // ensure result is sound -- keys and their values must come from one of these places
    ensures forall addr | addr in out.entries 
      :: (exists i :: 
            && 0 <= i < |diskViews|
            && addr in diskViews[i].entries
            && out.entries[addr] == diskViews[i].entries[addr]
      )
    // ensure result is complete -- result must contain all the keys
    ensures forall i | 0 <= i < |diskViews| :: diskViews[i].entries.Keys <= out.entries.Keys
    decreases |diskViews|
  { var out :=
      if |diskViews| == 0 then EmptyDisk()
      else diskViews[0].MergeDisk(MergeDiskViews(diskViews[1..]));
    reveal_MergeDiskViews();
    out
  }

  
  // This is the unit of interpretation: A LinkedBetree has enough info in it to interpret to a PivotBetree.BetreeNode.
  datatype LinkedBetree = LinkedBetree(
    root: Pointer,
    diskView: DiskView
  )
  {
    predicate WF() {
      && diskView.WF()
      && diskView.IsNondanglingPointer(root)
    }

    predicate HasRoot() {
      && diskView.IsNondanglingPointer(root)
      && root.Some?
    }

    function Root() : BetreeNode
      requires HasRoot()
    {
      diskView.Get(root)
    }

    function ChildAtIdx(idx: nat) : LinkedBetree
      requires WF()
      requires HasRoot()
      requires Root().ValidChildIndex(idx)
    {
      LinkedBetree(Root().children[idx], diskView)
    }

    function ChildForKey(key: Key) : LinkedBetree
      requires HasRoot()
      requires Root().KeyInDomain(key)
    {
      LinkedBetree(Root().ChildPtr(key), diskView)
    }

    function GetRank(ranking: Ranking) : nat
      requires WF()
    {
      if HasRoot() && root.value in ranking then ranking[root.value]+1 else 0
    }

    function GetChildCount() : nat 
      requires WF()
    {
      if HasRoot() then |Root().children| else 0
    }

    // this says that ranking is closed 
    predicate ValidRanking(ranking: Ranking) 
      requires WF()
    {
      && diskView.ValidRanking(ranking)
      && (HasRoot() ==> root.value in ranking)  // ranking covers tree from this root
    }

    predicate Acyclic()
    {
      && WF()
      && (exists ranking :: ValidRanking(ranking))
    }

    function TheRanking() : Ranking
      requires Acyclic()
    {
      var out :| ValidRanking(out);
      out
    }

    // Build a tight disk with respect to this root
    function BuildTightTreeUsingRanking(ranking: Ranking) : (out: LinkedBetree)
      requires WF()
      requires ValidRanking(ranking)
      ensures out.root == root
      ensures HasRoot() ==> root.value in out.diskView.entries
      ensures HasRoot() ==> out.diskView.entries[root.value] == Root()
      decreases GetRank(ranking)
    {
      if !HasRoot()
      then 
        // base case, return empty disk
        LinkedBetree(root, EmptyDisk())
      else 
        var numChildren := |Root().children|;
        // list of tight diskviews at each of my children
        var tightChildrenDvs := seq(numChildren, i requires 0 <= i < numChildren => ChildAtIdx(i).BuildTightTreeUsingRanking(ranking).diskView);
        var dv := DiskView.DiskView(MergeDiskViews(tightChildrenDvs).entries[root.value := Root()]);
        LinkedBetree(root, dv)
    }
    
    function BuildTightTree() : LinkedBetree {
      if Acyclic() then BuildTightTreeUsingRanking(TheRanking()) 
      else this  // Can't build a tight tree if I'm not acyclic
    }
  }

  
  // LinkedBetreee w/ Forest State Machine

  datatype Variables = Variables(
    memtable: Memtable,
    linked: LinkedBetree,
    forestSM: LF.Variables)
  {
    // linked diskView and forest diskView should have disjoint addresses
    predicate DisjointForest() {
      && linked.diskView.IsFresh(forestSM.Addresses())
    }

    // buffers in each node should be known to forest
    predicate BoundedForest() {
      // && (forall addr, buffer | )
      && (forall buffer | buffer in linked.diskView.Buffers() :: buffer in forestSM.forest.trees)
    }

    predicate WF() {
      && linked.WF()
      && forestSM.WF()
      // TODO: move to Valid
      && DisjointForest()
      && BoundedForest()
    }
  }

  // TODO(jonh): SO much copypasta from PivotBetree! Library, paramaterize child mechanism?
  datatype QueryReceiptLine = QueryReceiptLine(
    ptr: Pointer,
    result: Message)
  {
    predicate WF()
    {
      && result.Define?
    }
  }

  datatype QueryReceipt = QueryReceipt(
    key: Key,
    diskView: DiskView,
    forest: LF.LinkedForest,
    lines: seq<QueryReceiptLine>)
  {
    predicate Structure()
    {
      && 0 < |lines|
      && (forall i:nat | i < |lines| :: lines[i].ptr.Some? <==> i < |lines|-1)
      && (forall i:nat | i < |lines|-1 :: diskView.IsNondanglingPointer(lines[i].ptr))
      && Last(lines).result == Define(DefaultValue())
      && diskView.WF()
      && forest.WF() // don't have to require disjointness here since query is read only 
    }

    function Node(i: nat) : (out:BetreeNode)
      requires Structure()
      requires i < |lines| - 1  // last line is None ptr
      ensures out.WF()
    {
      diskView.Get(lines[i].ptr)
    }

    predicate AllLinesWF()
    {
      && Structure()
      && (forall i:nat | i < |lines|-1 :: Node(i).KeyInDomain(key))
      && (forall i:nat, buffer | i < |lines|-1 && buffer in Node(i).buffers :: forest.ValidTree(buffer))
    }

    predicate ChildLinkedAt(i: nat)
      requires AllLinesWF()
      requires i < |lines|-1
    {
      lines[i+1].ptr == Node(i).ChildPtr(key)
    }

    function ResultAt(i: nat) : Message
      requires i < |lines|
    {
      lines[i].result
    }

    predicate ResultLinkedAt(i: nat)
      requires Structure()
      requires AllLinesWF()
      requires i < |lines| - 1
    {
      && var start := Node(i).ChildBufferRange(key); // only query on a child's active range
      && var msg := forest.Query(key, Node(i).buffers[start..]);
      && lines[i].result == Merge(msg, ResultAt(i+1))
    }

    predicate Valid()
    {
      && Structure()
      && AllLinesWF()
      && (forall i:nat | i < |lines| - 1 :: ChildLinkedAt(i))
      && (forall i:nat | i < |lines| - 1 :: ResultLinkedAt(i))
    }

    predicate ValidFor(linked: LinkedBetree, forest: LF.LinkedForest, key: Key)
    {
      && Valid()
      && this.diskView == linked.diskView
      && this.lines[0].ptr == linked.root
      && this.forest == forest
      && this.key == key
    }

    function Result() : Message
      requires Structure()
    {
      ResultAt(0)
    }
  }

  predicate Query(v: Variables, v': Variables, lbl: TransitionLabel, receipt: QueryReceipt)
  {
    && lbl.QueryLabel?
    && lbl.endLsn == v.memtable.seqEnd
    && receipt.ValidFor(v.linked, v.forestSM.forest, lbl.key)
    && Define(lbl.value) == Merge(v.memtable.Query(lbl.key), receipt.Result())
    && v' == v
  }

  predicate Put(v: Variables, v': Variables, lbl: TransitionLabel)
  {
    && lbl.PutLabel?
    && lbl.puts.WF()
    && lbl.puts.seqStart == v.memtable.seqEnd
    && v' == v.(memtable := v.memtable.ApplyPuts(lbl.puts))
  }

  predicate QueryEndLsn(v: Variables, v': Variables, lbl: TransitionLabel)
  {
    && lbl.QueryEndLsnLabel?
    && lbl.endLsn == v.memtable.seqEnd
    && v' == v
  }

  predicate FreezeAs(v: Variables, v': Variables, lbl: TransitionLabel)
  {
    && lbl.FreezeAsLabel?
    && v.WF()
    && v.memtable.IsEmpty()
    && lbl.linkedBetree == Stamped(v.linked, v.memtable.seqEnd)
    && lbl.forest == Stamped(v.forestSM.forest, v.memtable.seqEnd) // TODO: revisit after marshall layer
    && v' == v
  }

  predicate InternalFlushMemtable(v: Variables, v': Variables, lbl: TransitionLabel, step: Step)
  {
    && lbl.InternalLabel?
    && step.InternalFlushMemtableStep?
    && step.WF()
    && assert step.branch.I().WF() by { step.branch.WFI( step.branch.I() ); } // TODO: revisit
    && step.branch.I().I() == v.memtable.buffer  // new branch must represent memtable 

    && v.WF()
    && v'.WF() // be careful
    && v'.linked.diskView.AgreesWithDisk(v.linked.diskView)
      // NB: linked.WF() ==> No nondangling pointers, so in practice linked <= linked'
    && v'.linked.HasRoot()
    && v'.linked.Root() == (
      if !v.linked.HasRoot()
      then BetreeNode([step.branch.root], TotalPivotTable(), [None], [0])
      else v.linked.Root().PushBufferStack(step.branch.root))

    && LF.Next(v.forestSM, v'.forestSM, LF.AddTreeLabel(step.branch))
  }

  type PathAddrs = seq<Address>

  // Question is should one of the restriction on path be that 
  // replaced path can't have different, linked = a root (might even be a subtree and a disk)

  datatype Path = Path(linked: LinkedBetree, key: Key, depth: nat)
  {
    function Subpath() : (out: Path)
      requires 0 < depth
      requires linked.HasRoot()
      requires linked.Root().KeyInDomain(key)
    {
      Path(linked.ChildForKey(key), key, depth-1)
    }

    predicate Valid()
      decreases depth
    {
      && linked.WF()
      && linked.HasRoot()  
      && linked.Root().KeyInDomain(key)
      && (0 < depth ==> Subpath().Valid())  // implies path must lead to a non-nil node
    }

    function Target() : (out: LinkedBetree)
      requires Valid()
      ensures out.WF()
      ensures out.root.Some?
      ensures out.diskView == linked.diskView
      ensures out.HasRoot() ==> out.root.value in out.diskView.entries
      decreases depth
    {
      if 0 == depth
      then linked
      else Subpath().Target()
    }

    // shows that the Path can be replaced with 
    // we want to maintain the same property with regard to forest as before
    predicate CanSubstitute(replacement: LinkedBetree, pathAddrs: PathAddrs) 
    {
      && linked.WF()
      && replacement.WF()
      && depth == |pathAddrs|
      && Valid()
      && linked.diskView.IsSubsetOf(replacement.diskView)
    }

    function Substitute(replacement: LinkedBetree, pathAddrs: PathAddrs) : (out: LinkedBetree)
      requires CanSubstitute(replacement, pathAddrs)
      decreases depth, 1
    { 
      if depth == 0 
      then replacement
      else 
        var node := linked.Root();
        var subtree := Subpath().Substitute(replacement, pathAddrs[1..]);
        var newChildren := node.children[Route(node.pivotTable, key) := subtree.root];
        // child is replaced but no changes to buffers, so the new child should have the same 
        // active buffer range as the old child 
        var newNode := BetreeNode(node.buffers, node.pivotTable, newChildren, node.activeBufferRanges); 
        var newDiskView := DiskView.DiskView(subtree.diskView.entries[pathAddrs[0] := newNode]); 
        LinkedBetree(GenericDisk.Pointer.Some(pathAddrs[0]), newDiskView)
    }
  }

  function InsertGrowReplacement(oldRoot: LinkedBetree, newRootAddr:Address) : (out: LinkedBetree)
    requires oldRoot.WF()
  {
    // The new root node
    var root' := BetreeNode([], TotalPivotTable(), [oldRoot.root], [0]);
    // The new diskview
    var dv' := DiskView.DiskView(oldRoot.diskView.entries[newRootAddr := root']); 
    LinkedBetree(Pointer.Some(newRootAddr), dv')
  } 

  predicate InternalGrow(v: Variables, v': Variables, lbl: TransitionLabel, step: Step)
  {
    && v.WF()
    && step.WF()
    && lbl.InternalLabel?
    && step.InternalGrowStep?
    // Subway Eat Fresh!
    && v.linked.diskView.IsFresh({step.newRootAddr})
    && v' == v.(linked := InsertGrowReplacement(v.linked, step.newRootAddr).BuildTightTree())
  }

  predicate IsSplit(linked: LinkedBetree, linked': LinkedBetree, childIdx: nat, splitKey: Key)
  {
    && linked.WF()
    && linked'.WF()
    && linked.HasRoot()
    && linked'.HasRoot()
    && linked'.diskView.AgreesWithDisk(linked.diskView)
    && var root := linked.Root();
    && var root' := linked'.Root();

    && root.ValidChildIndex(childIdx)
    && PivotInsertable(root.pivotTable, childIdx, splitKey)
    && 0 < childIdx < NumBuckets(root.pivotTable) // Split can't extend domain of this node.
    && var oldChildPtr := root.children[childIdx];
    && oldChildPtr.Some?

    // Parent adds splitKey pivot; replaces child at childIdx with two children
    && root'.ValidChildIndex(childIdx+1)  // obvious once we have replace1with2, but we're not there yet
    && var leftChildPtr := root'.children[childIdx];
    && var rightChildPtr := root'.children[childIdx+1];
    && var childActiveRange := root.activeBufferRanges[childIdx];
    && root' == root.(
      pivotTable := InsertPivot(root.pivotTable, childIdx, splitKey),

      // replace1with2 is just telling us about the structure of
      // root'.children: the prefix and suffix are identical, and the new left
      // & right child ptrs appear where childIdx once was. But it *doesn't*
      // say anything about the value of leftChildPtr (resp. rightChildPtr),
      // since we fetched those out of root'.children in the var statement
      // above. That's a "clever" trick to leave nondeterminism that says we
      // don't care what the actual values of those pointers are.
      children := replace1with2(root.children, leftChildPtr, rightChildPtr, childIdx),
      activeBufferRanges := replace1with2(root.activeBufferRanges, childActiveRange, childActiveRange, childIdx) // yea?

      )

    // Children get correspending slices
    && leftChildPtr.Some?
    && rightChildPtr.Some?

    // TODO: we should be cleaning up pivot ranges, not buffers [revisit]

    // && var oldChild := linked.diskView.Get(oldChildPtr);
    // && var leftChild := linked'.diskView.Get(leftChildPtr);
    // && var rightChild := linked'.diskView.Get(rightChildPtr);

    // && leftChild == oldChild.ApplyFilter(Domain(root.pivotTable[childIdx-1], Element(splitKey)))
    // && rightChild == oldChild.ApplyFilter(Domain(Element(splitKey), root.pivotTable[childIdx]))

    // TODO(jonh): Say, ApplyFilter only affects buffers, but we also need to
    // carve up the pivot tables and children! ...in PivotBetree, too.
  }

  predicate InternalSplit(v: Variables, v': Variables, lbl: TransitionLabel, step: Step)
  {
    // todo: rewrite
    assume false; 
    && v.WF()
    && lbl.InternalLabel?
    && step.InternalSplitStep?
    && step.path.linked == v.linked
    && step.path.Valid()
    // // v && v' agree on everything down to Target()
    // // && step.path.IsSubstitution(v.linked, v'.linked, [])
    // // Target and Target' are related by a split operation
    // && IsSplit(step.path.Target(), step.path.Target(), step.childIdx, step.splitKey)
    // && v'.memtable == v.memtable  // UNCHANGED
  }

//   function InsertFlushReplacement(target: LinkedBetree, childIdx:nat, targetAddr: Address, targetChildAddr: Address) : (out: LinkedBetree)
//     requires target.WF()
//     requires target.HasRoot()
//     requires target.Root().OccupiedChildIndex(childIdx)
//   {
//     var root := target.Root();
//     var keepKeys := AllKeys() - root.ChildDomain(childIdx).KeySet();
//     var keptBuffers := root.buffers.ApplyFilter(keepKeys);
//     var movedBuffers := root.buffers.ApplyFilter(root.ChildDomain(childIdx).KeySet());
//     // BetreeNode of the new child, to be stored at targetChildAddr in the diskview
//     var subroot := target.diskView.Get(root.children[childIdx]);
//     var subroot' := BetreeNode(subroot.buffers.PushBufferStack(movedBuffers), subroot.pivotTable, subroot.children);

//     // BetreeNode of the new root, to be stored at targetAddr in the diskview
//     var children' := root.children[childIdx := Pointer.Some(targetChildAddr)];
//     var root' := BetreeNode(keptBuffers, root.pivotTable, children');
    
//     // The new diskview
//     var dv' := DiskView.DiskView(target.diskView.entries[targetAddr := root'][targetChildAddr := subroot']); 
//     LinkedBetree(Pointer.Some(targetAddr), dv')
//   } 

  // TODO: internal step for shifting the active buffer range, remove entries from the bufferstack

  // makes no changes to the forest as a whole
  // targetAddr: the node to flush, targetChildAddr: child with the latest update, pathAddrs: ancestor of flushed node
  predicate InternalFlush(v: Variables, v': Variables, lbl: TransitionLabel, step: Step)
  {
    && v.WF()
    && step.WF()
    && lbl.InternalLabel?
    && step.InternalFlushStep?
    && step.path.linked == v.linked
    && step.path.Valid()
//     && step.path.Target().Root().OccupiedChildIndex(step.childIdx)  // the downstream child must exist
//     // Subway Eat Fresh!
//     && v.linked.diskView.IsFresh({step.targetAddr, step.targetChildAddr} + Set(step.pathAddrs))
//     && v'.linked == step.path.Substitute( 
//         InsertFlushReplacement(step.path.Target(), step.childIdx, step.targetAddr, step.targetChildAddr), 
//         step.pathAddrs
//     ).BuildTightTree()
//     && v'.memtable == v.memtable  // UNCHANGED
  }

//   // target is the root node before it is compacted. 
//   // InsertReplacement returns a LinkedBetree that has the diskview of target with replacement placed at
//   // the replacementAddr
//   function InsertCompactReplacement(target: LinkedBetree, compactedBuffers: BufferStack, replacementAddr: Address) : (out: LinkedBetree)
//     requires target.WF()
//     requires target.HasRoot()
//     requires target.Root().buffers.Equivalent(compactedBuffers)
//     ensures out.WF() 
//   {
//     var root := target.Root();
//     var newRoot := BetreeNode(compactedBuffers, root.pivotTable, root.children);
//     var newDiskView := DiskView.DiskView(target.diskView.entries[replacementAddr := newRoot]);
//     LinkedBetree(GenericDisk.Pointer.Some(replacementAddr), newDiskView)
//   }

  // TODO: Compaction could result in removal of a tree, it is probably fine to use the full
  // system state to decide this in the modeling and use a reference count in the implementation
  // which refines to that, ref count should be tracked with this module and forest just takes a step to remove
  // it's safe to do bc each step should maintain WF of variables which requires all buffers to be bounded 
  // (are present in the tree)
  predicate InternalCompact(v: Variables, v': Variables, lbl: TransitionLabel, step: Step)
  {
    && v.WF()
    && step.WF()
    && lbl.InternalLabel?
    && step.InternalCompactStep?
    && step.path.linked == v.linked
    && step.path.Valid()
//     && step.path.Target().Root().buffers.Equivalent(step.compactedBuffers)
//     // Subway Eat Fresh!
//     && v.linked.diskView.IsFresh({step.targetAddr} + Set(step.pathAddrs))
//     && v'.linked == step.path.Substitute(
//         InsertCompactReplacement(step.path.Target(), step.compactedBuffers, step.targetAddr), 
//         step.pathAddrs
//     ).BuildTightTree()
//     && v'.memtable == v.memtable  // UNCHANGED
  }

//   // public:

//   predicate Init(v: Variables, stampedBetree: StampedBetree)
//   {
//     && stampedBetree.value.WF()
//     && stampedBetree.value.Acyclic()
//     && v == Variables(EmptyMemtable(stampedBetree.seqEnd), stampedBetree.value)
//   }

  datatype Step =
      QueryStep(receipt: QueryReceipt)
    | PutStep()
    | QueryEndLsnStep()
    | FreezeAsStep()
    | InternalFlushMemtableStep(branch: LB.LinkedBranch)
    // newRootAddr is the new address allocated for the new root
    | InternalGrowStep(newRootAddr: Address) 
    | InternalSplitStep(path: Path, childIdx: nat, splitKey: Key)
    // targetAddr is the fresh address at which new node is placed, and targetChildAddr is for the new child receiving the flush
    // pathAddrs is the new addresses to place all its ancestors, used in substitution 
    | InternalFlushStep(path: Path, childIdx: nat, targetAddr: Address, targetChildAddr: Address, pathAddrs: PathAddrs)
    // targetAddr is the fresh address at which compactedNode is placed. pathAddrs is the new addresses to place all its ancestors
    | InternalCompactStep(path: Path, compactedBuffers: BufferStack, targetAddr: Address, pathAddrs: PathAddrs)
  {
    predicate WF() {
      match this {
        case QueryStep(receipt) => receipt.Valid()
        case InternalFlushMemtableStep(branch) =>
          && branch.Acyclic()  // new branch must be acyclic

//         case InternalSplitStep(path, childIdx, splitKey) => 
//            && path.Valid()
        case InternalFlushStep(_, _, targetAddr, targetChildAddr, pathAddrs) => 
          && path.Valid()
          && path.Target().Root().ValidChildIndex(childIdx)
          && path.depth == |pathAddrs|
          && SeqHasUniqueElems(pathAddrs) 
          && {targetAddr, targetChildAddr} !! Set(pathAddrs)
          && targetAddr != targetChildAddr
//         case InternalCompactStep(path, compactedNode, targetAddr, pathAddrs) =>
//           && path.Valid()
//           && path.Target().Root().buffers.Equivalent(compactedBuffers)
//           && path.depth == |pathAddrs|
//           && SeqHasUniqueElems(pathAddrs) 
//           && {targetAddr} !! Set(pathAddrs)
        case _ => true
      }
    }
  }

//   predicate NextStep(v: Variables, v': Variables, lbl: TransitionLabel, step: Step)
//   {
//     match step {
//       case QueryStep(receipt) => Query(v, v', lbl, receipt)
//       case PutStep() => Put(v, v', lbl)
//       case QueryEndLsnStep() => QueryEndLsn(v, v', lbl)
//       case FreezeAsStep() => FreezeAs(v, v', lbl)
//       case InternalGrowStep(_) => InternalGrow(v, v', lbl, step)
//       case InternalSplitStep(_, _, _) => InternalSplit(v, v', lbl, step)
//       case InternalFlushStep(_, _, _, _, _) => InternalFlush(v, v', lbl, step)
//       case InternalCompactStep(_, _, _, _) => InternalCompact(v, v', lbl, step)
//     }
//   }

//   predicate Next(v: Variables, v': Variables, lbl: TransitionLabel) {
//     exists step: Step :: NextStep(v, v', lbl, step)
//   }
}
