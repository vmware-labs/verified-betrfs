// Copyright 2018-2021 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, and University of Washington
// SPDX-License-Identifier: BSD-2-Clause

// include "PivotBetree.i.dfy"
include "LinkedBetree.i.dfy"
include "../../lib/Buckets/BoundedPivotsLib.i.dfy"
include "../Journal/GenericDisk.i.dfy"
include "Domain.i.dfy"
include "LinkedForest.i.dfy"
include "SplitRequest.i.dfy"

// TODO:
// This module deals with 
// 1. Concretize buffer implementation with Forest (seqs of B+ tree)
// 2. Filter should be implicitly tracked by pivot table (no more apply filters)
//    - In LinkedBetree we did not restrict the range of splitted child
// 3. Track active buffers for each child, as we don't want to visit a buffer that is flushed to a child already

module BranchedBetreeMod
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
  import opened SplitRequestMod

  import LF = LinkedForestMod
  import LB = LinkedBranchMod

  type Pointer = GenericDisk.Pointer
  type Address = GenericDisk.Address
  type StampedBetree = Stamped<LinkedBetree>
  type StampedForest = Stamped<LF.LinkedForest> // TODO: revisit

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
     // Internal-x labels refine to no-ops at the abstract spec
    | InternalAllocationsLabel(addrs: seq<Address>)  // for steps that involve allocating new pages
    | InternalLabel()   // Local No-op label


  datatype BetreeNode = BetreeNode(
    // bundle's filter apply to multiple branches
    buffers: seq<Address>, // Forest Disk
    pivotTable: PivotTable,
    children: seq<Pointer>, // Betree Disk
    activeBufferRanges: seq<nat>  // parallel DS to children array, each entry stores the start of active buffer range for the corresponding child
  ) {
    predicate WF() {
      && (BetreeNode? ==>
        && WFPivots(pivotTable)
        && |children| == NumBuckets(pivotTable)
        && |children| == |activeBufferRanges|
        && (forall i:nat | i < |activeBufferRanges| :: activeBufferRanges[i] <= |buffers|))
    }

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
      requires BetreeNode?
      ensures out.WF()
    {
      BetreeNode(buffers + [addr], pivotTable, children, activeBufferRanges)
    }

    predicate IsLeaf()
    {
      && |children|==1
      && children[0].None?
    }

    predicate IsIndex()
    {
      && (forall i | 0 <= i < |children| :: children[i].Some?)
    }

    function MyDomain() : (out: Domain)
      requires WF()
    {
      Domain(pivotTable[0], Last(pivotTable))
    }

    function DomainRoutedToChild(childIdx: nat) : (out: Domain)
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

    // // Redundant; should equal domain.KeySet() for the domain specified by the pivotTable.
    // function KeySet() : iset<Key>
    //   requires WF()
    //   requires BetreeNode?  // TODO(jonh): trouble for Nils?
    // {
    //   iset key | KeyInDomain(key)
    // }

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

    // TODO(jonh): Again, Split has a bunch of duplicated (complex) definitions duplicated from PivotBetree.
    // Would be nice to find a way to factor out the structure duplicated across layers without
    // making the state machines difficult to read.

    // Called on leaf; creates a new pivot
    function SplitLeaf(splitKey: Key) : (out: (BetreeNode, BetreeNode))
      requires WF()
      requires IsLeaf()
      requires MyDomain().Contains(splitKey)
      requires splitKey != MyDomain().start.e
      ensures out.0.WF() && out.1.WF()
    {
      var newLeft := BetreeNode(buffers, [pivotTable[0], Element(splitKey)], [None], [0]);
      var newRight := BetreeNode(buffers, [Element(splitKey), pivotTable[1]], [None], [0]);
      assert newLeft.WF() by { Keyspace.reveal_IsStrictlySorted(); }
      assert newRight.WF() by { Keyspace.reveal_IsStrictlySorted(); }
      (newLeft, newRight)
    }

    // Called on index; lifts an existing pivot from the child
    function SplitIndex(pivotIdx: nat) : (out: (BetreeNode, BetreeNode))
      requires WF()
      requires IsIndex()
      requires 0 < pivotIdx < |pivotTable|-1
      ensures out.0.WF() && out.1.WF()
    {
      var splitElt := pivotTable[pivotIdx];
      var leftFilter := Domain(MyDomain().start, splitElt);
      var rightFilter := Domain(splitElt, MyDomain().end);

      var newLeft := BetreeNode(buffers, pivotTable[..pivotIdx+1], children[..pivotIdx], activeBufferRanges[..pivotIdx]);
      var newRight := BetreeNode(buffers, pivotTable[pivotIdx..], children[pivotIdx..], activeBufferRanges[pivotIdx..]);
      WFSlice(pivotTable, 0, pivotIdx+1);
      WFSuffix(pivotTable, pivotIdx);
      //assert WFChildren(children);  // trigger TODO(jonh) delete
      assert newLeft.WF();
      assert newRight.WF();
      (newLeft, newRight)
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
      && ptr.Some? ==> ptr.value in entries
    }

    predicate NodeHasNondanglingChildPtrs(node: BetreeNode)
      requires EntriesWF()
      requires node.WF()
    {
      node.BetreeNode? ==> (
        && (forall idx:nat | node.ValidChildIndex(idx) :: IsNondanglingPointer(node.children[idx]))
      )
    }

    predicate ChildLinked(node: BetreeNode, idx: nat)
      requires EntriesWF()
      requires node.WF()
      requires NodeHasNondanglingChildPtrs(node)
      requires node.BetreeNode?
      requires node.ValidChildIndex(idx)
    {
      node.children[idx].Some? ==> (
        entries[node.children[idx].value].MyDomain() == node.DomainRoutedToChild(idx)
      )
    }

    predicate NodeHasLinkedChildren(node: BetreeNode)
      requires EntriesWF()
      requires node.WF()
      requires NodeHasNondanglingChildPtrs(node)
    {
      node.BetreeNode? ==> (
        && (forall idx | node.ValidChildIndex(idx) :: ChildLinked(node, idx))
      )
    }

    predicate HealthyChildPointers()  // i.e. disk is closed wrt to all the pointers in the nodes on disk
      requires EntriesWF()
    {
      && (forall addr | addr in entries :: NodeHasNondanglingChildPtrs(entries[addr]))
      && (forall addr | addr in entries :: NodeHasLinkedChildren(entries[addr]))
    }

    predicate WF()
    {
      && EntriesWF()
      && HealthyChildPointers()
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

    // returns a new diskview with the new entry inserted
    function ModifyDisk(addr: Address, item: BetreeNode) : DiskView{
      DiskView.DiskView(entries[addr := item])
    }
  }

  function EmptyDisk() : DiskView {
    DiskView.DiskView(map[])
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

    function BuildTightTree() : (out: LinkedBetree)
      ensures out.diskView.IsSubsetOf(diskView)
    {
      if ! Acyclic() then
        // Need this case because at the state machine I don't have proof that after an
        // operation, that the new state is acyclic
        this
      else
        var tightDv := DiskView.DiskView(MapRestrict(diskView.entries, ReachableAddrs()));
        LinkedBetree(root, tightDv)
    }

    function ReachableAddrs() : set<Address>
      requires Acyclic()
    {
      ReachableAddrsUsingRanking(TheRanking())
    }

    function ReachableAddrsUsingRanking(ranking: Ranking) : (out: set<Address>)
      requires WF()
      requires ValidRanking(ranking)
      ensures HasRoot() ==> root.value in out
      ensures out <= diskView.entries.Keys
      decreases GetRank(ranking)
    {
      if !HasRoot() then {}
      else
        var numChildren := |Root().children|;
        var subTreeAddrs := seq(numChildren, i requires 0 <= i < numChildren => ChildAtIdx(i).ReachableAddrsUsingRanking(ranking));
        Sets.UnionSeqOfSetsSoundness(subTreeAddrs);
        {root.value} + Sets.UnionSeqOfSets(subTreeAddrs)
    }
    
    predicate CanSplitParent(request: SplitRequest)
    {
      && WF()
      && HasRoot()
      && Root().ValidChildIndex(request.childIdx)
      && var child := ChildAtIdx(request.childIdx);
      && child.HasRoot()
      && match request {
        case SplitLeaf(_, splitKey) => child.Root().SplitLeaf.requires(splitKey)
        case SplitIndex(_, childPivotIdx) => child.Root().SplitIndex.requires(childPivotIdx)
      }
    }

    function SplitKey(request: SplitRequest) : (out: Key)
      requires WF()
      requires CanSplitParent(request)
      ensures PivotInsertable(Root().pivotTable, request.childIdx+1, out)
    {
      var oldChild := ChildAtIdx(request.childIdx);
      var out := if request.SplitLeaf? then request.splitKey else oldChild.Root().pivotTable[request.childPivotIdx].e;

      assert PivotInsertable(Root().pivotTable, request.childIdx+1, out) by {
        Keyspace.reveal_IsStrictlySorted();
      }
      WFPivotsInsert(Root().pivotTable, request.childIdx+1, out);

      out
    }

    function SplitParent(request: SplitRequest, newAddrs: SplitAddrs) : (out: LinkedBetree)
      requires WF()
      requires CanSplitParent(request)
    {
      var oldChild := ChildAtIdx(request.childIdx);
      var (newLeftChild, newRightChild) := if request.SplitLeaf? then oldChild.Root().SplitLeaf(request.splitKey) else oldChild.Root().SplitIndex(request.childPivotIdx);
      var newChildren := replace1with2(Root().children, Some(newAddrs.left), Some(newAddrs.right), request.childIdx);
      var childActiveRange := Root().activeBufferRanges[request.childIdx];
      var newactiveBufferRanges := replace1with2(Root().activeBufferRanges, childActiveRange, childActiveRange, request.childIdx);

      // new children replace 1with2 
      var newParent := BetreeNode(Root().buffers, InsertPivot(Root().pivotTable, request.childIdx+1, SplitKey(request)), newChildren, newactiveBufferRanges);

      var dv' := diskView.ModifyDisk(newAddrs.left, newLeftChild).ModifyDisk(newAddrs.right, newRightChild).ModifyDisk(newAddrs.parent, newParent);
      LinkedBetree(Pointer.Some(newAddrs.parent), dv')
    }

    lemma SplitParentCanSubstitute(request: SplitRequest, newAddrs: SplitAddrs)
      requires CanSplitParent(request)
      requires newAddrs.HasUniqueElems()  // frameity frame frame
      requires diskView.IsFresh(newAddrs.Repr())  // frameity frame frame
      ensures SplitParent(request, newAddrs).WF()
      ensures SplitParent(request, newAddrs).Root().MyDomain() == Root().MyDomain()
    {
      var dv := SplitParent(request, newAddrs).diskView;
      var newParent := SplitParent(request, newAddrs).Root();

      WFPivotsInsert(Root().pivotTable, request.childIdx+1, SplitKey(request));

      forall idx:nat | newParent.ValidChildIndex(idx)
      ensures dv.IsNondanglingPointer(newParent.children[idx]) {
        if request.childIdx+1 < idx {
          assert dv.IsNondanglingPointer(Root().children[idx-1]);  // seq offset trigger
        }
      }

      forall idx:nat | newParent.ValidChildIndex(idx)
      ensures dv.ChildLinked(newParent, idx) {
        if idx < request.childIdx {
          assert diskView.ChildLinked(Root(), idx);  // seq offset trigger
        } else if request.childIdx+1 < idx {
          assert diskView.ChildLinked(Root(), idx-1);  // seq offset trigger
        }
      }

      forall i: nat | i < |newParent.activeBufferRanges|
        ensures newParent.activeBufferRanges[i] <= |newParent.buffers|
      {
        if i > request.childIdx + 1 {
          assert newParent.activeBufferRanges[i] == Root().activeBufferRanges[i-1];
        }
      }

      if request.SplitIndex? {
        var child := ChildAtIdx(request.childIdx).Root();
        var left := dv.entries[newAddrs.left];
        var right := dv.entries[newAddrs.right];

        forall idx:nat | left.ValidChildIndex(idx) ensures dv.ChildLinked(left, idx) {
          assert diskView.ChildLinked(child, idx);
          assert dv.ChildLinked(left, idx);
        }

        forall idx:nat | right.ValidChildIndex(idx) ensures dv.ChildLinked(right, idx) {
          assert diskView.ChildLinked(child, idx+request.childPivotIdx);
          assert dv.ChildLinked(right, idx);
        }
      }
      // assert dv.NodeHasLinkedChildren(dv.entries[newAddrs.parent]);
    }
  }

  // disk addresses that are created during a split
  datatype SplitAddrs = SplitAddrs(left: Address, right: Address, parent: Address)
  {
    predicate HasUniqueElems() {
      && left!=right
      && right!=parent
      && parent!=left
    }

    function Repr() : set<Address> {
      {left, right, parent}
    }

    function AsSeq() : seq<Address> {
      [left, right, parent]
    }
  }

  datatype Variables = Variables(
    memtable: Memtable,
    linked: LinkedBetree,
    forestSM: LF.Variables)
  {
    predicate WF() {
      && linked.WF()
      && forestSM.WF()
    }

    predicate Valid() {
      && DisjointForest()
      && BoundedForest()
    }

    // linked diskView and forest diskView should have disjoint addresses
    predicate DisjointForest() {
      && linked.diskView.IsFresh(forestSM.Addresses())
    }

    // buffers in each node should be known to forest
    predicate BoundedForest() {
      && (forall addr, buffer | 
        && addr in linked.diskView.entries 
        && buffer in linked.diskView.entries[addr].buffers 
        :: buffer in forestSM.forest.trees)
    }
  }

  // TODO(jonh): SO much copypasta from PivotBetree! Library, paramaterize child mechanism?
  datatype QueryReceiptLine = QueryReceiptLine(
    linked: LinkedBetree,
    result: Message)
  {
    predicate WF()
    {
      && result.Define?
    }
  }

  datatype QueryReceipt = QueryReceipt(
    key: Key,
    linked: LinkedBetree,
    forest: LF.LinkedForest,
    lines: seq<QueryReceiptLine>)
  {
    predicate Structure()
    {
      && 0 < |lines|
      && lines[0].linked == linked
      && (forall i:nat | i < |lines| :: lines[i].linked.WF())
      && (forall i:nat | i < |lines| :: lines[i].linked.root.Some? <==> i < |lines|-1)
      && (forall i:nat | i < |lines| :: lines[i].linked.diskView == linked.diskView)
      && Last(lines).result == Define(DefaultValue())
      && linked.Acyclic()
      && forest.WF() 
    }

    function Node(i: nat) : (out:BetreeNode)
      requires Structure()
      requires i < |lines| - 1  // last line is None ptr
      ensures out.WF()
    {
      lines[i].linked.Root()
    }

    predicate AllLinesWF()
    {
      && Structure()
      && (forall i:nat | i < |lines| :: lines[i].WF())
      && (forall i:nat | i < |lines| :: lines[i].linked.Acyclic())
      && (forall i:nat | i < |lines|-1 :: Node(i).KeyInDomain(key))
      && (forall i:nat, buffer | i < |lines|-1 && buffer in Node(i).buffers :: forest.ValidTree(buffer))
    }

    predicate ChildLinkedAt(i: nat)
      requires AllLinesWF()
      requires i < |lines|-1
    {
      lines[i+1].linked.root == Node(i).ChildPtr(key)
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
      && this.linked == linked
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
    && v' == v.(
        memtable := v.memtable.ApplyPuts(lbl.puts)
      )
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
    && lbl.forest == Stamped(v.forestSM.forest, v.memtable.seqEnd)
    && v' == v
  }

  type PathAddrs = seq<Address>

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
      && linked.Acyclic()
      && linked.HasRoot()
      && linked.Root().KeyInDomain(key)
      && (0 < depth ==> linked.Root().IsIndex())
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

    // Returns the address of all the nodes on the path, from root up to and including target
    function AddrsOnPath() : set<Address> 
      requires Valid()
      decreases depth
    {
      if depth == 0 then {}
      else Subpath().AddrsOnPath() + {linked.root.value}
    }

    predicate CanSubstitute(replacement: LinkedBetree, pathAddrs: PathAddrs)
    {
      && Valid()
      && Target().HasRoot() // redundant with "path must lead to a non-nil node"?
      && replacement.WF()
      && replacement.HasRoot()
      && replacement.Root().MyDomain() == Target().Root().MyDomain()
      && depth == |pathAddrs|
      && linked.diskView.IsSubsetOf(replacement.diskView)
    }

    lemma CanSubstituteSubpath(replacement: LinkedBetree, pathAddrs: PathAddrs)
      requires CanSubstitute(replacement, pathAddrs)
      requires 0 < depth
      ensures Subpath().CanSubstitute(replacement, pathAddrs[1..])
    {}

    function Substitute(replacement: LinkedBetree, pathAddrs: PathAddrs) : (out: LinkedBetree)
      requires CanSubstitute(replacement, pathAddrs)
      decreases depth, 1
    {
      if depth == 0
      then replacement
      else
        var node := linked.Root();
        CanSubstituteSubpath(replacement, pathAddrs);
        var subtree := Subpath().Substitute(replacement, pathAddrs[1..]);
        var newChildren := node.children[Route(node.pivotTable, key) := subtree.root];
        var newNode := BetreeNode(node.buffers, node.pivotTable, newChildren, node.activeBufferRanges);
        var newDiskView := subtree.diskView.ModifyDisk(pathAddrs[0], newNode);
        LinkedBetree(GenericDisk.Pointer.Some(pathAddrs[0]), newDiskView)
    }
  }

  function InsertInternalFlushMemtableReplacement(oldRoot: LinkedBetree, memtableTree: Address, newRootAddr:Address) : (out: LinkedBetree)
    requires oldRoot.WF()
  {
    var root' := 
      if oldRoot.HasRoot()
      then oldRoot.Root().PushBufferStack(memtableTree)
      else BetreeNode([memtableTree], TotalPivotTable(), [None], [0]);

    var dv' := oldRoot.diskView.ModifyDisk(newRootAddr, root');
    LinkedBetree(Pointer.Some(newRootAddr), dv')
  }

  predicate InternalFlushMemtable(v: Variables, v': Variables, lbl: TransitionLabel, step: Step)
  {
    && v.WF()
    && v.Valid()
    && step.WF()
    && lbl.InternalAllocationsLabel?
    && step.InternalFlushMemtableStep?
    && assert step.branch.I().WF() by { step.branch.WFI( step.branch.I() ); } // TODO: revisit
    && step.branch.I().I() == v.memtable.buffer

    && lbl.addrs == [step.newRootAddr] + step.branch.AddressesFromRoot() // TODO: revisit
    // Subway Eat Fresh!
    && v.linked.diskView.IsFresh({step.newRootAddr})
    && v.linked.diskView.IsFresh(step.branch.diskView.Addresses())
    && v.forestSM.forest.diskView.IsFresh({step.newRootAddr})
    // && v.linked.diskView.IsFresh(step.branch.Addresses()) // captured in next step

    && v'.linked == InsertInternalFlushMemtableReplacement(v.linked, step.branch.root, step.newRootAddr).BuildTightTree()
    && v'.memtable == v.memtable.Drain()
    && LF.Next(v.forestSM, v'.forestSM, LF.AddTreeLabel(step.branch))
  }

  function InsertGrowReplacement(oldRoot: LinkedBetree, newRootAddr:Address) : (out: LinkedBetree)
    requires oldRoot.WF()
  {
    // The new root node
    var root' := BetreeNode([], TotalPivotTable(), [oldRoot.root], [0]);
    // The new diskview
    var dv' := oldRoot.diskView.ModifyDisk(newRootAddr, root');
    LinkedBetree(Pointer.Some(newRootAddr), dv')
  }

  predicate InternalGrow(v: Variables, v': Variables, lbl: TransitionLabel, step: Step)
  {
    && v.WF()
    && step.WF()
    && lbl.InternalAllocationsLabel?
    && step.InternalGrowStep?
    && lbl.addrs == [step.newRootAddr]
    // Subway Eat Fresh!
    && v.linked.diskView.IsFresh({step.newRootAddr})
    && v'.linked == InsertGrowReplacement(v.linked, step.newRootAddr).BuildTightTree()
    && v'.memtable == v.memtable  // UNCHANGED
    && v'.forestSM == v.forestSM  // UNCHANGED
  }

//   predicate IsSplit(linked: LinkedBetree, linked': LinkedBetree, childIdx: nat, splitKey: Key)
//   {
//     && linked.WF()
//     && linked'.WF()
//     && linked.HasRoot()
//     && linked'.HasRoot()
//     && linked'.diskView.AgreesWithDisk(linked.diskView)
//     && var root := linked.Root();
//     && var root' := linked'.Root();

//     && root.ValidChildIndex(childIdx)
//     && PivotInsertable(root.pivotTable, childIdx, splitKey)
//     && 0 < childIdx < NumBuckets(root.pivotTable) // Split can't extend domain of this node.
//     && var oldChildPtr := root.children[childIdx];
//     && oldChildPtr.Some?

//     // Parent adds splitKey pivot; replaces child at childIdx with two children
//     && root'.ValidChildIndex(childIdx+1)  // obvious once we have replace1with2, but we're not there yet
//     && var leftChildPtr := root'.children[childIdx];
//     && var rightChildPtr := root'.children[childIdx+1];
//     && root' == root.(
//       pivotTable := InsertPivot(root.pivotTable, childIdx, splitKey),

//       // replace1with2 is just telling us about the structure of
//       // root'.children: the prefix and suffix are identical, and the new left
//       // & right child ptrs appear where childIdx once was. But it *doesn't*
//       // say anything about the value of leftChildPtr (resp. rightChildPtr),
//       // since we fetched those out of root'.children in the var statement
//       // above. That's a "clever" trick to leave nondeterminism that says we
//       // don't care what the actual values of those pointers are.
//       children := replace1with2(root.children, leftChildPtr, rightChildPtr, childIdx)
//       )

//     // Children get correspending slices
//     && leftChildPtr.Some?
//     && rightChildPtr.Some?
//     && var oldChild := linked.diskView.Get(oldChildPtr);
//     && var leftChild := linked'.diskView.Get(leftChildPtr);
//     && var rightChild := linked'.diskView.Get(rightChildPtr);
//     && leftChild == oldChild.ApplyFilter(Domain(root.pivotTable[childIdx-1], Element(splitKey)))
//     && rightChild == oldChild.ApplyFilter(Domain(Element(splitKey), root.pivotTable[childIdx]))

//     // TODO(jonh): Say, ApplyFilter only affects buffers, but we also need to
//     // carve up the pivot tables and children! ...in PivotBetree, too.
//   }

//   predicate InternalSplit(v: Variables, v': Variables, lbl: TransitionLabel, step: Step)
//   {
//     && v.WF()
//     && lbl.InternalAllocationsLabel?
//     && step.InternalSplitStep?
//     && lbl.addrs == step.pathAddrs + step.newAddrs.AsSeq()
//     && step.WF()
//     && step.path.linked == v.linked
//     && v.linked.diskView.IsFresh(step.newAddrs.Repr() + Set(step.pathAddrs))
//     && step.path.Target().CanSplitParent(step.request)
//     && var replacement := step.path.Target().SplitParent(step.request, step.newAddrs);
//     && assert step.path.CanSubstitute(replacement, step.pathAddrs) by {
//         step.path.Target().SplitParentCanSubstitute(step.request, step.newAddrs);
//       } true
//     && v'.linked == step.path.Substitute(replacement, step.pathAddrs).BuildTightTree()
//     && v'.memtable == v.memtable  // UNCHANGED
//   }

//   function InsertFlushReplacement(target: LinkedBetree, childIdx:nat, targetAddr: Address, targetChildAddr: Address) : (out: LinkedBetree)
//     requires target.WF()
//     requires target.HasRoot()
//     requires target.Root().OccupiedChildIndex(childIdx)
//   {
//     var root := target.Root();
//     var keepKeys := AllKeys() - root.DomainRoutedToChild(childIdx).KeySet();
//     var keptBuffers := root.buffers.ApplyFilter(keepKeys);
//     var movedBuffers := root.buffers.ApplyFilter(root.DomainRoutedToChild(childIdx).KeySet());
//     // BetreeNode of the new child, to be stored at targetChildAddr in the diskview
//     var subroot := target.diskView.Get(root.children[childIdx]);
//     var subroot' := BetreeNode(subroot.buffers.PushBufferStack(movedBuffers), subroot.pivotTable, subroot.children);

//     // BetreeNode of the new root, to be stored at targetAddr in the diskview
//     var children' := root.children[childIdx := Pointer.Some(targetChildAddr)];
//     var root' := BetreeNode(keptBuffers, root.pivotTable, children');

//     // The new diskview
//     var dv' := target.diskView.ModifyDisk(targetAddr, root').ModifyDisk(targetChildAddr, subroot');
//     LinkedBetree(Pointer.Some(targetAddr), dv')
//   }

//   predicate InternalFlush(v: Variables, v': Variables, lbl: TransitionLabel, step: Step)
//   {
//     && v.WF()
//     && step.WF()
//     && lbl.InternalAllocationsLabel?
//     && step.InternalFlushStep?
//     && lbl.addrs == step.pathAddrs + [step.targetAddr, step.targetChildAddr]
//     && step.path.linked == v.linked
//     && step.path.Valid()
//     && step.path.Target().Root().OccupiedChildIndex(step.childIdx)  // the downstream child must exist
//     && var replacement := InsertFlushReplacement(step.path.Target(), step.childIdx, step.targetAddr, step.targetChildAddr);
//     && step.path.CanSubstitute(replacement, step.pathAddrs)
//     // Subway Eat Fresh!
//     && v.linked.diskView.IsFresh({step.targetAddr, step.targetChildAddr} + Set(step.pathAddrs))
//     && v'.linked == step.path.Substitute(replacement, step.pathAddrs).BuildTightTree()
//     && v'.memtable == v.memtable  // UNCHANGED
//   }

//   // target is the root node before it is compacted.
//   // InsertReplacement returns a LinkedBetree that has the diskview of target with replacement placed at
//   // the replacementAddr
//   function InsertCompactReplacement(target: LinkedBetree, compactedBuffers: BufferStack, replacementAddr: Address) : (out: LinkedBetree)
//     requires target.WF()
//     requires target.HasRoot()
//     requires target.Root().buffers.Equivalent(compactedBuffers)
//     requires target.diskView.IsFresh({replacementAddr})
//     ensures target.diskView.IsSubsetOf(out.diskView)
//     ensures out.diskView.entries.Keys == target.diskView.entries.Keys + {replacementAddr}
//     ensures out.WF()   // prereq to MyDomain()
//     ensures out.HasRoot() && out.Root().MyDomain() == target.Root().MyDomain()
//   {
//     var root := target.Root();
//     var newRoot := BetreeNode(compactedBuffers, root.pivotTable, root.children);
//     var newDiskView := target.diskView.ModifyDisk(replacementAddr, newRoot);
//     var out := LinkedBetree(GenericDisk.Pointer.Some(replacementAddr), newDiskView);
//     out
//   }

//   predicate InternalCompact(v: Variables, v': Variables, lbl: TransitionLabel, step: Step)
//   {
//     && v.WF()
//     && step.WF()
//     && lbl.InternalAllocationsLabel?
//     && step.InternalCompactStep?
//     && lbl.addrs == step.pathAddrs + [step.targetAddr]
//     && step.path.linked == v.linked
//     && step.path.Valid()
//     && step.path.Target().Root().buffers.Equivalent(step.compactedBuffers)
//     // Subway Eat Fresh!
//     && v.linked.diskView.IsFresh({step.targetAddr} + Set(step.pathAddrs))
//     && v'.linked == step.path.Substitute(
//         InsertCompactReplacement(step.path.Target(), step.compactedBuffers, step.targetAddr),
//         step.pathAddrs
//     ).BuildTightTree()
//     && v'.memtable == v.memtable  // UNCHANGED
//   }

//   predicate InternalNoOp(v: Variables, v': Variables, lbl: TransitionLabel)
//   {
//     && lbl.InternalLabel?
//     && v.WF()
//     && v' == v
//   }

//   // public:

//   predicate Init(v: Variables, stampedBetree: StampedBetree)
//   {
//     && v == Variables(EmptyMemtable(stampedBetree.seqEnd), stampedBetree.value)
//   }

  datatype Step =
      QueryStep(receipt: QueryReceipt)
    | PutStep()
    | QueryEndLsnStep()
    | FreezeAsStep()
    // newRootAddr is the new address allocated for the new root
    | InternalGrowStep(newRootAddr: Address)

//     | InternalSplitStep(path: Path, request: SplitRequest, newAddrs: SplitAddrs, pathAddrs: PathAddrs)
//       // request describes how the split applies (to an Index or Leaf); newAddrs are the new page addresses
    | InternalFlushMemtableStep(newRootAddr: Address, branch: LB.LinkedBranch)
//     | InternalFlushStep(path: Path, childIdx: nat, targetAddr: Address, targetChildAddr: Address, pathAddrs: PathAddrs)
//       // targetAddr is the fresh address at which new node is placed, and targetChildAddr is for the new child receiving the flush
//       // pathAddrs is the new addresses to place all its ancestors, used in substitution

//     | InternalCompactStep(path: Path, compactedBuffers: BufferStack, targetAddr: Address, pathAddrs: PathAddrs)
//       // targetAddr is the fresh address at which compactedNode is placed. pathAddrs is the new addresses to place all its ancestors
//     | InternalNoOpStep()
  {
    predicate WF() {
      match this {
        case QueryStep(receipt) => receipt.Valid()
        case InternalFlushMemtableStep(_, branch) => 
          && branch.Acyclic()
        // case InternalSplitStep(path, request, newAddrs, pathAddrs) =>
//           && path.Valid()
//           && path.depth == |pathAddrs|
//           && SeqHasUniqueElems(pathAddrs)
//           && path.Target().Root().ValidChildIndex(request.childIdx)
//           && path.Target().CanSplitParent(request)
//           && newAddrs.HasUniqueElems()
//           && newAddrs.Repr() !! Set(pathAddrs)
//         case InternalFlushStep(_, _, targetAddr, targetChildAddr, pathAddrs) =>
//           && path.Valid()
//           && path.Target().Root().ValidChildIndex(childIdx)
//           && path.depth == |pathAddrs|
//           && SeqHasUniqueElems(pathAddrs)
//           && {targetAddr, targetChildAddr} !! Set(pathAddrs)
//           && targetAddr != targetChildAddr
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
//       case InternalSplitStep(_, _, _, _) => InternalSplit(v, v', lbl, step)
//       case InternalFlushMemtableStep(_) => InternalFlushMemtable(v, v', lbl, step)
//       case InternalFlushStep(_, _, _, _, _) => InternalFlush(v, v', lbl, step)
//       case InternalCompactStep(_, _, _, _) => InternalCompact(v, v', lbl, step)
//       case InternalNoOpStep() => InternalNoOp(v, v', lbl)
//     }
//   }

//   predicate Next(v: Variables, v': Variables, lbl: TransitionLabel) {
//     exists step: Step :: NextStep(v, v', lbl, step)
//   }
}
