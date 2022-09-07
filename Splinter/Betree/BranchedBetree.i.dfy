// Copyright 2018-2021 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, and University of Washington
// SPDX-License-Identifier: BSD-2-Clause

include "Domain.i.dfy"
include "Branches.i.dfy"
include "SplitRequest.i.dfy"
include "LinkedBetree.i.dfy"
include "../../lib/Buckets/BoundedPivotsLib.i.dfy"
include "../../lib/Base/mathematics.i.dfy"
include "../Journal/GenericDisk.i.dfy"

// This module deals with 
// 1. Concretize buffer implementation with Forest (seqs of B+ tree)
// 2. Filter should be implicitly tracked by pivot table (no more apply filters)
// 3. Track active buffers for each child, as we don't want to visit a buffer that is flushed to a child already

module BranchedBetreeMod
{
  import opened BoundedPivotsLib
  import opened DomainMod
  import opened GenericDisk
  import opened LSNMod
  import opened MemtableMod
  import opened MsgHistoryMod
  import opened Options
  import opened Sequences
  import opened StampedMod
  import opened Upperbounded_Lexicographic_Byte_Order_Impl
  import opened Upperbounded_Lexicographic_Byte_Order_Impl.Ord
  import opened KeyType
  import opened ValueMessage
  import opened Maps
  import TotalKMMapMod
  import opened SplitRequestMod

  import M = Mathematics
  import L = LinkedBetreeMod // to share some node independent structure
  import LB = LinkedBranchMod
  import opened BranchesMod

  type Pointer = GenericDisk.Pointer
  type Address = GenericDisk.Address
  type StampedBetree = Stamped<BranchedBetree>

  function EmptyBranchedBetree() : (out: BranchedBetree)
  {
    BranchedBetree(None, EmptyDisk(), EmptyBranches())
  }

  function EmptyImage() : StampedBetree
  {
    Stamped(EmptyBranchedBetree(), 0)
  }

  type Element = Upperbounded_Lexicographic_Byte_Order_Impl.Ord.Element

  datatype TransitionLabel =
      QueryLabel(endLsn: LSN, key: Key, value: Value)
    | PutLabel(puts: MsgHistory)
    | QueryEndLsnLabel(endLsn: LSN)
    | FreezeAsLabel(branched: StampedBetree)
     // Internal-x labels refine to no-ops at the abstract spec
    | InternalAllocationsLabel(treeAddrs: seq<Address>, branchAddrs: seq<Address>)  // for steps that involve allocating new pages
    | InternalLabel()   // Local No-op label


  datatype BetreeNode = BetreeNode(
    // Addresses in buffers belong to the Branches disk
    buffers: seq<Address>, 
    pivotTable: PivotTable,
    // Addresses in children belong to the Betree disk
    children: seq<Pointer>,
    // Once a buffer is flushed to a child, we no longer want to query
    // the buffer for keys in the child's domain, making the buffer
    // inactive for that child. Each child may have a different set of buffers
    // flushed to them, so we need to track the start of valid buffers for each child.
    // This is a parallel data structure to the children array.
    activeBufferRanges: seq<nat> 
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

    function PushBufferStack(addrs: seq<Address>) : (out: BetreeNode)
      requires WF()
      ensures out.WF()
    {
      BetreeNode(buffers + addrs, pivotTable, children, activeBufferRanges)
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

    function ChildPtr(key: Key) : Pointer
      requires KeyInDomain(key)
    {
      children[Route(pivotTable, key)]
    }

    // returns the start of active buffer ranges for a key
    function ActiveBuffersForKey(key: Key) : (i: nat)
      requires KeyInDomain(key)
    {
      activeBufferRanges[Route(pivotTable, key)]
    }

    // function LargestInactiveRange(count: nat) : (activeStart: nat) 
    //   requires WF()
    //   requires count <= |activeBufferRanges|
    //   ensures activeStart <= |buffers|
    //   ensures (forall i:nat | i < count :: activeStart <= activeBufferRanges[i])
    // {
    //   if count == 0 then 0
    //   else if count == 1 then activeBufferRanges[count-1]
    //   else M.min(activeBufferRanges[count-1], LargestInactiveRange(count-1))
    // }

    function TruncateActiveRange(newStart: nat, count: nat) : seq<nat>
      requires count <= |activeBufferRanges|
      requires (forall i:nat | i < |activeBufferRanges| :: newStart <= activeBufferRanges[i]) 
    {
      if count == 0 then []
      else TruncateActiveRange(newStart, count-1) + [activeBufferRanges[count-1]-newStart] 
    }

    function TruncateBuffers(newStart: nat) : BetreeNode
      requires WF()
      requires newStart <= |buffers|
      requires (forall i:nat | i < |activeBufferRanges| :: newStart <= activeBufferRanges[i])
      ensures WF()
    {
      BetreeNode(buffers[newStart..], pivotTable, children, TruncateActiveRange(newStart, |activeBufferRanges|))
    }

    function CompactActiveRange(compactStart: nat, compactEnd: nat, count: nat) : (out: seq<nat>)
      requires WF()
      requires compactStart < compactEnd <= |buffers|
      requires count <= |activeBufferRanges|
      ensures |out| == |activeBufferRanges[..count]|
      ensures (forall i:nat | i < |out| :: out[i] <= |buffers| - (compactEnd-compactStart-1))
    {
      if count == 0 then []
      else (
        var range := activeBufferRanges[count-1];
        var range' := 
            if range < compactStart then range
            else if range < compactEnd then compactStart
            else range - (compactEnd - compactStart - 1);

        CompactActiveRange(compactStart, compactEnd, count-1) + [range']
      )
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

    predicate CompactedBranchEquivalence(branches: Branches, compactStart: nat, compactEnd: nat, compactedBranch: LB.LinkedBranch)
      requires WF()
      requires branches.WF()
      requires compactedBranch.Acyclic()
      requires compactedBranch.AllKeysInRange()
      requires compactedBranch.TightDiskView()
      requires compactStart < compactEnd <= |buffers|
      requires forall i:nat | compactStart <= i < compactEnd :: branches.ValidBranch(buffers[i])
    {
      && (forall key | KeyInDomain(key) && ActiveBuffersForKey(key) < compactEnd ::
        && var result := if compactedBranch.Query(key).Some? then compactedBranch.Query(key).value else Update(NopDelta());
        && var start := if ActiveBuffersForKey(key) <= compactStart then compactStart else ActiveBuffersForKey(key);
        && branches.Query(key, buffers[start..compactEnd]) == result)
      && (forall key | !KeyInDomain(key) || ActiveBuffersForKey(key) >= compactEnd :: compactedBranch.Query(key).None?)
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
  datatype BranchedBetree = BranchedBetree(
    root: Pointer,
    diskView: DiskView,
    branches: Branches  // branches of betree nodes, not part of the betree therefore not tracked the diskview
  ) {
    predicate WF() {
      && branches.WF()
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

    predicate Valid() {
      && DisjointForest()
      && BoundedForest()
    }

    // linked diskView and forest diskView should have disjoint addresses
    predicate DisjointForest() {
      && diskView.IsFresh(branches.diskView.AllAddresses())
    }

    // buffers in each node should be known to forest
    predicate BoundedForest() {
      && (forall addr, buffer | 
        && addr in diskView.entries 
        && buffer in diskView.entries[addr].buffers 
        :: buffer in branches.roots)
    }

    predicate IsFresh(addrs: set<Address>) {
      && diskView.IsFresh(addrs)
      && branches.diskView.IsFresh(addrs)
    }
   
    function ChildAtIdx(idx: nat) : BranchedBetree
      requires WF()
      requires HasRoot()
      requires Root().ValidChildIndex(idx)
    {
      BranchedBetree(Root().children[idx], diskView, branches)
    }

    function ChildForKey(key: Key) : BranchedBetree
      requires HasRoot()
      requires Root().KeyInDomain(key)
      ensures Valid() ==> Valid()
    {
      BranchedBetree(Root().ChildPtr(key), diskView, branches)
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

    // throw away disk addrs that are no longer reachable through the root
    function BuildTightTree() : (out: BranchedBetree)
      ensures out.diskView.IsSubsetOf(diskView)
    {
      if ! Acyclic() then
        // Need this case because at the state machine I don't have proof that after an
        // operation, that the new state is acyclic
        this
      else
        var tightDv := DiskView.DiskView(MapRestrict(diskView.entries, ReachableAddrs()));
        BranchedBetree(root, tightDv, branches)
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

    function SplitParent(request: SplitRequest, newAddrs: L.SplitAddrs) : (out: BranchedBetree)
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
      BranchedBetree(Pointer.Some(newAddrs.parent), dv', branches)
    }

    lemma SplitParentCanSubstitute(request: SplitRequest, newAddrs: L.SplitAddrs)
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

  type PathAddrs = seq<Address>

  datatype Path = Path(branched: BranchedBetree, key: Key, depth: nat)
  {
    function Subpath() : (out: Path)
      requires 0 < depth
      requires branched.HasRoot()
      requires branched.Root().KeyInDomain(key)
      ensures branched.branches == out.branched.branches
    {
      Path(branched.ChildForKey(key), key, depth-1)
    }

    predicate Valid()
      decreases depth
    {
      && branched.Acyclic()
      && branched.Valid()  // TODO(Jialin): revisit
      && branched.HasRoot()
      && branched.Root().KeyInDomain(key)
      && (0 < depth ==> branched.Root().IsIndex())
      && (0 < depth ==> Subpath().Valid())  // implies path must lead to a non-nil node
    }

    function Target() : (out: BranchedBetree)
      requires Valid()
      ensures out.WF()
      ensures out.root.Some?
      ensures out.diskView == branched.diskView
      ensures out.branches == branched.branches
      ensures out.HasRoot() ==> out.root.value in out.diskView.entries
      decreases depth
    {
      if 0 == depth
      then branched
      else Subpath().Target()
    }

    // Returns the address of all the nodes on the path, from root up to and including target
    function AddrsOnPath() : set<Address> 
      requires Valid()
      decreases depth
    {
      if depth == 0 then {}
      else Subpath().AddrsOnPath() + {branched.root.value}
    }

    predicate CanSubstitute(replacement: BranchedBetree, pathAddrs: PathAddrs)
    {
      && Valid()
      && Target().HasRoot() // redundant with "path must lead to a non-nil node"?
      && replacement.WF()
      && replacement.HasRoot()
      && replacement.Root().MyDomain() == Target().Root().MyDomain()
      && depth == |pathAddrs|
      && branched.diskView.IsSubsetOf(replacement.diskView)
    }

    lemma CanSubstituteSubpath(replacement: BranchedBetree, pathAddrs: PathAddrs)
      requires CanSubstitute(replacement, pathAddrs)
      requires 0 < depth
      ensures Subpath().CanSubstitute(replacement, pathAddrs[1..])
    {}

    function Substitute(replacement: BranchedBetree, pathAddrs: PathAddrs) : (out: BranchedBetree)
      requires CanSubstitute(replacement, pathAddrs)
      decreases depth, 1
    {
      if depth == 0
      then replacement
      else
        var node := branched.Root();
        CanSubstituteSubpath(replacement, pathAddrs);
        var subtree := Subpath().Substitute(replacement, pathAddrs[1..]);
        var newChildren := node.children[Route(node.pivotTable, key) := subtree.root];
        var newNode := BetreeNode(node.buffers, node.pivotTable, newChildren, node.activeBufferRanges);
        var newDiskView := subtree.diskView.ModifyDisk(pathAddrs[0], newNode);
        BranchedBetree(GenericDisk.Pointer.Some(pathAddrs[0]), newDiskView, branched.branches)
    }
  }

  // TODO(jonh): SO much copypasta from PivotBetree! Library, paramaterize child mechanism?
  datatype QueryReceiptLine = QueryReceiptLine(
    branched: BranchedBetree,
    result: Message)
  {
    predicate WF()
    {
      && result.Define?
    }
  }

  datatype QueryReceipt = QueryReceipt(
    key: Key,
    branched: BranchedBetree,
    lines: seq<QueryReceiptLine>)
  {
    predicate Structure()
    {
      && 0 < |lines|
      && lines[0].branched == branched
      && (forall i:nat | i < |lines| :: lines[i].branched.WF())
      && (forall i:nat | i < |lines| :: lines[i].branched.root.Some? <==> i < |lines|-1)
      && (forall i:nat | i < |lines| :: lines[i].branched.diskView == branched.diskView)
      && (forall i:nat | i < |lines| :: lines[i].branched.branches == branched.branches)      
      && Last(lines).result == Define(DefaultValue())
      && branched.Acyclic()
      && branched.Valid()
      // && branched.WF()
    }

    function Node(i: nat) : (out:BetreeNode)
      requires Structure()
      requires i < |lines| - 1  // last line is None ptr
      ensures out.WF()
    {
      lines[i].branched.Root()
    }

    predicate AllLinesWF()
    {
      && Structure()
      && (forall i:nat | i < |lines| :: lines[i].WF())
      // Note(Jialin): start
      && (forall i:nat | i < |lines| :: lines[i].branched.Acyclic())
      && (forall i:nat | i < |lines| :: lines[i].branched.Valid())
      // Note(Jialin): end
      && (forall i:nat | i < |lines|-1 :: Node(i).KeyInDomain(key))
      && (forall i:nat, buffer | i < |lines|-1 && buffer in Node(i).buffers :: branched.branches.ValidBranch(buffer))
    }

    predicate ChildLinkedAt(i: nat)
      requires AllLinesWF()
      requires i < |lines|-1
    {
      lines[i+1].branched.root == Node(i).ChildPtr(key)
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
      && var start := Node(i).ActiveBuffersForKey(key); // only query on a child's active range
      && var msg := branched.branches.Query(key, Node(i).buffers[start..]);
      && lines[i].result == Merge(msg, ResultAt(i+1))
    }

    predicate Valid()
    {
      && Structure()
      && AllLinesWF()
      && (forall i:nat | i < |lines| - 1 :: ChildLinkedAt(i))
      && (forall i:nat | i < |lines| - 1 :: ResultLinkedAt(i))
    }

    predicate ValidFor(branched: BranchedBetree, key: Key)
    {
      && Valid()
      && this.branched == branched
      && this.key == key
    }

    function Result() : Message
      requires Structure()
    {
      ResultAt(0)
    }
  }

  datatype Variables = Variables(memtable: Memtable, branched: BranchedBetree) {
    predicate WF() {
      && branched.WF()
    }
  }

  predicate Query(v: Variables, v': Variables, lbl: TransitionLabel, receipt: QueryReceipt)
  {
    && lbl.QueryLabel?
    && lbl.endLsn == v.memtable.seqEnd
    && receipt.ValidFor(v.branched, lbl.key)
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
    && lbl.branched == Stamped(v.branched, v.memtable.seqEnd)
    && v' == v
  }

  function InsertInternalFlushMemtableReplacement(branched: BranchedBetree, newBranch: LB.LinkedBranch, newRootAddr:Address) : (out: BranchedBetree)
    requires branched.WF()
    requires newBranch.Acyclic()
    requires newBranch.TightDiskView()
    requires branched.IsFresh(newBranch.ReachableAddrs())
  {
    var root' := 
      if branched.HasRoot()
      then branched.Root().PushBufferStack([newBranch.root])
      else BetreeNode([newBranch.root], TotalPivotTable(), [None], [0]);

    var dv' := branched.diskView.ModifyDisk(newRootAddr, root');
    BranchedBetree(Pointer.Some(newRootAddr), dv', branched.branches.AddBranch(newBranch))
  }

  predicate InternalFlushMemtable(v: Variables, v': Variables, lbl: TransitionLabel, step: Step)
  {
    && v.WF()
    && step.WF()
    && lbl.InternalAllocationsLabel?
    && step.InternalFlushMemtableStep?
    && (step.branch.I().WF() ==> step.branch.I().I() == v.memtable.buffer) // TODO: revisit

    // Allocation validation
    && lbl.treeAddrs == [ step.newRootAddr ]
    && Set(lbl.branchAddrs) == step.branch.ReachableAddrs()

    // Subway Eat Fresh!
    && v.branched.IsFresh({step.newRootAddr})
    && v.branched.IsFresh(step.branch.ReachableAddrs())
    && v'.branched == InsertInternalFlushMemtableReplacement(v.branched, step.branch, step.newRootAddr).BuildTightTree()
    && v'.memtable == v.memtable.Drain()
  }

  function InsertGrowReplacement(branched: BranchedBetree, newRootAddr:Address) : (out: BranchedBetree)
    requires branched.WF()
  {
    // The new root node
    var root' := BetreeNode([], TotalPivotTable(), [branched.root], [0]);
    // The new diskview
    var dv' := branched.diskView.ModifyDisk(newRootAddr, root');
    BranchedBetree(Pointer.Some(newRootAddr), dv', branched.branches)
  }

  predicate InternalGrow(v: Variables, v': Variables, lbl: TransitionLabel, step: Step)
  {
    && v.WF()
    && step.WF()
    && lbl.InternalAllocationsLabel?
    && step.InternalGrowStep?
    && lbl.treeAddrs == [step.newRootAddr]
    && lbl.branchAddrs == []
    // Subway Eat Fresh!
    && v.branched.IsFresh({step.newRootAddr})
    && v'.branched == InsertGrowReplacement(v.branched, step.newRootAddr).BuildTightTree()
    && v'.memtable == v.memtable  // UNCHANGED
  }

  predicate InternalSplit(v: Variables, v': Variables, lbl: TransitionLabel, step: Step)
  {
    && v.WF()
    && lbl.InternalAllocationsLabel?
    && step.InternalSplitStep?
    && lbl.treeAddrs == step.pathAddrs + step.newAddrs.AsSeq()
    && lbl.branchAddrs == []
    && step.WF()
    && step.path.branched == v.branched
    && v.branched.IsFresh(step.newAddrs.Repr() + Set(step.pathAddrs))
    && step.path.Target().CanSplitParent(step.request)
    && var replacement := step.path.Target().SplitParent(step.request, step.newAddrs);
    && assert step.path.CanSubstitute(replacement, step.pathAddrs) by {
        step.path.Target().SplitParentCanSubstitute(step.request, step.newAddrs);}
    && v'.branched == step.path.Substitute(replacement, step.pathAddrs).BuildTightTree()
    && v'.memtable == v.memtable  // UNCHANGED
  }

  function InsertFlushReplacement(target: BranchedBetree, childIdx:nat, targetAddr: Address, targetChildAddr: Address, bufferStart: nat) : (out: BranchedBetree)
    requires target.WF()
    requires target.HasRoot()
    requires target.Root().OccupiedChildIndex(childIdx)
    requires bufferStart <= |target.Root().buffers|
    requires forall i:nat | i < |target.Root().activeBufferRanges| && i != childIdx :: bufferStart <= target.Root().activeBufferRanges[i]
  {
    var root := target.Root();
    var oldRange := root.activeBufferRanges[childIdx];
    var activeBufferRanges' := root.activeBufferRanges[childIdx := |root.buffers|];
  
    var subroot := target.diskView.Get(root.children[childIdx]);
    var subroot' := subroot.PushBufferStack(root.buffers[oldRange..]);

    // BetreeNode of the new root, to be stored at targetAddr in the diskview
    var children' := root.children[childIdx := Pointer.Some(targetChildAddr)];
    var root' := BetreeNode(root.buffers, root.pivotTable, children', activeBufferRanges').TruncateBuffers(bufferStart);

    // The new diskview
    var dv' := target.diskView.ModifyDisk(targetAddr, root').ModifyDisk(targetChildAddr, subroot');
    BranchedBetree(Pointer.Some(targetAddr), dv', target.branches)
  }

  // Flush is responsible for 1. flush buffer to child 2. update the active buffer range for that child 
  // 3. truncate inactive buffers and shift active range when possible
  predicate InternalFlush(v: Variables, v': Variables, lbl: TransitionLabel, step: Step)
  {
    && v.WF()
    && step.WF()
    && lbl.InternalAllocationsLabel?
    && step.InternalFlushStep?

    && lbl.treeAddrs == step.pathAddrs + [step.targetAddr, step.targetChildAddr]
    && lbl.branchAddrs == []
    && step.path.branched == v.branched
    && step.path.Valid()

    && var root := step.path.Target().Root();
    && root.OccupiedChildIndex(step.childIdx)  // the downstream child must exist
    && step.bufferStart <= |root.buffers|
    && (forall i:nat | i < |root.activeBufferRanges| && i != step.childIdx :: step.bufferStart <= root.activeBufferRanges[i]) 
    && var replacement := InsertFlushReplacement(step.path.Target(), step.childIdx, step.targetAddr, step.targetChildAddr, step.bufferStart); // meow
    && step.path.CanSubstitute(replacement, step.pathAddrs)
    
    // Subway Eat Fresh!
    && v.branched.IsFresh({step.targetAddr, step.targetChildAddr} + Set(step.pathAddrs))
    && v'.branched == step.path.Substitute(replacement, step.pathAddrs).BuildTightTree()
    && v'.memtable == v.memtable  // UNCHANGED
  }

  predicate InternalPruneBranches(v: Variables, v': Variables, lbl: TransitionLabel, step: Step)
  {
    && v.WF()
    && step.WF()
    && lbl.InternalLabel?
    && step.InternalPruneBranchesStep?
    && v.branched.branches.ValidBranch(step.rootToRemove)
    && (forall addr | addr in v.branched.diskView.entries :: 
        step.rootToRemove !in v.branched.diskView.entries[addr].buffers) // buffer has no more references

    && v'.branched == v.branched.(branches := v.branched.branches.RemoveBranch(step.rootToRemove))
    && v'.memtable == v.memtable
  }

  // @target: the root node before it is compacted
  // @compactStart: start index of buffers being compacted
  // @compactEnd: end index of buffers being compacted, exclusive
  // @compactedRoot: compacted branch root address (not in our diskview)
  // InsertReplacement returns a LinkedBetree that has the diskview of target with replacement placed at the replacementAddr
  function InsertCompactReplacement(target: BranchedBetree, compactStart: nat, compactEnd: nat, compactedRoot: Address, replacementAddr: Address) : (out: BranchedBetree)
    requires target.WF()
    requires target.HasRoot()
    requires compactStart < compactEnd <= |target.Root().buffers|
    requires target.diskView.IsFresh({replacementAddr})
    ensures target.diskView.IsSubsetOf(out.diskView)
    ensures out.diskView.entries.Keys == target.diskView.entries.Keys + {replacementAddr}
    ensures out.WF()   // prereq to MyDomain()
    ensures out.HasRoot() && out.Root().MyDomain() == target.Root().MyDomain()
  {
    var root := target.Root();
    var compactedBuffers := root.buffers[0..compactStart] + [ compactedRoot ] + root.buffers[compactEnd..];
    var compactedActiveBufferRanges := root.CompactActiveRange(compactStart, compactEnd, |root.activeBufferRanges|);
    var newRoot := BetreeNode(compactedBuffers, root.pivotTable, root.children, compactedActiveBufferRanges);

    var newDiskView := target.diskView.ModifyDisk(replacementAddr, newRoot);
    var out := BranchedBetree(GenericDisk.Pointer.Some(replacementAddr), newDiskView, target.branches);
    out
  }

  predicate InternalCompact(v: Variables, v': Variables, lbl: TransitionLabel, step: Step)
  {
    && v.WF()
    && v.branched.Valid() // can reduce to ValidTree(buffers[compactStart..compactEnd]) if needed
    && step.WF()
    && step.InternalCompactStep?
    
    // allocation validation
    && lbl.InternalAllocationsLabel?
    && lbl.treeAddrs == step.pathAddrs + [ step.targetAddr ]
    && Set(lbl.branchAddrs) == step.compactedBranch.ReachableAddrs()
    && step.path.branched == v.branched

    // Subway Eat Fresh!
    && v.branched.IsFresh(Set(lbl.treeAddrs + lbl.branchAddrs))
    && var tmp := step.path.Substitute(
        InsertCompactReplacement(step.path.Target(), step.compactStart, step.compactEnd, step.compactedBranch.root, step.targetAddr),
        step.pathAddrs).BuildTightTree();

    && v'.branched == tmp.(branches := v.branched.branches.AddBranch(step.compactedBranch))
    && v'.memtable == v.memtable  // UNCHANGED
  }

  predicate InternalNoOp(v: Variables, v': Variables, lbl: TransitionLabel)
  {
    && lbl.InternalLabel?
    && v.WF()
    && v' == v
  }

  // public:

  // we might want to let forestSM take a step itself
  predicate Init(v: Variables, stampedBetree: StampedBetree)
  {
    && v == Variables(EmptyMemtable(stampedBetree.seqEnd), stampedBetree.value)
  }

  datatype Step =
      QueryStep(receipt: QueryReceipt)
    | PutStep()
    | QueryEndLsnStep()
    | FreezeAsStep()
      // newRootAddr is the new address allocated for the new root
    | InternalGrowStep(newRootAddr: Address)
      // request describes how the split applies (to an Index or Leaf); newAddrs are the new page addresses
    | InternalSplitStep(path: Path, request: SplitRequest, newAddrs: L.SplitAddrs, pathAddrs: PathAddrs)
    | InternalFlushMemtableStep(newRootAddr: Address, branch: LB.LinkedBranch)
      // targetAddr is the fresh address at which new node is placed, and targetChildAddr is for the new child receiving the flush
      // pathAddrs is the new addresses to place all its ancestors, used in substitution
    | InternalFlushStep(path: Path, childIdx: nat, targetAddr: Address, targetChildAddr: Address, pathAddrs: PathAddrs, bufferStart: nat)
    | InternalPruneBranchesStep(rootToRemove: Address)
      // targetAddr is the fresh address at which compacted node is placed. pathAddrs is the new addresses to place all its ancestors
    | InternalCompactStep(path: Path, compactStart: nat, compactEnd: nat, compactedBranch: LB.LinkedBranch, targetAddr: Address, pathAddrs: PathAddrs)
    | InternalNoOpStep()
  {
    predicate WF() {
      match this {
        case QueryStep(receipt) => receipt.Valid()
        case InternalFlushMemtableStep(_, branch) => 
          && branch.Acyclic()
          && branch.TightDiskView()
        case InternalSplitStep(path, request, newAddrs, pathAddrs) =>
          && path.Valid()
          && path.depth == |pathAddrs|
          && SeqHasUniqueElems(pathAddrs)
          && path.Target().Root().ValidChildIndex(request.childIdx)
          && path.Target().CanSplitParent(request)
          && newAddrs.HasUniqueElems()
          && newAddrs.Repr() !! Set(pathAddrs)
        case InternalFlushStep(_, _, targetAddr, targetChildAddr, pathAddrs, _) =>
          && path.Valid()
          && path.Target().Root().ValidChildIndex(childIdx)
          && path.depth == |pathAddrs|
          && SeqHasUniqueElems(pathAddrs)
          && {targetAddr, targetChildAddr} !! Set(pathAddrs)
          && targetAddr != targetChildAddr
        case InternalCompactStep(path, compactStart, compactEnd, compactedBranch, targetAddr, pathAddrs) =>
          && path.Valid()
          && path.depth == |pathAddrs|
          && SeqHasUniqueElems(pathAddrs)
          && {targetAddr} !! Set(pathAddrs)
          && compactedBranch.Acyclic()
          && compactedBranch.TightDiskView()
          && compactedBranch.AllKeysInRange()
          && compactStart < compactEnd <= |path.Target().Root().buffers|
          && path.Target().Root().CompactedBranchEquivalence(path.branched.branches, compactStart, compactEnd, compactedBranch)
        case _ => true
      }
    }
  }

  predicate NextStep(v: Variables, v': Variables, lbl: TransitionLabel, step: Step)
  {
    match step {
      case QueryStep(receipt) => Query(v, v', lbl, receipt)
      case PutStep() => Put(v, v', lbl)
      case QueryEndLsnStep() => QueryEndLsn(v, v', lbl)
      case FreezeAsStep() => FreezeAs(v, v', lbl)
      case InternalGrowStep(_) => InternalGrow(v, v', lbl, step)
      case InternalSplitStep(_, _, _, _) => InternalSplit(v, v', lbl, step)
      case InternalFlushMemtableStep(_,_) => InternalFlushMemtable(v, v', lbl, step)
      case InternalFlushStep(_, _, _, _, _, _) => InternalFlush(v, v', lbl, step)
      case InternalPruneBranchesStep(_) => InternalPruneBranches(v, v', lbl, step)
      case InternalCompactStep(_, _, _, _, _, _) => InternalCompact(v, v', lbl, step)
      case InternalNoOpStep() => InternalNoOp(v, v', lbl)
    }
  }

  predicate Next(v: Variables, v': Variables, lbl: TransitionLabel) {
    exists step: Step :: NextStep(v, v', lbl, step)
  }
}
