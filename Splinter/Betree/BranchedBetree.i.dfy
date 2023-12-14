// Copyright 2018-2021 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, and University of Washington
// SPDX-License-Identifier: BSD-2-Clause

include "Domain.i.dfy"
include "BranchSeq.i.dfy"
include "SplitRequest.i.dfy"
include "LinkedBetree.i.dfy"
include "../../lib/Buckets/BoundedPivotsLib.i.dfy"
include "../../lib/Base/mathematics.i.dfy"
include "../Disk/GenericDisk.i.dfy"

// This module concretizes buffer implementation with Forest (seqs of B+ tree)

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

  import opened BufferMod
  import opened BranchSeqMod
  import opened BufferOffsetsMod
  import opened OffsetMapMod

  type Pointer = GenericDisk.Pointer
  type Address = GenericDisk.Address
  type StampedBetree = Stamped<BranchedBetree>
  type BranchDiskView = LB.DiskView

  function EmptyBranchedBetree() : (out: BranchedBetree)
    ensures out.Acyclic()
  {
    var out := BranchedBetree(None, EmptyDisk(), LB.EmptyDisk());
    assert out.ValidRanking(map[]);
    out
  }

  function EmptyImage() : StampedBetree
  {
    Stamped(EmptyBranchedBetree(), 0)
  }

  type Element = Upperbounded_Lexicographic_Byte_Order_Impl.Ord.Element

  datatype TransitionLabel =
      QueryLabel(endLsn: LSN, key: Key, value: Value)
    | PutLabel(puts: MsgHistory) // 
    | QueryEndLsnLabel(endLsn: LSN)
    | FreezeAsLabel(branched: StampedBetree)
    | InternalLabel()   // Local No-op label

  datatype BetreeNode = BetreeNode(
    branches: BranchSeq,
    pivotTable: PivotTable,
    children: seq<Pointer>,
    flushedOffsets: BufferOffsets
  ) {
    predicate WF() {
      && (BetreeNode? ==>
        && WFPivots(pivotTable)
        && |children| == NumBuckets(pivotTable)
        && |children| == flushedOffsets.Size()
        && flushedOffsets.BoundedBy(branches.Length())
      )
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

    function ExtendBranchSeq(newBranches: BranchSeq) : (out: BetreeNode)
      requires WF()
      ensures out.WF()
    {
      BetreeNode(branches.Extend(newBranches), pivotTable, children, flushedOffsets)
    }

    function ActiveBranchesForKey(key: Key) : (i: nat)
      requires KeyInDomain(key)
    {
      flushedOffsets.Get(Route(pivotTable, key))
    }

    predicate IsLeaf()
    {
      && |children|==1
      && children[0].None?
      && flushedOffsets == BufferOffsets([0]) 
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
      var newLeft := BetreeNode(branches, [pivotTable[0], Element(splitKey)], [None], BufferOffsets([0]));
      var newRight := BetreeNode(branches, [Element(splitKey), pivotTable[1]], [None], BufferOffsets([0]));
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

      var newLeft := BetreeNode(branches, pivotTable[..pivotIdx+1], children[..pivotIdx], flushedOffsets.Slice(0, pivotIdx));
      var newRight := BetreeNode(branches, pivotTable[pivotIdx..], children[pivotIdx..], flushedOffsets.Slice(pivotIdx, flushedOffsets.Size()));
      WFSlice(pivotTable, 0, pivotIdx+1);
      WFSuffix(pivotTable, pivotIdx);
      assert newLeft.WF();
      assert newRight.WF();
      (newLeft, newRight)
    }

    function MakeOffsetMap() : OffsetMap
      requires WF()
      requires BetreeNode?
    {
      OffsetMap(imap k | AnyKey(k) 
      :: if BoundedKey(pivotTable, k) then flushedOffsets.Get(Route(pivotTable, k))
          else branches.Length())
    }
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
    BetreeNode(BranchSeq([]), pivotTable, [None], BufferOffsets([0]))
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

    predicate NondanglingChildPtrs()  // i.e. disk is closed wrt to all the pointers in the nodes on disk
      requires EntriesWF()
    {
      forall addr | addr in entries :: NodeHasNondanglingChildPtrs(entries[addr])
    }

    predicate WF()
    {
      && EntriesWF()
      && NondanglingChildPtrs()
    }

    predicate LinkedChildren()  // i.e. disk is closed wrt to all the pointers in the nodes on disk
      requires WF()
    {
      forall addr | addr in entries :: NodeHasLinkedChildren(entries[addr])
    }

    function Get(ptr: Pointer) : BetreeNode
      // requires WF()
      requires IsNondanglingPointer(ptr)
      requires ptr.Some?
    {
      entries[ptr.value]
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

  // // This is the unit of interpretation: A LinkedBetree has enough info in it to interpret to a PivotBetree.BetreeNode.
  datatype BranchedBetree = BranchedBetree(
    root: Pointer,
    diskView: DiskView,
    branchDiskView: BranchDiskView
  ) {
    predicate WF() {
      && diskView.WF()
      && diskView.IsNondanglingPointer(root)
      // && diskView.IsFresh(branchDiskView.Representation())

      && branchDiskView.WF()
      // && NoDanglingBranchPointers()
      // && AcyclicBranches()
      // && DisjointBranches()
    }

    // Quantified vs Recursive
    predicate NoDanglingBranchPointers() 
      requires Acyclic()
    {
      forall branch | branch in BranchSeqRepresentation() :: branch in branchDiskView.Representation()
    }

    predicate AcyclicBranches() 
      requires Acyclic()
      requires NoDanglingBranchPointers()
    {
      // Acyclic implies all nodes in representation are in branchdiskview
      forall branch | branch in BranchSeqRepresentation() ::  LB.LinkedBranch(branch, branchDiskView).Acyclic()
    }

    predicate DisjointBranches()
      requires Acyclic()
      requires NoDanglingBranchPointers()
      requires AcyclicBranches()
    {
      forall b1, b2 | b1 in BranchSeqRepresentation() && b2 in BranchSeqRepresentation() && b1 != b2 :: 
        LB.LinkedBranch(b1, branchDiskView).Representation() !! LB.LinkedBranch(b2, branchDiskView).Representation() 
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

    predicate IsFresh(addrs: set<Address>) {
      && diskView.IsFresh(addrs)
      && branchDiskView.IsFresh(addrs)
    }
   
    function ChildAtIdx(idx: nat) : BranchedBetree
      requires WF()
      requires HasRoot()
      requires Root().ValidChildIndex(idx)
    {
      BranchedBetree(Root().children[idx], diskView, branchDiskView)
    }

    function ChildForKey(key: Key) : BranchedBetree
      requires HasRoot()
      requires Root().KeyInDomain(key)
      ensures WF() ==> WF()
    {
      BranchedBetree(Root().ChildPtr(key), diskView, branchDiskView)
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
        var tightDv := DiskView.DiskView(MapRestrict(diskView.entries, Representation()));
        var tightBDv := 
          if NoDanglingBranchPointers() && AcyclicBranches()
          then LB.DiskView(MapRestrict(branchDiskView.entries, BranchFullRepresentation()))
          else branchDiskView;

      BranchedBetree(root, tightDv, tightBDv)
    }

    function Representation() : set<Address>
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

    // only returns roots of branches
    function BranchSeqRepresentation() : (out: set<Address>) 
      requires Acyclic()
    {
      var sets := set treeAddr | treeAddr in Representation() :: diskView.Get(Some(treeAddr)).branches.Representation();
      Sets.UnionSetOfSets(sets)
    }

    // returns roots and all nodes within a branch
    function BranchFullRepresentation() : (out: set<Address>)
      requires Acyclic()
      requires NoDanglingBranchPointers()
      requires AcyclicBranches()
    {
      var sets := set branch | branch in BranchSeqRepresentation() :: LB.LinkedBranch(branch, branchDiskView).Representation();
      Sets.UnionSetOfSets(sets)
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
      requires diskView.LinkedChildren()
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
      // requires diskView.LinkedChildren()
      requires CanSplitParent(request)
    {
      if diskView.LinkedChildren() then  
        var oldChild := ChildAtIdx(request.childIdx);
        var (newLeftChild, newRightChild) := 
          if request.SplitLeaf? 
          then oldChild.Root().SplitLeaf(request.splitKey) 
          else oldChild.Root().SplitIndex(request.childPivotIdx);

        var newChildren := replace1with2(Root().children, Some(newAddrs.left), Some(newAddrs.right), request.childIdx);
        var newflushedOffsets := Root().flushedOffsets.Split(request.childIdx);
        var newParent := BetreeNode(Root().branches, InsertPivot(Root().pivotTable, request.childIdx+1, SplitKey(request)), newChildren, newflushedOffsets);

        var dv' := diskView.ModifyDisk(newAddrs.left, newLeftChild).ModifyDisk(newAddrs.right, newRightChild).ModifyDisk(newAddrs.parent, newParent);
        BranchedBetree(Pointer.Some(newAddrs.parent), dv', branchDiskView)
      else
        this // silly
    }

    lemma SplitParentCanSubstitute(request: SplitRequest, newAddrs: L.SplitAddrs)
      requires CanSplitParent(request)
      requires newAddrs.HasUniqueElems()  // frameity frame frame
      // requires IsFresh(newAddrs.Repr())  // frameity frame frame
      // requires diskView.LinkedChildren()  // TODO: This seems sketch
      ensures SplitParent(request, newAddrs).WF()
      // ensures SplitParent(request, newAddrs).Root().MyDomain() == Root().MyDomain()
    {
      if diskView.LinkedChildren() {
        var dv := SplitParent(request, newAddrs).diskView;
        var newParent := SplitParent(request, newAddrs).Root();

        WFPivotsInsert(Root().pivotTable, request.childIdx+1, SplitKey(request));

        forall idx:nat | newParent.ValidChildIndex(idx)
        ensures dv.IsNondanglingPointer(newParent.children[idx]) {
          if request.childIdx+1 < idx {
            assert dv.IsNondanglingPointer(Root().children[idx-1]);  // seq offset trigger
          }
        }

        // forall idx:nat | newParent.ValidChildIndex(idx)
        // ensures dv.ChildLinked(newParent, idx) {
        //   if idx < request.childIdx {
        //     assert diskView.ChildLinked(Root(), idx);  // seq offset trigger
        //   } else if request.childIdx+1 < idx {
        //     assert diskView.ChildLinked(Root(), idx-1);  // seq offset trigger
        //   }
        // }

        var newflushedOffsets := Root().flushedOffsets.Split(request.childIdx);
        forall i:nat | i < newflushedOffsets.Size()
          ensures newflushedOffsets.Get(i) <= Root().branches.Length()
        {
          if i < request.childIdx {
          } else if i <= request.childIdx+1 {
            assert newflushedOffsets.Get(i) == Root().flushedOffsets.Get(request.childIdx);
          } else {
            assert newflushedOffsets.Get(i) == Root().flushedOffsets.Get(i-1);
          }
        }

        if request.SplitIndex? {
          var child := ChildAtIdx(request.childIdx).Root();
          var left := dv.entries[newAddrs.left];
          var right := dv.entries[newAddrs.right];

          // forall idx:nat | left.ValidChildIndex(idx) ensures dv.ChildLinked(left, idx) {
          //   assert diskView.ChildLinked(child, idx);
          //   assert dv.ChildLinked(left, idx);
          // }

          // forall idx:nat | right.ValidChildIndex(idx) ensures dv.ChildLinked(right, idx) {
          //   assert diskView.ChildLinked(child, idx+request.childPivotIdx);
          //   assert dv.ChildLinked(right, idx);
          // }
        }
        // assert dv.NodeHasLinkedChildren(dv.entries[newAddrs.parent]);
        assert  SplitParent(request, newAddrs).WF();
      } else {
        assert  SplitParent(request, newAddrs).WF();  // true for silly reasons
      }
    }
  }

  type PathAddrs = seq<Address>

  datatype Path = Path(branched: BranchedBetree, key: Key, depth: nat)
  {
    function Subpath() : (out: Path)
      requires 0 < depth
      requires branched.HasRoot()
      requires branched.Root().KeyInDomain(key)
    {
      Path(branched.ChildForKey(key), key, depth-1)
    }

    predicate Valid()
      decreases depth
    {
      && branched.Acyclic()
      && branched.WF()
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
      ensures out.branchDiskView == branched.branchDiskView
      ensures out.HasRoot() ==> out.root.value in out.diskView.entries
      decreases depth
    {
      if 0 == depth
      then branched
      else Subpath().Target()
    }

    // Returns the address of all the nodes on the path, from root up to and including target
    function AddrsOnPath() : seq<Address> 
      requires Valid()
      decreases depth
    {
      if depth == 0 then []
      else Subpath().AddrsOnPath() + [branched.root.value]
    }

    predicate CanSubstitute(replacement: BranchedBetree, pathAddrs: PathAddrs)
    {
      && Valid()
      && Target().HasRoot() // redundant with "path must lead to a non-nil node"?
      && replacement.WF()
      && replacement.HasRoot()
      && replacement.Root().MyDomain() == Target().Root().MyDomain()
      && depth == |pathAddrs|
      // TODOOOOO
      // && branched.diskView.IsSubsetOf(replacement.diskView)
    }

    lemma CanSubstituteSubpath(replacement: BranchedBetree, pathAddrs: PathAddrs)
      requires CanSubstitute(replacement, pathAddrs)
      requires 0 < depth
      ensures Subpath().CanSubstitute(replacement, pathAddrs[1..])
    {}

    // predicate DomainAfterSubstitute(dv: DiskView, pathAddrs: PathAddrs, dv': DiskView)
    // {
    //   && (Set(pathAddrs) !! dv.entries.Keys ==> 
    //     dv'.entries.Keys - dv.entries.Keys == Set(pathAddrs))
    // }

    function Substitute(replacement: BranchedBetree, pathAddrs: PathAddrs) : (out: BranchedBetree)
      requires CanSubstitute(replacement, pathAddrs)
      // ensures DomainAfterSubstitute(replacement.diskView, pathAddrs, out.diskView)
      decreases depth, 1
    {
      if depth == 0
      then replacement
      else
        var node := branched.Root();
        CanSubstituteSubpath(replacement, pathAddrs);
        var subtree := Subpath().Substitute(replacement, pathAddrs[1..]);
        var newChildren := node.children[Route(node.pivotTable, key) := subtree.root];
        var newNode := BetreeNode(node.branches, node.pivotTable, newChildren, node.flushedOffsets);
        var newDiskView := subtree.diskView.ModifyDisk(pathAddrs[0], newNode);

        // assert DomainAfterSubstitute(replacement.diskView, pathAddrs, newDiskView) by {
        //   assert DomainAfterSubstitute(replacement.diskView, pathAddrs[1..], subtree.diskView);
        //   if Set(pathAddrs) !! replacement.diskView.entries.Keys {
        //     assert subtree.diskView.entries.Keys - replacement.diskView.entries.Keys == Set(pathAddrs[1..]);
        //     assert newDiskView.entries.Keys == subtree.diskView.entries.Keys + {pathAddrs[0]};
        //     assert  Set(pathAddrs[1..]) + {pathAddrs[0]} == Set(pathAddrs);
        //   }
        // }

        BranchedBetree(GenericDisk.Pointer.Some(pathAddrs[0]), newDiskView, branched.branchDiskView)
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
      && (forall i:nat | i < |lines| :: lines[i].branched.branchDiskView == branched.branchDiskView)      
      && Last(lines).result == Define(DefaultValue())
      && branched.WF()
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
      && (forall i:nat | i < |lines| :: lines[i].branched.WF())
      && (forall i:nat | i < |lines|-1 :: Node(i).KeyInDomain(key))
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
      && var start := Node(i).ActiveBranchesForKey(key); // only query on a child's active range
      && var msg := Node(i).branches.QueryFrom(branched.branchDiskView, key, start);      
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
      branched.WF()
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
    && lbl.PutLabel? // insert into the linked memtable, more steps (internal memtable step)
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

  function InsertInternalFlushMemtableReplacement(oldRoot: BranchedBetree, newBranch: LB.LinkedBranch, newRootAddr:Address) : (out: BranchedBetree)
    requires oldRoot.WF()
  {
    var root' := 
      if oldRoot.HasRoot()
      then oldRoot.Root().ExtendBranchSeq(BranchSeq([newBranch.root]))
      else BetreeNode(BranchSeq([newBranch.root]), L.TotalPivotTable(), [None], BufferOffsets([0]));

    var dv' := oldRoot.diskView.ModifyDisk(newRootAddr, root');
    var bdv' := oldRoot.branchDiskView.MergeDisk(newBranch.diskView);
    BranchedBetree(Pointer.Some(newRootAddr), dv', bdv')
  }

  predicate InternalFlushMemtableTree(v: Variables, v': Variables, lbl: TransitionLabel, step: Step)
  {
    && v.WF()
    && step.WF()
    && lbl.InternalLabel?
    && step.InternalFlushMemtableStep?
    // Allocation validation

    // memtable allocation put label and build memtable label
    // TODO: memtable => linkedBranch 
    // what labelfor populate memtable 

    // perhaps we need to 
    && (forall key :: step.branch.Query(key) == v.memtable.buffer.Query(key)) // TODO: revisit
    && v'.branched == InsertInternalFlushMemtableReplacement(v.branched, step.branch, step.newRootAddr).BuildTightTree()
    && v'.memtable == v.memtable.Drain()
  }


  predicate InternalFlushMemtable(v: Variables, v': Variables, lbl: TransitionLabel, step: Step)
  {
    && InternalFlushMemtableTree(v, v', lbl, step)
    && v.branched.IsFresh({step.newRootAddr})
    && v.branched.IsFresh(step.branch.Representation())
  }

  function InsertGrowReplacement(branched: BranchedBetree, newRootAddr:Address) : (out: BranchedBetree)
    requires branched.WF()
  {
    // The new root node
    var root' := BetreeNode(BranchSeq([]), L.TotalPivotTable(), [branched.root], BufferOffsets([0]));
    // The new diskview
    var dv' := branched.diskView.ModifyDisk(newRootAddr, root');
    BranchedBetree(Pointer.Some(newRootAddr), dv', branched.branchDiskView)
  }

  predicate InternalGrowTree(v: Variables, v': Variables, lbl: TransitionLabel, step: Step) 
  {
    && v.WF()
    && step.WF()
    && lbl.InternalLabel?
    && step.InternalGrowStep?
    && v'.branched == InsertGrowReplacement(v.branched, step.newRootAddr)
    && v'.memtable == v.memtable  // UNCHANGED
  }

  predicate InternalGrow(v: Variables, v': Variables, lbl: TransitionLabel, step: Step)
  {
    && InternalGrowTree(v, v', lbl, step)
    && v.branched.IsFresh({step.newRootAddr}) // Subway Eat Fresh!
  }

  predicate InternalSplitTree(v: Variables, v': Variables, lbl: TransitionLabel, step: Step)
  {
    && v.WF()
    && lbl.InternalLabel?
    && step.InternalSplitStep?
    && step.WF()
    && step.path.branched == v.branched
    && step.path.Target().CanSplitParent(step.request)
    && var replacement := step.path.Target().SplitParent(step.request, step.newAddrs);
    && assert step.path.CanSubstitute(replacement, step.pathAddrs) by {
        step.path.Target().SplitParentCanSubstitute(step.request, step.newAddrs);}
    && v'.branched == step.path.Substitute(replacement, step.pathAddrs).BuildTightTree()
    && v'.memtable == v.memtable  // UNCHANGED
  }

  predicate InternalSplit(v: Variables, v': Variables, lbl: TransitionLabel, step: Step)
  {
    && InternalSplitTree(v, v', lbl, step)
    && v.branched.IsFresh(step.newAddrs.Repr() + Set(step.pathAddrs))
  }

  function InsertFlushReplacement(target: BranchedBetree, childIdx:nat, 
    targetAddr: Address, targetChildAddr: Address, branchGCCount: nat) : (out: BranchedBetree)
    requires target.WF()
    requires target.HasRoot()
    requires target.Root().OccupiedChildIndex(childIdx)
    requires target.Root().flushedOffsets.AdvanceIndex(childIdx, target.Root().branches.Length()).CanCollectGarbage(branchGCCount)
  {
    var root := target.Root();

    var newflushedOffsets := root.flushedOffsets.AdvanceIndex(childIdx, root.branches.Length());
    assert branchGCCount <= root.branches.Length() by {
      var i:nat :| i < newflushedOffsets.Size();
      assert newflushedOffsets.Get(i) <= root.branches.Length();
    }

    var keptBranches := root.branches.Slice(branchGCCount, root.branches.Length()); // branchs remaining after gc
    var movedBranches := root.branches.Slice(root.flushedOffsets.Get(childIdx), root.branches.Length()); // branchs to flush to child

    var GCflushedOffsets := BufferOffsets(seq (newflushedOffsets.Size(), 
      i requires 0 <= i < newflushedOffsets.Size() => 
      newflushedOffsets.Get(i)-branchGCCount));

    var subroot := target.diskView.Get(root.children[childIdx]);
    var extendBranchSeq := subroot.branches.Extend(movedBranches);
    var subroot' := BetreeNode(extendBranchSeq, 
      subroot.pivotTable, subroot.children, subroot.flushedOffsets);

    // BetreeNode of the new root, to be stored at targetAddr in the diskview
    var children' := root.children[childIdx := Pointer.Some(targetChildAddr)];
    var root' := BetreeNode(keptBranches, root.pivotTable, children', GCflushedOffsets);

    // The new diskview
    var dv' := target.diskView.ModifyDisk(targetAddr, root').ModifyDisk(targetChildAddr, subroot');
    BranchedBetree(Pointer.Some(targetAddr), dv', target.branchDiskView)
  }

  predicate InternalFlushTree(v: Variables, v': Variables, lbl: TransitionLabel, step: Step)
  {
    && v.WF()
    && step.WF()
    && lbl.InternalLabel?
    && step.InternalFlushStep?

    && step.path.branched == v.branched
    && step.path.Valid()
    && var root := step.path.Target().Root();
    && root.OccupiedChildIndex(step.childIdx)  // the downstream child must exist
    && var replacement := InsertFlushReplacement(step.path.Target(), step.childIdx, step.targetAddr, step.targetChildAddr, step.branchGCCount); // meow
    && step.path.CanSubstitute(replacement, step.pathAddrs)
    // Subway Eat Fresh!
    && v'.branched == step.path.Substitute(replacement, step.pathAddrs).BuildTightTree()
    && v'.memtable == v.memtable  // UNCHANGED
  }

  // Flush is responsible for 1. flush branch to child 2. update the active branch range for that child 
  // 3. truncate inactive branches and shift active range when possible
  predicate InternalFlush(v: Variables, v': Variables, lbl: TransitionLabel, step: Step)
  {
    && InternalFlushTree(v, v', lbl, step)
    && v.branched.IsFresh({step.targetAddr, step.targetChildAddr} + Set(step.pathAddrs))
  }

  function InsertCompactReplacement(target: BranchedBetree, start: nat, end: nat, 
    newBranch: LB.LinkedBranch, replacementAddr: Address) : (out: BranchedBetree)
    requires target.WF()
    requires target.HasRoot()
    requires start <= end <= target.Root().branches.Length()
    requires newBranch.Acyclic()
    requires newBranch.TightDiskView()
    requires {replacementAddr} !! newBranch.Representation()
    ensures out.diskView.entries.Keys == target.diskView.entries.Keys + {replacementAddr}
    ensures out.WF()   // prereq to MyDomain()
    ensures out.HasRoot() && out.Root().MyDomain() == target.Root().MyDomain()
  {
    var root := target.Root();
    var newBranchSeq := root.branches.Slice(0, start).Extend(BranchSeq([newBranch.root])).Extend(root.branches.Slice(end, root.branches.Length()));
    var newBranchDiskView := target.branchDiskView.MergeDisk(newBranch.diskView);

    var newRoot := BetreeNode(newBranchSeq, root.pivotTable, root.children, root.flushedOffsets.OffSetsAfterCompact(start, end));
    var newDiskView := target.diskView.ModifyDisk(replacementAddr, newRoot);

    // assert newDiskView.HealthyChildPointers() by {
    //   forall addr | addr in newDiskView.entries
    //   ensures newDiskView.NodeHasLinkedChildren(newDiskView.entries[addr])
    //   {
    //     if addr != replacementAddr {
    //       assert addr in target.diskView.entries;
    //     }
    //   }
    // }

    var out := BranchedBetree(GenericDisk.Pointer.Some(replacementAddr), newDiskView, newBranchDiskView);
    assert out.diskView.WF();
 
    out
  }

  predicate InternalCompactTree(v: Variables, v': Variables, lbl: TransitionLabel, step: Step)
  {
    && v.WF()
    && step.WF()
    && step.InternalCompactStep?
    && lbl.InternalLabel?
    && step.path.branched == v.branched
    && var replacement := InsertCompactReplacement(step.path.Target(), step.start, step.end, step.newBranch, step.targetAddr);
    && v'.branched == step.path.Substitute(replacement, step.pathAddrs).BuildTightTree()
    && v'.memtable == v.memtable  // UNCHANGED
  }

  predicate InternalCompact(v: Variables, v': Variables, lbl: TransitionLabel, step: Step)
  {
    && InternalCompactTree(v, v', lbl, step)
    && v.branched.IsFresh(Set(step.pathAddrs) + {step.targetAddr} + step.newBranch.Representation())
  }

  predicate InternalNoOp(v: Variables, v': Variables, lbl: TransitionLabel)
  {
    && lbl.InternalLabel?
    && v.WF()
    && v' == v
  }

  // public:
  predicate Init(v: Variables, stampedBetree: StampedBetree)
  {
    && v == Variables(EmptyMemtable(stampedBetree.seqEnd), stampedBetree.value)
  }

  // TODO: add allocation addrs for betree and branch 
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
    | InternalFlushStep(path: Path, childIdx: nat, targetAddr: Address, targetChildAddr: Address, pathAddrs: PathAddrs, branchGCCount: nat)
      // targetAddr is the fresh address at which compacted node is placed. pathAddrs is the new addresses to place all its ancestors
    | InternalCompactStep(path: Path, start: nat, end: nat, newBranch: LB.LinkedBranch, targetAddr: Address, pathAddrs: PathAddrs)
    | InternalNoOpStep()
  {
    predicate WF() {
      match this {
        case QueryStep(receipt) => receipt.Valid()
        case InternalFlushMemtableStep(_, branch) => 
          && branch.Acyclic()
          && branch.TightDiskView()
        //   && branch.AllKeysInRange()
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
          && path.Target().Root().flushedOffsets.AdvanceIndex(childIdx, path.Target().Root().branches.Length()).CanCollectGarbage(branchGCCount)
        case InternalCompactStep(path, start, end, newBranch, targetAddr, pathAddrs) =>
          && path.Valid()
          && path.depth == |pathAddrs|
          && SeqHasUniqueElems(pathAddrs)
          && {targetAddr} !! Set(pathAddrs)
          && newBranch.Acyclic()
          && newBranch.TightDiskView()
          // && newBranch.AllKeysInRange()
          && {targetAddr} !! newBranch.Representation()
          && var node := path.Target().Root();
          && var offsetMap := node.MakeOffsetMap().Decrement(start);
          && start < end <= node.branches.Length()
          && node.branches.Slice(start, end).QueryFilteredEquiv(path.Target().branchDiskView, offsetMap, newBranch)
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
      case InternalCompactStep(_, _, _, _, _, _) => InternalCompact(v, v', lbl, step)
      case InternalNoOpStep() => InternalNoOp(v, v', lbl)
    }
  }

  predicate Next(v: Variables, v': Variables, lbl: TransitionLabel) {
    exists step: Step :: NextStep(v, v', lbl, step)
  }
}
