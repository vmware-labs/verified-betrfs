// Copyright 2018-2021 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, and University of Washington
// SPDX-License-Identifier: BSD-2-Clause

include "FilteredBetree.i.dfy"
include "../../lib/Buckets/BoundedPivotsLib.i.dfy"
include "../Disk/GenericDisk.i.dfy"
include "Domain.i.dfy"
include "SplitRequest.i.dfy"
include "LinkedBufferStack.i.dfy"

// Introduces a diskview and pointers, carries forward filtered buffer stacks inside the 
// betree nodes. There are two disk views here. One for the BetreeNode type, and one for 
// the abstract Branch type. A refining state machine replaces single-node branches with
// b+trees.
module LinkedBetreeMod
{
  import Sets
  import opened BoundedPivotsLib
  // import opened Buffers
  import opened DomainMod
  import opened GenericDisk
  import opened KeyType
//  import opened Lexicographic_Byte_Order
  import opened LSNMod
  import opened MemtableMod
  import opened MsgHistoryMod
  import opened Options
  import opened Sequences
  import opened BufferMod
  import opened LinkedBufferStackMod
  import opened StampedMod
  import opened Upperbounded_Lexicographic_Byte_Order_Impl
  import opened Upperbounded_Lexicographic_Byte_Order_Impl.Ord
  import opened ValueMessage
  import opened Maps
  import TotalKMMapMod
  import opened SplitRequestMod
  import FilteredBetree
  import opened OffsetMapMod
  import opened BufferOffsetsMod

  type Pointer = GenericDisk.Pointer
  type Address = GenericDisk.Address
  type StampedBetree = Stamped<LinkedBetree>

  function EmptyLinkedBetree() : (out: LinkedBetree)
  {
    LinkedBetree(None, EmptyDisk(), EmptyBufferDisk())
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
    | FreezeAsLabel(linkedBetree: StampedBetree)
     // Internal-x labels refine to no-ops at the abstract spec
    | InternalAllocationsLabel(addrs: set<Address>)  // for steps that involve allocating new pages
    | InternalLabel()   // Local No-op label

  datatype BetreeNode = BetreeNode(
    bufferStack: BufferStack,  // seq<Address> to represent linked buffers
    pivotTable: PivotTable,
    children: seq<Pointer>,
    flushedOffsets: BufferOffsets)
  {
    predicate WF() {
      && (BetreeNode? ==>
          && WFPivots(pivotTable)
          && |children| == NumBuckets(pivotTable)
          && |children| == flushedOffsets.Size()
          && flushedOffsets.BoundedBy(bufferStack.Length())
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

    function PushBufferStack(newBufferStack: BufferStack) : (out: BetreeNode)
      requires WF()
      requires BetreeNode?
      ensures out.WF()
    {
      BetreeNode(bufferStack.PushBufferStack(newBufferStack), pivotTable, children, flushedOffsets)
    }

    function ActiveBuffersForKey(key: Key) : (i: nat)
      requires KeyInDomain(key)
    {
      bufferStack.Length() - flushedOffsets.Get(Route(pivotTable, key))
    }

    predicate IsLeaf()
    {
      && |children|==1
      && children[0].None?
      && flushedOffsets== BufferOffsets([0]) 
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
      requires WF()
      requires BetreeNode?
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
      var newLeft := BetreeNode(bufferStack, [pivotTable[0], Element(splitKey)], [None], BufferOffsets([0]));
      var newRight := BetreeNode(bufferStack, [Element(splitKey), pivotTable[1]], [None], BufferOffsets([0]));
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
      var newLeft := BetreeNode(bufferStack, pivotTable[..pivotIdx+1], children[..pivotIdx], flushedOffsets.Slice(0, pivotIdx));
      var newRight := BetreeNode(bufferStack, pivotTable[pivotIdx..], children[pivotIdx..], flushedOffsets.Slice(pivotIdx, flushedOffsets.Size()));
      WFSlice(pivotTable, 0, pivotIdx+1);
      WFSuffix(pivotTable, pivotIdx);
      // assert WFChildren(children);  // trigger
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
          else bufferStack.Length())
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
    BetreeNode(BufferStack([]), pivotTable, [None], BufferOffsets([0]))
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

    predicate AgreesWithDisk(other: DiskView)
    {
      MapsAgree(entries, other.entries)
    }

    predicate IsSubDisk(bigger: DiskView)
    {
      IsSubMap(entries, bigger.entries)
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
    {
      && WF()
      && (forall addr |
            && addr in ranking
            && addr in entries
          ::
            NodeChildrenRespectsRank(ranking, addr)
      )
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
  // Holds the diskviews that lets us interpret BetreeNode pointers and Buffer pointers
  datatype LinkedBetree = LinkedBetree(
    root: Pointer,
    diskView: DiskView,
    bufferDiskView: BufferDiskView
  )
  {
    predicate WF() {
      && diskView.WF()
      && diskView.IsNondanglingPointer(root)
      && diskView.IsFresh(bufferDiskView.Addresses())
      && NoDanglingBufferPointers() // might not be in WF
    }

    // buffers in each node should be known to forest
    predicate NoDanglingBufferPointers() {
      && (forall addr, buffer | 
        && addr in diskView.entries 
        && buffer in diskView.entries[addr].bufferStack.buffers
        :: buffer in bufferDiskView.Addresses())
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
      LinkedBetree(Root().children[idx], diskView, bufferDiskView)
    }

    function ChildForKey(key: Key) : LinkedBetree
      requires HasRoot()
      requires Root().KeyInDomain(key)
    {
      LinkedBetree(Root().ChildPtr(key), diskView, bufferDiskView)
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
    {
      && WF()
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
      ensures out.diskView.IsSubDisk(diskView)
    {
      if ! Acyclic() then
        // Need this case because at the state machine I don't have proof that after an
        // operation, that the new state is acyclic
        this
      else
        var tightDv := DiskView.DiskView(MapRestrict(diskView.entries, Representation()));
        var tightBDv := BufferDiskView(MapRestrict(bufferDiskView.entries, BufferStackRepresentation()));
        LinkedBetree(root, tightDv, tightBDv)
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

    function BufferStackRepresentation() : (out: set<Address>) {
      var sets := set treeAddr | treeAddr in Representation() :: diskView.Get(Some(treeAddr)).bufferStack.Representation();
      Sets.UnionSetOfSets(sets)
    }

    predicate DiskIsTightWrtRepresentation()
      requires Acyclic()
    {
      diskView.entries.Keys == Representation()
    }

    function GetLinkedAtAddr(addr: Address) : LinkedBetree 
      requires addr in diskView.entries
    {
      LinkedBetree(Pointer.Some(addr), diskView, bufferDiskView)
    }

    predicate RepresentationIsDagFree()
      requires Acyclic()
    {
      forall addr | 
        && addr in Representation()
        && GetLinkedAtAddr(addr).HasRoot()
      :: 
        GetLinkedAtAddr(addr).AllSubtreesAreDisjoint()
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
      var newflushedOffsets := Root().flushedOffsets.Split(request.childIdx);
      var newParent := BetreeNode(Root().bufferStack, InsertPivot(Root().pivotTable, request.childIdx+1, SplitKey(request)), newChildren, Root().flushedOffsets);

      var dv' := diskView.ModifyDisk(newAddrs.left, newLeftChild).ModifyDisk(newAddrs.right, newRightChild).ModifyDisk(newAddrs.parent, newParent);
      LinkedBetree(Pointer.Some(newAddrs.parent), dv', bufferDiskView)
    }

    lemma SplitParentCanSubstitute(request: SplitRequest, newAddrs: SplitAddrs)
      requires CanSplitParent(request)
      requires newAddrs.HasUniqueElems()  // frameity frame frame
      requires diskView.IsFresh(newAddrs.Repr())  // frameity frame frame
      ensures SplitParent(request, newAddrs).WF()
      ensures SplitParent(request, newAddrs).Root().MyDomain() == Root().MyDomain()
    {
      var dv := SplitParent(request, newAddrs).diskView;

      var newChildren := replace1with2(Root().children, Some(newAddrs.left), Some(newAddrs.right), request.childIdx);
      var newParent := BetreeNode(Root().bufferStack, InsertPivot(Root().pivotTable, request.childIdx+1, SplitKey(request)), newChildren, Root().flushedOffsets);

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

      assert dv.NodeHasLinkedChildren(dv.entries[newAddrs.left]) by {  // trigger hecka weirdly brittle
        var node := dv.entries[newAddrs.left];
        forall idx:nat | node.ValidChildIndex(idx) ensures dv.ChildLinked(node, idx) {
          assert dv.ChildLinked(node, idx);
        }
      }  
      assert dv.NodeHasLinkedChildren(dv.entries[newAddrs.right]) by {  // trigger hecka weirdly brittle
        var node := dv.entries[newAddrs.right];
        forall idx:nat | node.ValidChildIndex(idx) ensures dv.ChildLinked(node, idx) {  // seq offset trigger seems to help with the brittle
          assert dv.ChildLinked(node, idx);
        }
      }
      assert dv.NodeHasLinkedChildren(dv.entries[newAddrs.parent]);  // trigger
    }

    // Subtree representations have null intersections
    predicate SubtreesAreDisjoint(i: nat, j: nat) 
      requires WF()
      requires HasRoot()
      requires Root().ValidChildIndex(i)
      requires Root().ValidChildIndex(j)
      requires ChildAtIdx(i).Acyclic()
      requires ChildAtIdx(j).Acyclic()
      requires i != j
    {
      ChildAtIdx(i).Representation() !! ChildAtIdx(j).Representation()
    }

    predicate AllSubtreesAreDisjoint() 
      requires WF()
      requires HasRoot()
    {
      forall i, j | 
          && i != j 
          && 0 <= i < |Root().children| 
          && 0 <= j < |Root().children|
          && ChildAtIdx(i).Acyclic()
          && ChildAtIdx(j).Acyclic()
      :: 
        SubtreesAreDisjoint(i, j)
    }
  }

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
  }

  datatype Variables = Variables(
    memtable: Memtable,
    linked: LinkedBetree)
  {
    predicate WF() {
      && linked.WF()
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
      && var end := Node(i).ActiveBuffersForKey(key);
      && lines[i].result == Merge(Node(i).bufferStack.QueryUpTo(linked.bufferDiskView, key, end), ResultAt(i+1))
    }

    predicate Valid()
    {
      && Structure()
      && AllLinesWF()
      && (forall i:nat | i < |lines| - 1 :: ChildLinkedAt(i))
      && (forall i:nat | i < |lines| - 1 :: ResultLinkedAt(i))
    }

    predicate ValidFor(linked: LinkedBetree, key: Key)
    {
      && Valid()
      && this.linked == linked
      && this.key == key
    }

    function Result() : Message
      requires Structure()
    {
      ResultAt(0)
    }
  }  // end datatype QueryReceipt

  predicate Query(v: Variables, v': Variables, lbl: TransitionLabel, receipt: QueryReceipt)
  {
    && lbl.QueryLabel?
    && lbl.endLsn == v.memtable.seqEnd
    && receipt.ValidFor(v.linked, lbl.key)
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
    function AddrsOnPath() : (out: set<Address>)
      requires Valid()
      decreases depth
    {
      if depth == 0 then {linked.root.value}
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
      && linked.diskView.IsSubDisk(replacement.diskView)
      && linked.bufferDiskView.IsSubDisk(replacement.bufferDiskView)
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
        var newNode := BetreeNode(node.bufferStack, node.pivotTable, newChildren, node.flushedOffsets);
        var newDiskView := subtree.diskView.ModifyDisk(pathAddrs[0], newNode);
        LinkedBetree(GenericDisk.Pointer.Some(pathAddrs[0]), newDiskView, linked.bufferDiskView)
    }
  }

  function InsertInternalFlushMemtableReplacement(oldRoot: LinkedBetree, newBuffer: Buffer, newBufferAddr: Address, newRootAddr:Address) : (out: LinkedBetree)
    requires oldRoot.WF()
  {
    var root' := if oldRoot.HasRoot()
      then
        oldRoot.Root().PushBufferStack(BufferStack([newBufferAddr]))
      else
        BetreeNode(BufferStack([newBufferAddr]), TotalPivotTable(), [None], BufferOffsets([0]));
    var dv' := oldRoot.diskView.ModifyDisk(newRootAddr, root');
    var bdv' := oldRoot.bufferDiskView.ModifyDisk(newBufferAddr, newBuffer);
    LinkedBetree(Pointer.Some(newRootAddr), dv', bdv') 
  }

  predicate InternalFlushMemtable(v: Variables, v': Variables, lbl: TransitionLabel, step: Step)
  {
    && v.WF()
    && step.WF()
    && lbl.InternalAllocationsLabel?
    && step.InternalFlushMemtableStep?
    && lbl.addrs == {step.newRootAddr} + {step.newBufferAddr}
    // Subway Eat Fresh!
    && v.linked.diskView.IsFresh(lbl.addrs)
    && v'.linked == InsertInternalFlushMemtableReplacement(v.linked, v.memtable.buffer, step.newBufferAddr, step.newRootAddr).BuildTightTree()
    && v'.memtable == v.memtable.Drain()
  }

  function InsertGrowReplacement(oldRoot: LinkedBetree, newRootAddr:Address) : (out: LinkedBetree)
    requires oldRoot.WF()
  {
    // The new root node
    var root' := BetreeNode(BufferStack([]), TotalPivotTable(), [oldRoot.root], BufferOffsets([0]));
    // The new diskview
    var dv' := oldRoot.diskView.ModifyDisk(newRootAddr, root');
    LinkedBetree(Pointer.Some(newRootAddr), dv', oldRoot.bufferDiskView)
  }

  predicate InternalGrow(v: Variables, v': Variables, lbl: TransitionLabel, step: Step)
  {
    && v.WF()
    && step.WF()
    && lbl.InternalAllocationsLabel?
    && step.InternalGrowStep?
    && lbl.addrs == {step.newRootAddr}
    // Subway Eat Fresh!
    && v.linked.diskView.IsFresh({step.newRootAddr})
    // && v'.linked == InsertGrowReplacement(v.linked, step.newRootAddr).BuildTightTree()
    // Removed BuildTight because it doesn't do anything here
    && v'.linked == InsertGrowReplacement(v.linked, step.newRootAddr)
    && v'.memtable == v.memtable  // UNCHANGED
  }

  predicate InternalSplit(v: Variables, v': Variables, lbl: TransitionLabel, step: Step)
  {
    && v.WF()
    && lbl.InternalAllocationsLabel?
    && step.InternalSplitStep?
    && lbl.addrs == Set(step.pathAddrs) + step.newAddrs.Repr()
    && step.WF()
    && step.path.linked == v.linked
    && v.linked.diskView.IsFresh(step.newAddrs.Repr() + Set(step.pathAddrs))
    && step.path.Target().CanSplitParent(step.request)
    && var replacement := step.path.Target().SplitParent(step.request, step.newAddrs);
    && assert step.path.CanSubstitute(replacement, step.pathAddrs) by {
        step.path.Target().SplitParentCanSubstitute(step.request, step.newAddrs);
      } true
    && v'.linked == step.path.Substitute(replacement, step.pathAddrs).BuildTightTree()
    && v'.memtable == v.memtable  // UNCHANGED
  }

  function InsertFlushReplacement(target: LinkedBetree, childIdx:nat, 
    targetAddr: Address, targetChildAddr: Address, bufferGCCount: nat) : (out: LinkedBetree)
    requires target.WF()
    requires target.HasRoot()
    requires target.Root().OccupiedChildIndex(childIdx)
    requires target.Root().flushedOffsets.AdvanceIndex(childIdx, target.Root().bufferStack.Length()).CanCollectGarbage(bufferGCCount)
  {
    var root := target.Root();

    var newflushedOffsets := root.flushedOffsets.AdvanceIndex(childIdx, root.bufferStack.Length());
    var keptBuffers := root.bufferStack.Slice(0, root.bufferStack.Length() - bufferGCCount);
    var movedBuffers := root.bufferStack.Slice(0, root.bufferStack.Length() - root.flushedOffsets.Get(childIdx));

    var GCflushedOffsets := BufferOffsets(seq (newflushedOffsets.Size(), 
      i requires 0 <= i < newflushedOffsets.Size() => 
      newflushedOffsets.Get(i)-bufferGCCount));

    // BetreeNode of the new child, to be stored at targetChildAddr in the diskview
    var subroot := target.diskView.Get(root.children[childIdx]);
    var pushedBufferStack := subroot.bufferStack.PushBufferStack(movedBuffers);
    var subroot' := BetreeNode(pushedBufferStack, 
      subroot.pivotTable, subroot.children, subroot.flushedOffsets);

    // BetreeNode of the new root, to be stored at targetAddr in the diskview
    var children' := root.children[childIdx := Pointer.Some(targetChildAddr)];



    var root' := BetreeNode(keptBuffers, root.pivotTable, children', GCflushedOffsets);

    // The new diskview
    var dv' := target.diskView.ModifyDisk(targetAddr, root').ModifyDisk(targetChildAddr, subroot');

    // linked 
    LinkedBetree(Pointer.Some(targetAddr), dv', target.bufferDiskView)
  }

  predicate InternalFlush(v: Variables, v': Variables, lbl: TransitionLabel, step: Step)
  {
    && v.WF()
    && step.WF()
    && lbl.InternalAllocationsLabel?
    && step.InternalFlushStep?
    && lbl.addrs == Set(step.pathAddrs) + {step.targetAddr} + {step.targetChildAddr}
    && step.path.linked == v.linked
    && step.path.Valid()
    && step.path.Target().Root().OccupiedChildIndex(step.childIdx)  // the downstream child must exist
    && var replacement := InsertFlushReplacement(step.path.Target(), step.childIdx, step.targetAddr, step.targetChildAddr, step.bufferGCCount);
    && step.path.CanSubstitute(replacement, step.pathAddrs)
    // Subway Eat Fresh!
    && v.linked.diskView.IsFresh({step.targetAddr, step.targetChildAddr} + Set(step.pathAddrs))
    && v'.linked == step.path.Substitute(replacement, step.pathAddrs).BuildTightTree()
    && v'.memtable == v.memtable  // UNCHANGED
  }


  function OffSetsAfterCompact(offsets: BufferOffsets, start: nat, end: nat) : BufferOffsets{
    BufferOffsets(
      seq(offsets.Size(), i requires 0 <= i < offsets.Size() => 
        if offsets.Get(i) <= start then offsets.Get(i)
        else if offsets.Get(i) < end then start
        else offsets.Get(i) - (end-start)
      )
    )
  }

  // TODO(tony): Need to define notion of how newBufferDiskView is valid. For instance, it needs to contain 
  // the old bufferdiskview, and have some notion of "target.Root().bufferStack.Equivalent(compactedBuffers)"
  // target is the root node before it is compacted.
  // InsertReplacement returns a LinkedBetree that has the diskview of target with replacement placed at
  // the replacementAddr
  function InsertCompactReplacement(
    target: LinkedBetree, 
    start: nat, end: nat, compactedBuffer: Address, newBufferDiskView: BufferDiskView, 
    replacementAddr: Address) : (out: LinkedBetree)
    requires target.WF()
    requires target.HasRoot()
    requires target.Root().bufferStack.Slice(start, end).I(target.bufferDiskView, target.Root().MakeOffsetMap()) 
              == newBufferDiskView.Get(compactedBuffer) // equivalence
    requires target.diskView.IsFresh({replacementAddr})
    ensures target.diskView.IsSubDisk(out.diskView)
    ensures out.diskView.entries.Keys == target.diskView.entries.Keys + {replacementAddr}
    ensures out.WF()   // prereq to MyDomain()
    ensures out.HasRoot() && out.Root().MyDomain() == target.Root().MyDomain()
  {
    var root := target.Root();
    var newBufferStack := root.bufferStack.Slice(0, start).Extend(BufferStack([compactedBuffer])).Extend(root.bufferStack.Slice(end, root.bufferStack.Length()));
    var newRoot := BetreeNode(newBufferStack, root.pivotTable, root.children, OffSetsAfterCompact(root.flushedOffsets, start, end));
    var newDiskView := target.diskView.ModifyDisk(replacementAddr, newRoot);
    var out := LinkedBetree(GenericDisk.Pointer.Some(replacementAddr), newDiskView, newBufferDiskView);
    out
  }

  predicate InternalCompact(v: Variables, v': Variables, lbl: TransitionLabel, step: Step)
  {
    && v.WF()
    && step.WF()
    && lbl.InternalAllocationsLabel?
    && step.InternalCompactStep?
    && lbl.addrs == Set(step.pathAddrs) + {step.targetAddr}
    && step.path.linked == v.linked
    && step.path.Valid()

    // Subway Eat Fresh!
    && v.linked.diskView.IsFresh({step.targetAddr} + Set(step.pathAddrs))
    && var replacement := InsertCompactReplacement(step.path.Target(), step.compactStart, step.compactEnd, step.compactedBuffer, step.newBufferDiskView, step.targetAddr);
    && v.linked.bufferDiskView.IsSubDisk(step.newBufferDiskView)
    && v'.linked == step.path.Substitute(replacement, step.pathAddrs).BuildTightTree()
    && v'.memtable == v.memtable  // UNCHANGED
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

  datatype Step =
      QueryStep(receipt: QueryReceipt)
    | PutStep()
    | QueryEndLsnStep()
    | FreezeAsStep()
    // newRootAddr is the new address allocated for the new root
    | InternalGrowStep(newRootAddr: Address)

    | InternalSplitStep(path: Path, request: SplitRequest, newAddrs: SplitAddrs, pathAddrs: PathAddrs)
      // request describes how the split applies (to an Index or Leaf); newAddrs are the new page addresses
    | InternalFlushMemtableStep(newRootAddr: Address, newBufferAddr: Address)
    | InternalFlushStep(path: Path, childIdx: nat, targetAddr: Address, targetChildAddr: Address, pathAddrs: PathAddrs, bufferGCCount: nat)
      // targetAddr is the fresh address at which new node is placed, and targetChildAddr is for the new child receiving the flush
      // pathAddrs is the new addresses to place all its ancestors, used in substitution

    | InternalCompactStep(path: Path, compactStart: nat, compactEnd: nat, compactedBuffer: Address, newBufferDiskView: BufferDiskView, targetAddr: Address, pathAddrs: PathAddrs)
      // targetAddr is the fresh address at which compactedNode is placed. pathAddrs is the new addresses to place all its ancestors
    | InternalNoOpStep()
  {
    predicate WF() {
      match this {
        case QueryStep(receipt) => receipt.Valid()
        case InternalSplitStep(path, request, newAddrs, pathAddrs) =>
          && path.Valid()
          && path.depth == |pathAddrs|
          && SeqHasUniqueElems(pathAddrs)
          && path.Target().Root().ValidChildIndex(request.childIdx)
          && path.Target().CanSplitParent(request)
          && newAddrs.HasUniqueElems()
          && newAddrs.Repr() !! Set(pathAddrs)
        case InternalFlushStep(_, _, targetAddr, targetChildAddr, pathAddrs, bufferGCCount) =>
          && path.Valid()
          && path.Target().Root().ValidChildIndex(childIdx)
          && path.depth == |pathAddrs|
          && SeqHasUniqueElems(pathAddrs)
          && {targetAddr, targetChildAddr} !! Set(pathAddrs)
          && targetAddr != targetChildAddr
          && bufferGCCount <= path.Target().Root().bufferStack.Length()
        case InternalCompactStep(path, start, end, compactedBuffer, newBufferDv, targetAddr, pathAddrs) =>
          && path.Valid()
          && compactedBuffer in newBufferDv.entries
          && path.Target().Root().bufferStack.Slice(start, end).I(path.Target().bufferDiskView, path.Target().Root().MakeOffsetMap()) 
              == newBufferDv.Get(compactedBuffer)
          && path.depth == |pathAddrs|
          && SeqHasUniqueElems(pathAddrs)
          && {targetAddr} !! Set(pathAddrs)
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
      case InternalFlushMemtableStep(_, _) => InternalFlushMemtable(v, v', lbl, step)
      case InternalFlushStep(_, _, _, _, _, _) => InternalFlush(v, v', lbl, step)
      case InternalCompactStep(_, _, _, _, _, _, _) => InternalCompact(v, v', lbl, step)
      case InternalNoOpStep() => InternalNoOp(v, v', lbl)
    }
  }

  predicate Next(v: Variables, v': Variables, lbl: TransitionLabel) {
    exists step: Step :: NextStep(v, v', lbl, step)
  }
}
