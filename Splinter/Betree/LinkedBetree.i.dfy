// Copyright 2018-2021 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, and University of Washington
// SPDX-License-Identifier: BSD-2-Clause

include "PivotBetree.i.dfy"
include "../../lib/Buckets/BoundedPivotsLib.i.dfy"
include "../Journal/GenericDisk.i.dfy"
include "Domain.i.dfy"

module LinkedBetreeMod
{
  import opened BoundedPivotsLib
  import opened Buffers
  import opened DomainMod
  import opened GenericDisk
  import opened KeyType
//  import opened Lexicographic_Byte_Order
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

  type Pointer = GenericDisk.Pointer
  type Address = GenericDisk.Address
  type StampedBetree = Stamped<LinkedBetree>

  type Element = Upperbounded_Lexicographic_Byte_Order_Impl.Ord.Element

  datatype TransitionLabel =
      QueryLabel(endLsn: LSN, key: Key, value: Value)
    | PutLabel(puts: MsgHistory)
    | QueryEndLsnLabel(endLsn: LSN)
    | FreezeAsLabel(linkedBetree: StampedBetree)
    | InternalLabel()


  datatype BetreeNode = BetreeNode(
    buffers: BufferStack,  // Should buffer stack also be linked via pointers?
    pivotTable: PivotTable,
    children: seq<Pointer>)
  {
    predicate WF() {
      && (BetreeNode? ==>
          && WFPivots(pivotTable)
          && |children| == NumBuckets(pivotTable)
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

    function PushBufferStack(bufferStack: BufferStack) : (out: BetreeNode)
      requires WF()
      requires BetreeNode?
      ensures out.WF()
    {
      BetreeNode(buffers.PushBufferStack(bufferStack), pivotTable, children)
    }

    function ApplyFilter(filter: Domain) : (out: BetreeNode)
      requires WF()
      ensures out.WF()
    {
      BetreeNode(buffers.ApplyFilter(filter.KeySet()), pivotTable, children)
    }

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

    // // Redundant; should equal domain.KeySet() for the domain specified by the pivotTable.
    // function KeySet() : iset<Key>
    //   requires WF()
    //   requires BetreeNode?  // TODO(jonh): trouble for Nils?
    // {
    //   iset key | KeyInDomain(key)
    // }

    function ChildPtr(key: Key) : Pointer
      requires WF()
      requires BetreeNode?
      requires KeyInDomain(key)
    {
      children[Route(pivotTable, key)]
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
    BetreeNode(BufferStack([]), pivotTable, [None])
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
      requires WF()
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

    predicate IsFresh(addr: Address) {
      addr !in entries 
    } 
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
      && WF()
      && root.Some?
    }

    function Root() : BetreeNode
      requires HasRoot()
    {
      diskView.Get(root)
    }

    function ChildAtIdx(idx: nat) : LinkedBetree
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
    lines: seq<QueryReceiptLine>)
  {
    predicate Structure()
    {
      && 0 < |lines|
      && (forall i:nat | i < |lines| :: lines[i].ptr.Some? <==> i < |lines|-1)
      && (forall i:nat | i < |lines|-1 :: diskView.IsNondanglingPointer(lines[i].ptr))
      && Last(lines).result == Define(DefaultValue())
      && diskView.WF()
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
      && lines[i].result == Merge(Node(i).buffers.Query(key), ResultAt(i+1))
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
      && this.diskView == linked.diskView
      && this.lines[0].ptr == linked.root
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

  predicate InternalFlushMemtable(v: Variables, v': Variables, lbl: TransitionLabel)
  {
    && v.WF()
    && var newBuffer := Buffer(v.memtable.mapp);
    && v'.linked.diskView.AgreesWithDisk(v.linked.diskView)
      // NB: linked.WF() ==> No nondangling pointers, so in practice linked <= linked'
    && v'.linked.HasRoot()
    && var newBuffers := BufferStack([newBuffer]);
    && v'.linked.Root() == (
      if !v.linked.HasRoot()
      then
        BetreeNode(newBuffers, TotalPivotTable(), [None])
      else
        v.linked.Root().PushBufferStack(newBuffers)
      )
  }

  type PathAddrs = seq<Address>
  
  datatype Path = Path(key: Key, depth: nat)
  {
    // Valid is defined with respect to some DiskView; it checks whether the key can be routed to depth.
    function Subpath() : (out: Path)
      requires 0 < depth
    {
      Path(key, depth-1)
    }

    predicate Valid(linked: LinkedBetree)
      decreases depth
    {
      && linked.WF()
      && linked.HasRoot()
      && linked.Root().KeyInDomain(key)
      && (0 < depth ==> Subpath().Valid(linked.ChildForKey(key)))
    }

    function Target(linked: LinkedBetree) : (out: LinkedBetree)
      requires Valid(linked)
      ensures out.WF()
      ensures out.root.Some?
      ensures out.diskView == linked.diskView
      ensures out.HasRoot() ==> out.root.value in out.diskView.entries
      decreases depth
    {
      if 0 == depth
      then linked
      else Subpath().Target(linked.ChildForKey(key))
    }

    predicate CanSubstitute(linked: LinkedBetree, replacement: LinkedBetree, pathAddrs: PathAddrs) 
    {
      && linked.WF()
      && replacement.WF()
      && depth == |pathAddrs|
      && Valid(linked)
      && linked.diskView.IsSubsetOf(replacement.diskView)
    }

    function Substitute(linked: LinkedBetree, replacement: LinkedBetree, pathAddrs: PathAddrs) : (out: LinkedBetree)
      requires CanSubstitute(linked, replacement, pathAddrs)
      decreases depth, 1
    { 
      if depth == 0 
      then replacement
      else 
        var node := linked.Root();
        var subtree := Subpath().Substitute(linked.ChildForKey(key), replacement, pathAddrs[1..]);
        var newChildren := node.children[Route(node.pivotTable, key) := subtree.root];
        var newNode := BetreeNode(node.buffers, node.pivotTable, newChildren);
        var newDiskView := DiskView.DiskView(subtree.diskView.entries[pathAddrs[0] := newNode]); 
        LinkedBetree(GenericDisk.Pointer.Some(pathAddrs[0]), newDiskView)
    }
  }

  // TODO(tony/jonh): Side quest: now that we know we want predicate-style down
  // here anyway, try retrofitting predicate style definitions into
  // PivotBetree. If it works, maybe we can do some functional decomposition
  // and cut the duplication.

  predicate InternalGrow(v: Variables, v': Variables, lbl: TransitionLabel, step: Step)
  {
    && v.WF()
    && lbl.InternalLabel?
    && step.InternalGrowStep?
    && v.linked.HasRoot()

    && v'.linked.diskView.AgreesWithDisk(v.linked.diskView)
    && v'.linked.HasRoot()
    && v'.linked.Root() == BetreeNode(BufferStack([]), TotalPivotTable(), [v.linked.root])
    && v'.memtable == v.memtable  // UNCHANGED
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
    && root' == root.(
      pivotTable := InsertPivot(root.pivotTable, childIdx, splitKey),

      // replace1with2 is just telling us about the structure of
      // root'.children: the prefix and suffix are identical, and the new left
      // & right child ptrs appear where childIdx once was. But it *doesn't*
      // say anything about the value of leftChildPtr (resp. rightChildPtr),
      // since we fetched those out of root'.children in the var statement
      // above. That's a "clever" trick to leave nondeterminism that says we
      // don't care what the actual values of those pointers are.
      children := replace1with2(root.children, leftChildPtr, rightChildPtr, childIdx)
      )

    // Children get correspending slices
    && leftChildPtr.Some?
    && rightChildPtr.Some?
    && var oldChild := linked.diskView.Get(oldChildPtr);
    && var leftChild := linked'.diskView.Get(leftChildPtr);
    && var rightChild := linked'.diskView.Get(rightChildPtr);
    && leftChild == oldChild.ApplyFilter(Domain(root.pivotTable[childIdx-1], Element(splitKey)))
    && rightChild == oldChild.ApplyFilter(Domain(Element(splitKey), root.pivotTable[childIdx]))

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
    && step.path.Valid(v.linked)
    // v && v' agree on everything down to Target()
    // && step.path.IsSubstitution(v.linked, v'.linked, [])
    // Target and Target' are related by a split operation
    && IsSplit(step.path.Target(v.linked), step.path.Target(v'.linked), step.childIdx, step.splitKey)
    && v'.memtable == v.memtable  // UNCHANGED
  }

  // Is linked'.Root() a Flush(childIdx) of linked.Root()?
  predicate IsFlush(linked: LinkedBetree, linked': LinkedBetree, childIdx: nat)
  {
    && linked.WF()
    && linked'.WF()
    && linked.HasRoot()
    && linked'.HasRoot()
    && linked'.diskView.AgreesWithDisk(linked.diskView)
    && var root := linked.Root();
    && var root' := linked'.Root();

    && root.ValidChildIndex(childIdx)

    && var keepKeys := AllKeys() - root.ChildDomain(childIdx).KeySet();
    && var keptBuffers := root.buffers.ApplyFilter(keepKeys);
    && var movedBuffers := root.buffers.ApplyFilter(root.ChildDomain(childIdx).KeySet());

    // Parent changes buffers & child at childIdx
    && root'.buffers == keptBuffers
    && root'.pivotTable == root.pivotTable
    && root'.children == root.children[childIdx := root'.children[childIdx]]  // this pointer is allowed to change

    // Flushed childs are nearly identical, except for buffers
    && root.children[childIdx].Some?
    && root'.children[childIdx].Some?
    && var child := linked.diskView.Get(root.children[childIdx]);
    && var child' := linked'.diskView.Get(root'.children[childIdx]);

    && child'.buffers == child.buffers.PushBufferStack(movedBuffers)
    && child'.pivotTable == child.pivotTable
    && child'.children == child.children
  }

  // The flush step reaches down a path and applies IsFlush.
  predicate InternalFlush(v: Variables, v': Variables, lbl: TransitionLabel, step: Step)
  {
    // An advantage of predicate-style is that we don't have to explicitly
    // declare BuildTight() (garbage collection); we can leave that to a lower
    // layer.
    // todo: rewrite
    assume false;
    && v.WF()
    && lbl.InternalLabel?
    && step.InternalFlushStep?
    && step.path.Valid(v.linked)
    // v && v' agree on everything down to Target()
    // && step.path.IsSubstitution(v.linked, v'.linked, [])
    // Target and Target' are related by a flush operation
    && IsFlush(step.path.Target(v.linked), step.path.Target(v'.linked), step.childIdx)
    && v'.memtable == v.memtable  // UNCHANGED
  }

  // Compaction on a single node
  predicate IsCompaction(previous: BetreeNode, replacement: BetreeNode)
  {
    && replacement.buffers.Equivalent(previous.buffers)
    && replacement.pivotTable == previous.pivotTable  // UNCHANGED
    && replacement.children == previous.children  // UNCHANGED
  }

  // target is the root node before it is compacted. 
  // InsertReplacement returns a LinkedBetree that has the diskview of target with replacement placed at
  // the replacementAddr
  function InsertCompactReplacement(target: LinkedBetree, replacement: BetreeNode, replacementAddr: Address) : (out: LinkedBetree)
    requires target.WF()
    requires replacement.WF()
    requires target.HasRoot()
    requires IsCompaction(target.Root(), replacement)
    requires target.diskView.IsFresh(replacementAddr)
    ensures out.diskView.entries == target.diskView.entries[replacementAddr := replacement]
    ensures out.WF() 
  {
    var newDiskView := DiskView.DiskView(target.diskView.entries[replacementAddr := replacement]);
    LinkedBetree(GenericDisk.Pointer.Some(replacementAddr), newDiskView)
  }

  predicate InternalCompact(v: Variables, v': Variables, lbl: TransitionLabel, step: Step)
  {
    && step.WF()
    && lbl.InternalLabel?
    && step.InternalCompactStep?
    && step.path.Valid(v.linked)
    && IsCompaction(step.path.Target(v.linked).Root(), step.compactedNode)
    // Fresh!
    && v.linked.diskView.IsFresh(step.targetAddr)
    && SeqHasUniqueElems(step.pathAddrs) 
    && Set(step.pathAddrs) !! v.linked.diskView.entries.Keys
    && {step.targetAddr} !! Set(step.pathAddrs)
    // todo(tony): make tight
    && v'.linked == step.path.Substitute(
        v.linked, 
        InsertCompactReplacement(step.path.Target(v.linked), step.compactedNode, step.targetAddr), 
        step.pathAddrs
    )
    && v'.memtable == v.memtable  // UNCHANGED
  }

  // public:

  predicate Init(v: Variables, stampedBetree: StampedBetree)
  {
    && stampedBetree.value.WF()
    && stampedBetree.value.Acyclic()
    && v == Variables(EmptyMemtable(stampedBetree.seqEnd), stampedBetree.value)
  }

  datatype Step =
      QueryStep(receipt: QueryReceipt)
    | PutStep()
    | QueryEndLsnStep()
    | FreezeAsStep()
    | InternalGrowStep()
    | InternalSplitStep(path: Path, childIdx: nat, splitKey: Key)
    | InternalFlushStep(path: Path, childIdx: nat)
    | InternalCompactStep(path: Path, compactedNode: BetreeNode, targetAddr: Address, pathAddrs: PathAddrs)
  {
    predicate WF() {
      match this {
        case QueryStep(receipt) => receipt.Valid()
        case InternalSplitStep(path, childIdx, splitKey) => true
        case InternalFlushStep(path, childIdx) => true
        case InternalCompactStep(path, compactedNode, _, pathAddrs) =>
          && compactedNode.WF()
          && path.depth == |pathAddrs|
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
      case InternalGrowStep() => InternalGrow(v, v', lbl, step)
      case InternalSplitStep(_, _, _) => InternalSplit(v, v', lbl, step)
      case InternalFlushStep(_, _) => InternalFlush(v, v', lbl, step)
      case InternalCompactStep(_, _, _, _) => InternalCompact(v, v', lbl, step)
    }
  }

  predicate Next(v: Variables, v': Variables, lbl: TransitionLabel) {
    exists step: Step :: NextStep(v, v', lbl, step)
  }
}
