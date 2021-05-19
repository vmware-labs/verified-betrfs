// Copyright 2018-2021 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, and University of Washington
// SPDX-License-Identifier: BSD-2-Clause

include "../lib/Base/total_order.i.dfy"
include "Tables.i.dfy"
include "MsgSeq.i.dfy"

/*
a Betree consists of:
- Trunk nodes. These have routing information, and link to B+trees that store actual messages.
  Links include filters that select particular keys, neutralize old messages.
- Immutable B+trees, allocated in big (many-MB?) chunks, store a batch of messages from
  a rectangle of some keyrange * sequence number window.
- Flush is two steps:
  - "Pushdown"? logically pushes a sub-rectangle of messages to a child trunk node, done by
    forwarding the references.
  - Compact rewrites content from input B+trees to an output B+tree, pushing the input trees
    closer to being freed. This is garbage collection.
- Lookup must:
  - follow an appropriate trunk path
  - Collect non-excluded messages from every linked B+tree
- Allocation must account for:
  - Used trunk nodes. (One CU allocated in an entire AU, evidently.)
  - Batches of CUs (AUs) used to build a B+tree.

So Betree.lookup is a series of trunk nodes, their CUs,
  plus for each a B+tree.lookup, which itself is a series of CUs.

  So maybe the thing to do is stub out the B+tree interface that this thing is going to
  take as a submodule.

  Also, how are we going to do:
  * dependency tracking for when we can free B+trees
    * how do we write down that change in allocation?
    * at this layer, maybe define the Betree allocation as the union of the reachable B+tree
      allocations?
  * indirection table?  each time we replace a trunk node, we want to
    - allocate a new CU to store it in
    - link the parent to this new CU
    - This process doesn't need reference counting, but it does affect the reference
      counts for the B+trees. WAIT YES IT DOES it's a Bedag -- for clone.
    - We do need to adjust allocations when we make the swap.

  How to B+trees get incrementally constructed?
    - At this layer in the refinement stack, maybe they just get incrementally allocated,
    in a way that the increments never get frozen?

  Allocation strategy.
  * At this refinement layer, we'll identify the
    - reachable trunk CUs (Identified by lookups? gulp) and
    - reachable B+tree CU sets.
    - and then our sb.alloc will reflect those sets whenever we freeze.

  * In next layer down, we can't require faulting the entire tree in to compute the alloc,
    so we'll attach it to invariants that track:
    - an allocation table read from the disk representing the base (persistent) image
    - When we de/allocate a trunk CU or B+tree set<CU>, we'll subtract/add them to the table
  Will the invariant connection be via a recursive definition? Gulp. Definitely not if
    trunks form a DAG.
  Will the invariant connection simply be induction invariants that
    - every reachable thing is in the set
    - everything in the set is reachable (ew)
    - no reachable thing overlaps with another reachable thing (ew ew)
  Maybe
    - we ghostily know the set of reachable B+trees. (Can we marshal ghost data across a restart?)
    - we ghostily know the set of reachable trunks.
    - we maintain an invariant between the set of IReads sets of those data structures
    that gives mutual disjointness and that they union to the allocation set.

  Indirection table:
  - There are two kinds of things that need refcounting: B+trees and trunks.
  - We used to think we'd reference count allocated CUs. That doesn't make any sense.
  - But how do we *name* the B+trees and name the trunks? By their roots? Why not? CUs are
    disjoint, so root CUs are unique... and that's also how they're named in pointers.

  - How many trunks are there? How many B+trees?
    - I think we're going to end up storing a table in memory that's shaped very much
    like an allocation table, but has counters.
    - It's going to count refs to CUs.
      - Can we represent this one relationally against a whole DiskView? I think we can!
      forall reachable trunks forall b+trees count once?
    - And then another table is going to connect CU roots to all the CUs (or rather all the AUs)
      for a given data structure.
      - in particular, this second table, at this layer, can be represented by just reading the
      underlying data structures!

*/

module BetreeMachineMod {
  import opened Options
  import opened Sequences
  import opened Maps
  import opened MessageMod
  import opened InterpMod
  import opened AllocationMod
  import opened MsgSeqMod
  import AllocationTableMachineMod
  import IndirectionTableMod
  import CacheIfc

  datatype Superblock = Superblock(
    indTbl: IndirectionTableMod.Superblock,
    allocation: AllocationTableMachineMod.Superblock,
    endSeq: LSN)

  // Is it gross that my Betree knows about the three views?
  // The alternative would be for some outer module to instantiate
  // me three times, and then maintain allocation information on
  // my behalf. How would that look?
  // It would look like Program doing a "Freeze" step that captures the current
  // (indTbl, nextSeq, alloc).
  // Alloc would be non-opaque (so Program could protect the allocation against
  // Journal and ephemeral Btree while freeze gets written to disk).
  // indTbl must be kinda-visible, because someone has to alloc it and escort the dirty
  // pages to disk.
  // Someone has to figure out when this frozen state is all clean (perhaps
  // using some dirty bits in alloc?)
  // None of that seems like a great layering economy. Let's leave Frozen in here.
  //
  // The result is that, down here, we have to protect two separate allocs, I guess.
  datatype Frozen = Idle | Frozen(
    indTbl: IndirectionTableMod.IndirectionTable,
    endSeq: LSN)

  datatype Variables = Starting | Running(
    indTbl: IndirectionTableMod.IndirectionTable,
    memBuffer: map<Key, Message>,  // Real Splinter (next layer down? :v) has >1 memBuffers so we can be inserting at the front while flushing at the back.
    allocation: AllocationTableMachineMod.Variables,

    // TODO add a membuffer to record LSN; a frozen-like transition to keep one membuffer available
    // for filling while packing the other into a b+tree in the top trunk.
    // OR just have freeze drain the membuffer, introducing a write hiccup every 20GB.
    nextSeq: LSN,  // exclusive
    frozen: Frozen
  )
  {
    // A "public" method for Program to inquire how many LSNs are in the tree
    function BetreeEndsLSNExclusive() : LSN { nextSeq }
  }

  predicate Init(v: Variables, sb: Superblock, cache: CacheIfc.Variables)
  {
    && IndirectionTableMod.DurableAt(v.indTbl, cache, sb.indTbl)
    && v.memBuffer == map[]
    //&& v.allocation // TODO clean up this mess
    && v.nextSeq == sb.endSeq
    && v.frozen.Idle?
  }
  
  type TrunkId = nat
  function RootId() : TrunkId { 0 }

  datatype TrunkNode = TrunkNode()
  function parseTrunkNode(b: UninterpretedDiskPage) : Option<TrunkNode>
    // TODO
  function marshalTrunkNode(node: TrunkNode) : UninterpretedDiskPage
    // TODO

  datatype NodeAssignment = NodeAssignment(id: TrunkId, cu: CU, node: TrunkNode)
  {
    predicate InIndTable(v: Variables)
      requires v.Running?
    {
      && id in v.indTbl
      && v.indTbl[id] == cu
    }
    predicate Valid(v: Variables, cache: CacheIfc.Variables)
      requires v.Running?
    {
      && InIndTable(v)
      && var unparsedPage := CacheIfc.ReadValue(cache, cu);
      && unparsedPage.Some?
      && Some(node) == parseTrunkNode(unparsedPage.value)
    }
  }

  // TODO find in library
  function CombineMessages(newer: Message, older: Message) : Message
  function EvaluateMessage(m: Message) : Value
  function MakeValueMessage(value:Value) : Message

  function MessageFolder(newer: map<Key,Message>, older: map<Key,Message>) : map<Key,Message>
  {
		map x : Key | (x in newer.Keys + older.Keys) ::
      if x in newer
      then if x in older
        then CombineMessages(newer[x], older[x])
        else newer[x]
      else older[x]
  }

  datatype TrunkStep = TrunkStep(
    na: NodeAssignment,
    msgs: map<Key, Message>
    // , branchMsgs: seq<map<Key, Message>>, branchAssigment: BranchAssignment   ...
    )
  datatype TrunkPath = TrunkPath(k: Key, steps: seq<TrunkStep>)
  {
    predicate ValidPrefix(cache: CacheIfc.Variables) {
      true // some path from the root
    }

    predicate Valid(cache: CacheIfc.Variables) {
      && ValidPrefix(cache)
      && true // no nodes below this one for k.
    }

    function Decode() : Value
    {
      // filter Messages on k, I guess
      var unflattenedMsgs := seq(|steps|, i requires 0<=i<|steps| => steps[i].msgs);
      var flattenedMsgs := FoldLeft(MessageFolder, map[], unflattenedMsgs);
      if k in flattenedMsgs then EvaluateMessage(flattenedMsgs[k]) else DefaultValue()
    }
  }

  datatype Skolem =
    | QueryStep(trunkPath: TrunkPath)
    | PutStep()
    | FlushStep(flush: FlushRec)
    | DrainMemBufferStep(oldRoot: NodeAssignment, newRoot: NodeAssignment)
    | CompactBranchStep(receipt: CompactReceipt)

  predicate Query(v: Variables, v': Variables, cache: CacheIfc.Variables, key: Key, value: Value, sk: Skolem)
  {
    && v.Running?
    && sk.QueryStep?
    // TODO check memtable!
    && var trunkPath := sk.trunkPath;
    && trunkPath.Valid(cache)
    && trunkPath.k == key
    && trunkPath.Decode() == value
    && v' == v
  }

  predicate PutMany(v: Variables, v': Variables, puts: MsgSeq)
  {
    && v.Running?
    && puts.seqStart == v.nextSeq
    && v' == v.(
      memBuffer := puts.ApplyToKeyMap(v.memBuffer),
      nextSeq := puts.seqEnd
      )
  }

  predicate Put(v: Variables, v': Variables, key: Key, value: Value, sk: Skolem)
  {
    && v.Running?
    && sk.PutStep?
    && var newMessage := MakeValueMessage(value);
    && v' == v.(memBuffer := v.memBuffer[key := newMessage], nextSeq := v.nextSeq + 1)
  }
  
  datatype FlushRec = FlushRec(
    trunkPath: TrunkPath,
    newParent: NodeAssignment,
    newChild: NodeAssignment)
  {
    predicate WF() {
      2<=|trunkPath.steps|
    }
    predicate Valid(cache: CacheIfc.Variables) {
      && WF()
      && trunkPath.ValidPrefix(cache)
    }
    function ParentStep() : TrunkStep
      requires WF()
      { trunkPath.steps[|trunkPath.steps|-2] }
    function ChildStep() : TrunkStep
      requires WF()
      { trunkPath.steps[|trunkPath.steps|-1] }
    function ParentNode() : TrunkNode
      requires WF()
      { ParentStep().na.node }
    function ChildNode() : TrunkNode
      requires WF()
      { ChildStep().na.node }
  }

  predicate FlushesNodes(oldParent: TrunkNode, oldChild: TrunkNode, newParent: TrunkNode, newChild: TrunkNode) {
    true // TODO
  }
  
  predicate CUIsAllocatable(cu: CU)
  {
    && true // TODO cu unallocated across all live views
  }

  // Internal operation; noop
  predicate Flush(v: Variables, v': Variables, cache: CacheIfc.Variables, cacheOps: CacheIfc.Ops, sk: Skolem)
  {
    && v.Running?
    && sk.FlushStep?
    && var flush := sk.flush;
    && flush.Valid(cache)
    // TODO keep the parent's trunkId, but move the child, so that other nodes' outbound links
    // to existing child don't change.
    && FlushesNodes(flush.ParentNode(), flush.ChildNode(), flush.newParent.node, flush.newChild.node)
    && flush.newParent.id == flush.ParentStep().na.id  // parent keeps its id
    && true // UnusedId(flush.newChild.id) child gets id unallocated in eph ind tbl
    && CUIsAllocatable(flush.newParent.cu)
    && CUIsAllocatable(flush.newChild.cu)
    && cacheOps == [
      CacheIfc.Write(flush.newParent.cu, marshalTrunkNode(flush.newParent.node)),
      CacheIfc.Write(flush.newChild.cu, marshalTrunkNode(flush.newChild.node))
      ]
    && v' == v.(indTbl := v.indTbl
      [flush.ParentStep().na.id := flush.newParent.cu]
      [flush.newChild.id := flush.newChild.cu])  // TODO breaks other dag neighbors
  }

  predicate MergeBuffer(oldNode: TrunkNode, memBuffer: map<Key, Message>, newNode: TrunkNode)
  {
    true // tODO
  }

  // Internal
  // drain mem buffer into a B+tree in the root trunk node
  predicate DrainMemBuffer(v: Variables, v': Variables, cache: CacheIfc.Variables, cacheOps: CacheIfc.Ops, sk:Skolem)
  {
    && v.Running?
    && sk.DrainMemBufferStep?
    && var oldRoot := sk.oldRoot;
    && var newRoot := sk.newRoot;
    && oldRoot.id == RootId()
    && oldRoot.Valid(v, cache)
    && newRoot.id == RootId()
    // when we're done, newRoot.Valid(v', cache')

    && CUIsAllocatable(newRoot.cu)
    && MergeBuffer(oldRoot.node, v.memBuffer, newRoot.node)
    && cacheOps == [ CacheIfc.Write(newRoot.cu, marshalTrunkNode(newRoot.node)) ]
    && v' == v.(
      indTbl := v.indTbl[RootId() := newRoot.cu],
      memBuffer := map[]
      )
  }

  datatype CompactReceipt = CompactReceipt(path: TrunkPath, newna: NodeAssignment)
  {
    predicate WF() {
      && 0 < |path.steps|
    }
    function Oldna() : NodeAssignment
      requires WF()
    {
      Last(path.steps).na
    }
    predicate Valid(cache: CacheIfc.Variables)
    {
      && WF()
      && path.Valid(cache)
      && Oldna().id == newna.id
    }
  }

  predicate EquivalentNodes(a: TrunkNode, b: TrunkNode) {
    true // TODO
  }

  // Internal operation; noop
  // Rearrange mem buffers in some node
  predicate CompactBranch(v: Variables, v': Variables, cache: CacheIfc.Variables, cacheOps: CacheIfc.Ops, sk: Skolem)
  {
    && v.Running?
    && sk.CompactBranchStep?
    && var r := sk.receipt;
    && r.Valid(cache)
    && CUIsAllocatable(r.newna.cu)
    && EquivalentNodes(r.Oldna().node, r.newna.node)  // Buffer replacements
      // TODO need to establish replacement B+tree is correct
    && cacheOps == [ CacheIfc.Write(r.newna.cu, marshalTrunkNode(r.newna.node)) ]
    && v' == v.(indTbl := v.indTbl[r.newna.id := r.newna.cu])
  }

  predicate Freeze(v: Variables, v': Variables)
  {
    && v.Running?
    && v.frozen.Idle?
    && v.memBuffer == map[]  // someday we'd like to avoid clogging the memtable during freeze, but...
    && v' == v.(frozen := Frozen(v.indTbl,  v.nextSeq))
  }

  predicate KnowFrozenIsClean(v: Variables, sb: Superblock, cache: CacheIfc.Variables)
  {
    true // TODO
  }

  predicate Internal(v: Variables, v': Variables, cache: CacheIfc.Variables, cacheOps: CacheIfc.Ops, sk: Skolem)
  {
    || Flush(v, v', cache, cacheOps, sk)
    || DrainMemBuffer(v, v', cache, cacheOps, sk)
    || CompactBranch(v, v', cache, cacheOps, sk)
  }

  predicate CommitStart(v: Variables, v': Variables, cache: CacheIfc.Variables, sb: Superblock, newBoundaryLSN: LSN)
  {
    && v.Running?
    && v.frozen.Frozen?
    && KnowFrozenIsClean(v, sb, cache)
    && sb.endSeq == v.frozen.endSeq
    && v' == v
  }

  predicate CommitComplete(v: Variables, v': Variables, cache: CacheIfc.Variables, sb: Superblock)
  {
    && v.Running?
    // TODO need to update the persistent table to keep our allocation set correct
    && v' == v.(frozen := Idle)
  }

/*
  predicate ReachableTrunk(sb: Superblock, trunkRoot: CU)
  {
    && true // TODO -- lookup-y definition
  }

  predicate ReachableBranch(cache: CacheIfc.Variables, sb: Superblock, branchRoot: CU)
  {
    // NB: no indirection from trunks to branches -- but there is refcounting here. Use multiset representation for IReads, I guess.
    exists trunkCU, trunkNode, branchIdx ::
      && ReachableTrunk(sb, trunkCU)
      && var unparsedPage := CacheIfc.ReadValue(cache, trunkCU);
      && unparsedPage.Some?
      && var trunkNode := parseTrunkNode(unparsedPage.value);
      && trunkNode.Some?
      // TODO trunk nodes need some guts
      //&& trunkNode.value.branches[branchIdx] == branchRoot
  }

  predicate BranchMember(sb: Superblock, branchRoot: CU, block: CU)
  {
    && true // TODO -- this defn belongs inside branch module
  }

  predicate ReachableBlock(cache: CacheIfc.Variables, sb: Superblock, cu: CU)
  {
    || ReachableTrunk(cache, trunkCu)
    || (exists branch ::
      && ReachableBranch(cache, sb, trunkCu)
      && BranchMember(branchRoot, cu))
  }
*/

  // And then IReads <= ReachableBlocks == alloc.
  // We can prove this because anything in IReads justifies ReachableTrunk (and maybe BranchMember).

  function AllocationOnDisk(cache: CacheIfc.Variables, sb: Superblock) : Option<AllocationTableMachineMod.Variables>
  {
    if exists allocation :: AllocationTableMachineMod.DurableAt(allocation, cache, sb.allocation)
    then var allocation :| AllocationTableMachineMod.DurableAt(allocation, cache, sb.allocation);
      Some(allocation)
    else
      None
  }

  function Alloc(v: Variables, cache: CacheIfc.Variables, sb: Superblock) : set<CU>
  {
    if v.Running?
    then AllocationTableMachineMod.Alloc(v.allocation)
    else if AllocationOnDisk(cache, sb).Some?
    then
      // Module hasn't started; use allocation info it will eventually read from disk
      set s | s in AllocationOnDisk(cache, sb).value.Allocated()
    else
      // disk is borked; return nonsense
      {}
  }
}

module BetreeInterpMod {
  import opened Options
  import opened MessageMod
  import opened InterpMod
  import opened AllocationMod
  import opened MsgSeqMod
  import IndirectionTableMod
  import opened BetreeMachineMod
  import Nat_Order

  datatype LookupRecord = LookupRecord(
    cu: CU
  )
  type Lookup = seq<LookupRecord>

  // Select the messages that lookup finds.
  function LookupToValue(lookup: Lookup) : Value
    // TODO body

  predicate ValidLookup(v: Variables, cache: CacheIfc.Variables, key: Key, lookup: Lookup)
    // TODO

  // What indirection table would we see if the system were running?
  function ITbl(v: Variables, cache: CacheIfc.Variables, sb: Superblock) : Option<IndirectionTableMod.IndirectionTable> {
    match v {
      case Starting => IndirectionTableMod.I(cache.dv /*TODO change ind tbl to expect cache*/, sb.indTbl)
      case Running => Some(v.indTbl)
    }
  }

  function IMKey(v: Variables, cache: CacheIfc.Variables, sb: Superblock, key: Key) : Value
  {
    var indTbl := ITbl(v, cache, sb);
    if
      && indTbl.Some?
      && exists lookup :: ValidLookup(v, cache, key, lookup)
    then
      var lookup :| ValidLookup(v, cache, key, lookup);
      LookupToValue(lookup)
    else
      DefaultValue()
  }

  function IM(v: Variables, cache: CacheIfc.Variables, sb: Superblock) : (i:Interp)
    ensures i.WF()
  {
    Interp(imap key | key in AllKeys() :: IMKey(v, cache, sb, key), sb.endSeq)
  }

  function IReadsKey(v: Variables, cache: CacheIfc.Variables, sb: Superblock, key: Key) : set<AU> {
    var indTbl := ITbl(v, cache, sb);
    if
      && indTbl.Some?
      && exists lookup :: ValidLookup(v, cache, key, lookup)
    then
      var lookup :| ValidLookup(v, cache, key, lookup);
      set i | 0<=i<|lookup| :: var lr:LookupRecord := lookup[i]; lr.cu.au
    else
      {}
  }

  function IReadsSet(v: Variables, cache: CacheIfc.Variables, sb: Superblock) : set<AU> {
    set au:AU |
      && au < AUSizeInCUs()
      && exists key :: au in IReadsKey(v, cache, sb, key)
  }

  function IReads(v: Variables, cache: CacheIfc.Variables, sb: Superblock) : seq<AU>
    ensures forall au :: au in IReads(v, cache, sb) <==> au in IReadsSet(v, cache, sb)
  {
    Nat_Order.SortSet(IReadsSet(v, cache, sb))
  }

  lemma Framing(v: Variables, cache0: CacheIfc.Variables, cache1: CacheIfc.Variables, sb:Superblock)
    requires DiskViewsEquivalentForSet(cache0.dv, cache1.dv, IReads(v, cache0, sb))
    ensures IM(v, cache0, sb) == IM(v, cache1, sb)
  {
    // TODO I'm surprised this proof passes easily.
    // narrator: It doesn't.
    forall key | key in AllKeys()
      ensures IMKey(v, cache0, sb, key) == IMKey(v, cache1, sb, key)
    {
      var indTbl0 := ITbl(v, cache0, sb);
      var indTbl1 := ITbl(v, cache1, sb);
      if indTbl0.Some? && indTbl1.Some?
      {
        var le0 := exists lookup0 :: ValidLookup(v, cache0, key, lookup0);
        var le1 := exists lookup1 :: ValidLookup(v, cache1, key, lookup1);
        if le0 {
          var lookup0 :| ValidLookup(v, cache0, key, lookup0);
          assume ValidLookup(v, cache1, key, lookup0);
        }
        if le1 {
          var lookup1 :| ValidLookup(v, cache1, key, lookup1);
          assume ValidLookup(v, cache0, key, lookup1);
        }
        assert le0 == le1;
        if (le0) {
          // This definitely won't work.
          var lookup0 :| ValidLookup(v, cache0, key, lookup0);
          var lookup1 :| ValidLookup(v, cache1, key, lookup1);
          calc {
            IMKey(v, cache0, sb, key);
              { assume false; } // var|
            LookupToValue(lookup0);
              { assume false; } // framing
            LookupToValue(lookup1);
              { assume false; } // var|
            IMKey(v, cache1, sb, key);
          }
        } else {
          calc {
            IMKey(v, cache0, sb, key);
            DefaultValue();
            IMKey(v, cache1, sb, key);
          }
        }
      }
    }
  }

  lemma PutEffect(v: Variables, v': Variables, cache: CacheIfc.Variables, cache': CacheIfc.Variables, sb: Superblock, key: Key, value: Value, sk: Skolem)
    ensures IM(v', cache', sb) == IM(v, cache, sb).Put(key, value)
  {
  }
}
