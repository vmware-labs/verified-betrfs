// Copyright 2018-2021 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, and University of Washington
// SPDX-License-Identifier: BSD-2-Clause

include "SequenceSets.i.dfy"
include "../lib/Base/total_order.i.dfy"
include "../lib/Base/Maps.i.dfy"
include "IndirectionTable.i.dfy"
include "AllocationTable.i.dfy"
include "AllocationTableMachine.i.dfy"
include "MsgHistory.i.dfy"
include "../Spec/Message.s.dfy"
include "../Spec/Interp.s.dfy"
include "BranchTree.i.dfy"
include "BranchTreeInterp.i.dfy"
include "MsgSeq.i.dfy"
include "../lib/Buckets/BoundedPivotsLib.i.dfy"

/*
a Splinter tree consists of:
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

So Splintertree.lookup is a series of trunk nodes, their CUs,
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

// trunk nodes and IndirectionTable (makes trunk nodes behave like they're mutable)
// immutable b+trees
// Index/leaf nodes in the b+trees

module SplinterTreeMachineMod {
  import opened Options
  import opened Sequences
  import opened Maps
  import opened SequenceSetsMod
  import opened ValueMessage
  import opened KeyType
  import opened InterpMod
  import opened DiskTypesMod
  import opened AllocationMod
  import opened MsgHistoryMod
  import AllocationTableMachineMod
  import IndirectionTableMod
  import CacheIfc
  import MsgSeqMod
  import opened BoundedPivotsLib

  // I'd rather not have to pull the whole interp library in here,
  // but export sets really blow.
  import BranchTreeInterpIfc

  // TODO: Rename this module
  datatype Superblock = Superblock(
    indTbl: IndirectionTableMod.Superblock,
    endSeq: LSN,
    root: CU)

  // This has to mkfs the initial root of the trunk tree which is just an
  // empty trunk node -- TODO: finish
  predicate Mkfs(dv: DiskView, treeRootCU: CU)
  {
    parseTrunkNode(dv[treeRootCU]) == Some(Leaf([]))
  }

  function MkfsSuperblock(rootCU : CU) : Superblock
  {
    Superblock(IndirectionTableMod.EmptySuperblock(), 0, rootCU)
  }


  function parseTrunkNode(b: UninterpretedDiskPage) : Option<TrunkNode>
      // TODO

  // Parses CU units to BranchNodes that we can use
  function CUToTrunkNode(cache: CacheIfc.Variables, cu : CU) : Option<TrunkNode>
    {
        var diskPage := CacheIfc.ReadValue(cache, cu);
        if diskPage == None
        then
          None
        else
          parseTrunkNode(diskPage.value)
    }


  function marshalTrunkNode(node: TrunkNode) : UninterpretedDiskPage
      // f

  type TrunkId = nat
  function RootId() : TrunkId { 0 }

  datatype NodeAssignment = NodeAssignment(id: TrunkId, cu: CU, node: TrunkNode)
  {

    predicate WF()
    {
       && node.WF()
       && cu in CUsInDisk()
       // Note that every piece of information associated with a node must exist in the trunkNode
       // Since it has to parsable from a cu. We could get rid of this here?
    }

    predicate Valid(v: Variables, cache: CacheIfc.Variables)
    {
      && WF()
      && node.Valid(v, cache)
    }
  }

  // Note that branches are ordered from oldest to youngest. So 0 is the oldest branch and 1 is the youngest
  // activeBranches tells us the lowest index of an active branch tree for the corresponding child
  datatype TrunkNode =
    | Index(branches : seq<BranchTreeInterpIfc.BranchTop>,
        children : seq<CU>,
        pivots : PivotTable,
        activeBranches : seq<nat>)
    | Leaf(branches : seq<BranchTreeInterpIfc.BranchTop>)
  {

    predicate WFIndexNode()
      requires this.Index?
    {
      && WFPivots(pivots)
      && |children| == NumBuckets(pivots)
      && |children| == |activeBranches|
      // activeBranches can only point to actual branch trees
      && (0 < |branches| ==> forall i |  0 <= i < |activeBranches| :: 0 <= activeBranches[i] < |branches|)
    }

    predicate WF()
    {
       && this.Index? ==> WFIndexNode()
    }

    predicate ValidCU(cache : CacheIfc.Variables)
    {
//      && var unparsedPage := CacheIfc.ReadValue(cache, cu);
//      && unparsedPage.Some?
//      && var node := parseTrunkNode(unparsedPage.value);
//      && node.Some?
//      && this == node.value
      true
    }

    predicate Valid(v: Variables, cache: CacheIfc.Variables)
    {
      && WF()
      && ValidCU(cache)
    }

    function nextStep(k : Key) : CU
      requires this.Index?
      requires WFIndexNode()
      requires BoundedKey(pivots, k)
    {
      var slot := Route(pivots, k);
      children[slot]
    }

    // TODO: Collapse all the in all the branch nodes in this level
    function AllMessages() : map<Key, Message>
  }

  // Three states : STatble persistent disk state , ephemeral working state and a frozen ephemeral state
  // that's being written out

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

  datatype Variables = Variables(
    // Write Opt file systems allows us to leverage immutability to simplfy reasoning about crash safety using cow
    // Add a layer of indirection over Immutable splinter tree. This indirection table adds mutability over the tree
    indTbl: IndirectionTableMod.IndirectionTable,
    memBuffer: map<Key, Message>,  // Real Splinter (next layer down? :v) has >1 memBuffers so we can be inserting at the front while flushing at the back.
    // TODO add a membuffer to record LSN; a frozen-like transition to keep one membuffer available
    // for filling while packing the other into a b+tree in the top trunk.
    // OR just have freeze drain the membuffer, introducing a write hiccup every 20GB.
    nextSeq: LSN,  // exclusive
    frozen: Frozen,
    root : CU // The CU to the root of the trunk tree
    // we need this because we need ro
    //rootNode : TrunkNode
  )
  {
      predicate WF()
      {
        root in CUsInDisk()
      }

      predicate Valid(cache : CacheIfc.Variables)
      {
        && WF()
        && var diskPage := CacheIfc.ReadValue(cache, root);
        && diskPage.Some?
        && parseTrunkNode(diskPage.value).Some?
      }

      function rootNode(cache : CacheIfc.Variables) : TrunkNode
        requires Valid(cache)
      {
        CUToTrunkNode(cache, root).value
      }

      function BetreeEndsLSNExclusive() : LSN {
        nextSeq
      }

      function getRoot() : CU {
        root
      }
  }

  // We need this for lookup no?
  function FindCorrectBranch(v : Variables, k: Key) : Option<TrunkPath>

  // TODO replay log!
  predicate Start(v: Variables, v': Variables, cache: CacheIfc.Variables, sb: Superblock)
  {
    // Note predicate-style assignment of some fields of v'
    && IndirectionTableMod.DurableAt(v'.indTbl, cache, sb.indTbl) // Parse ind tbl from cache
    && v'.memBuffer == map[]
    && v'.nextSeq == sb.endSeq
    && v'.frozen == Idle
  }

  datatype TrunkStep = TrunkStep(
    // The information about the trunk node of this step
    na: NodeAssignment,
    // The Branch Receipts of a lookup from all the branches of this trunk node
    branchReceipts: seq<BranchTreeInterpIfc.BranchReceipt>)
    // The messages accumulated in till the previous trunkStep -- don't need this might change later
    // accumulatedMsgs: seq<Message>)
  {
    predicate WF()
    {
      && na.WF()
      && ( forall i | 0 <= i < |branchReceipts| :: branchReceipts[i].WF() )
      // We have all the receipts. Does this go in WF() or Valid()??
      && |branchReceipts| == |na.node.branches|
    }

    predicate hasSameKey(key : Key) {
      ( forall i | 0 <= i < |branchReceipts| :: branchReceipts[i].Key() == key )
    }

    function MsgSeqRecurse(count : nat) : (out: seq<Message>)
      requires WF()
      requires count <= |branchReceipts|
    {
      if count == 0
      then
        []
      else
        assert branchReceipts[count-1].WF();
        //assert branchReceipts[count-1].branchPath.WF();
        var currBranchVal := branchReceipts[count-1].Decode();
        ( if currBranchVal.Some?
        then
          [currBranchVal.value]
        else [] )
        + MsgSeqRecurse(count - 1)

    }

    // Messages in all the branch receipts at this layer
    function MsgSeq() : seq<Message>
      requires WF()
    {
      MsgSeqRecurse(|branchReceipts|)
    }

    predicate ValidCUsInductive(cus: seq<CU>, count : nat)
      requires WF()
      requires count <= |branchReceipts|
    {
      && na.cu in cus
      && (forall i | 0<=i<=count-1 :: branchReceipts[i].ValidCUs())
      && (forall i | 0<=i<=count-1 :: SequenceSubset(branchReceipts[i].CUs(), cus))
      && (forall cu | cu in cus :: cu in CUsInDisk())
    }

    function CUsRecurse(count: nat) : (cus: seq<CU>)
      requires WF()
      requires count <= |branchReceipts|
      ensures ValidCUsInductive(cus, count)
    {
      if count == 0
      then
         // add trunk node
        assert na.cu in CUsInDisk();
        [na.cu]
      else
        var branch := branchReceipts[count-1];
        assert branch.WF(); // TRIGGER (Seems to have trouble parsing this from the forall)
        assert branch.ValidCUs();
        branch.CUs() + CUsRecurse(count - 1)
    }

    predicate ValidCUs(cus: seq<CU>)
      requires WF()
    {
      ValidCUsInductive(cus, |branchReceipts|)
    }

    function {:opaque} CUs() : (cus: seq<CU>)
      requires WF()
      ensures na.cu in cus
      ensures ValidCUs(cus)
    {
      CUsRecurse(|branchReceipts|)
    }

    predicate Valid(v: Variables, cache: CacheIfc.Variables)
       requires WF()
    {
      && na.Valid(v, cache)
      && ( forall i | 0 <= i < |branchReceipts| :: branchReceipts[i].Valid(cache) )
      // Note: Here we require one to one correspondance between the node's branches and the corresponding look up receipt
      && (forall i | 0 <= i < |branchReceipts| :: na.node.branches[i] == branchReceipts[i].Top())
      && var cus := CUs();
      && ValidCUs(cus)
    }

  }

  datatype TrunkPath = TrunkPath(k: Key,
                                 membufferMsgs: seq<Message>,
                                 steps: seq<TrunkStep>)
  {

    predicate WF() {
       // Every path should at least have a root
       && 0 < |steps|
       // All the nodes but the last one shound be Index nodes
       && (forall i | 0 <= i < |steps|-1 :: steps[i].na.node.Index?)
       //  The last step's node has to be a Leaf
       && (0 < |steps| ==> steps[|steps| - 1].na.node.Leaf?)
       && (forall i | 0 <= i < |steps| :: steps[i].WF())
       // BoundedKey is derivable from ContainsRange, but that requires a mutual induction going down
       // the tree. It's easier to demand forall-i-BoundedKey so that we can call Route to get the slots
       // for ContainsRange.
       && (forall i | 0 <= i < |steps|-1 :: BoundedKey(steps[i].na.node.pivots, k))
       && (forall i | 0 <= i < |steps| :: steps[i].hasSameKey(k))
     }

     predicate LinkedAt(childIdx : nat)
       requires 0 < childIdx < |steps|
       requires WF()
     {
       && var parentNode := steps[childIdx-1].na.node;
       && var childStep := steps[childIdx].na;
       && var slot := Route(parentNode.pivots, k);
       // When coverting to clone edges use, ParentKeysInChildRange in TranslationLib
       && (childIdx < |steps|-1 ==> ContainsRange(childStep.node.pivots, parentNode.pivots[slot], parentNode.pivots[slot+1]))
       && childStep.cu == parentNode.children[slot]
     }

     predicate Linked()
       requires WF()
     {
       && (forall i | 0 < i < |steps| :: LinkedAt(i))
     }

    predicate {:opaque} ValidPrefix()
      requires WF()
    {
      // TODO: show that the child is also right pivot  // Find from Rob's pivot library
      && forall i :: (0 < i < |steps|) && steps[i].na.cu in steps[i-1].na.node.children
    }


    function msgSeqRecurse(count : nat) : (out : seq<Message>)
      requires WF()
      requires count <= |steps|
    {
      if count == 0
      then
          membufferMsgs
      else
         msgSeqRecurse(count-1) + steps[count-1].MsgSeq()
    }

    // Collapse all the messages in this trunk path
    function MsgSeq() : (out : seq<Message>)
      requires WF()
    {
      msgSeqRecurse(|steps|)
    }

    predicate ContainsAllStepCUs(cus: seq<CU>, step : TrunkStep)
      requires WF()
      requires step.WF()
    {
      && SequenceSubset(step.CUs(), cus)
    }


    predicate ValidCUsInductive(cus: seq<CU>, count : nat)
      requires WF()
      requires count <= |steps|
    {
      && (forall i | 0<=i<count :: steps[i].ValidCUs(cus))
      && (forall i | 0<=i<count :: ContainsAllStepCUs(cus, steps[i]))
    }

    // Return the sequence of CUs (aka nodes) this path touches
    function CUsRecurse(count : nat) : (cus : seq<CU>)
      requires WF()
      requires count <= |steps|
      ensures (forall i | 0<=i<count
        :: ValidCUsInductive(cus, count))
    {
       if count == 0
       then
         []
       else
         steps[count-1].CUs() +  CUsRecurse(count - 1)
    }

    predicate ValidCUs(cus: seq<CU>)
      requires WF()
    {
      ValidCUsInductive(cus, |steps|)
    }

    // Return the sequence of CUs (aka nodes) this path touches
    function  CUs() : (cus: seq<CU>)
      requires WF()
      ensures ValidCUs(cus)
    {
      CUsRecurse(|steps|)
    }

    // TODO: reorg into WF

    predicate Valid(v : Variables, cache: CacheIfc.Variables)
    {
      && WF()
      && (forall i | (0 <= i < |steps|) :: steps[i].Valid(v, cache))
      && (0 < |steps| ==> steps[0].na.id == RootId()) // check for root
      && 0 < |MsgSeq()|
      && Last(MsgSeq()).Define?
      && ValidPrefix()
      // check that the first step is the root
      && (0 < |steps| ==> steps[0].na.cu == v.root)
      // make sure we have the valid memBuffer lookup for this prefix
      && membufferMsgs == MemtableLookup(v, k)
      // NOte that cu corresponds to the correct node assignment
      && (forall i | 0 <= i < |steps| :: steps[i].Valid(v, cache))
      && Linked()
      // ensure that the path belongs to the tree in Variables
    }

    function Decode() : (msg : Message)
      requires WF()
      ensures msg.Define?
    {
      var msg := MsgSeqMod.CombineDeltasWithDefine(MsgSeq());
      if msg.None?
      then
        DefaultMessage()
      else
        msg.value
    }
  }

  // QUESTION: Not everything is compacted all at once, should we have this Recipt
  // also have what branches we're compacting
  datatype CompactReceipt = CompactReceipt(nodeIdx: nat, path: TrunkPath, newna: NodeAssignment)
  {
    predicate WF() {
      && 0 < |path.steps|
      && 0 <= nodeIdx < |path.steps|
    }

    function Oldna() : NodeAssignment
      requires WF()
    {
       Last(path.steps).na
    }

    predicate Valid(v : Variables, cache: CacheIfc.Variables)
    {
      && WF()
      && path.Valid(v, cache)
      && Oldna().id == newna.id
      && var oldna := path.steps[nodeIdx].na;
      && IsCompaction(oldna, newna)
    }

  }

  datatype Skolem =
    | QueryStep(trunkPath: TrunkPath)
    | PutStep()
    | FlushStep(flush: FlushRec) // pushdown branch pointers to children
    | DrainMemBufferStep(oldRoot: NodeAssignment, newRoot: NodeAssignment) // Push the memory only stuff into the persistent root of spliten tree as a branctree
    | CompactBranchStep(receipt: CompactReceipt) // Rewrite branches into a new branch.
    | BranchInteralStep(branchSk : BranchTreeInterpIfc.Skolem)


  function MemtableLookup(v: Variables, key: Key) : seq<Message>
  {
    if key in v.memBuffer
    then
      [v.memBuffer[key]]
    else
      []
  }

  // A valid lookup is something that produces a non DefaultMessage from the membuffer or has a valid trunk path
  // in the splinter tree
  predicate ValidLookup(v: Variables, cache: CacheIfc.Variables, key: Key, trunkPath : TrunkPath)
  {
    && trunkPath.Valid(v, cache)
    && trunkPath.k == key
  }

  predicate Query(v: Variables, v': Variables, cache: CacheIfc.Variables, key: Key, value: Value, sk: Skolem)
  {
    && sk.QueryStep?
    && var trunkPath := sk.trunkPath;
    && ValidLookup(v, cache, key, trunkPath)
    && EvaluateMessage(trunkPath.Decode()) == value
    // No change to the state
    && v == v'
  }

  predicate Put(v: Variables, v': Variables, key: Key, value: Value, sk: Skolem)
  {
    && sk.PutStep?
    && var newMessage := MakeValueMessage(value);
    && v' == v.(memBuffer := v.memBuffer[key := newMessage], nextSeq := v.nextSeq + 1)
  }

  predicate PutMany(v: Variables, v': Variables, puts: MsgSeq)
    requires puts.WF()
  {
    &&  v' == v.(memBuffer := puts.ApplyToKeyMap(v.memBuffer), nextSeq := v.nextSeq + puts.Len())
  }

  datatype FlushRec = FlushRec(
    trunkPath: TrunkPath,
    oldParentIdx: nat,
    newParent: NodeAssignment,
    newChild: NodeAssignment)
  {
    predicate WF() {
      && trunkPath.WF()
      && newParent.WF()
      && newChild.WF()
      && newParent.node.Index?
      && 0 <= oldParentIdx < |trunkPath.steps|-1
      && trunkPath.steps[oldParentIdx].na.node.Index?
    }
    predicate Valid(v: Variables, cache: CacheIfc.Variables) {
      && WF()
      && trunkPath.Valid(v, cache)
      && trunkPath.ValidPrefix()
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

  predicate IsCompaction(oldna : NodeAssignment, newna : NodeAssignment)
  {
   true
   // TODO: Need to finish the relation between BranchTreeMod and BranchTreeStackMod before then
  }

  predicate Compaction(v: Variables, v': Variables, cache: CacheIfc.Variables, sk: Skolem)
    requires v.WF()
    requires v'.WF()
  {
    && v.Valid(cache)
    && v'.Valid(cache)
    && sk.CompactBranchStep?
    && sk.receipt.Valid(v, cache)
    && var nodeIdx := sk.receipt.nodeIdx;
    && var oldna := sk.receipt.path.steps[nodeIdx].na;
    && IsCompaction(oldna, sk.receipt.newna)
  }

  // TODO: We need make sure this flush op is flushing entire prefix of local trunk versions
  // We could make this a separate Flush receipt ??
  predicate FlushesNodes(oldParent: TrunkNode, oldChild: NodeAssignment, newParent: TrunkNode, newChild: NodeAssignment)
    requires oldParent.WF()
    requires newParent.WF()
    requires oldChild.WF()
    requires newChild.WF()
    requires oldParent.Index?
    requires newParent.Index?
  {
    // ensure that they're still children of the parent
    && newChild.cu in newParent.children
    && oldChild.cu in oldParent.children
    && newParent.branches == oldParent.branches
    && newParent.children == oldParent.children
    && (oldChild.node.Index? ==> && newChild.node.Index?
                            && newChild.node.children == oldChild.node.children
                            // Our flush is only one layer, so the activeBranches here shouldn't change
                            && newChild.node.activeBranches == oldChild.node.activeBranches)
    // check that newChild got a branch from the oldParent
    && var oldChildId :| (0 <= oldChildId < |oldParent.children|) && oldParent.children[oldChildId] == oldChild.cu;
    && var newChildId :| (0 <= newChildId < |newParent.children|) && newParent.children[newChildId] == newChild.cu;
    && oldChildId == newChildId
    // for now we're flushing all current branches??
    && (forall i | oldParent.activeBranches[oldChildId] <= i < |oldParent.branches| :: oldParent.branches[i] in newChild.node.branches)
    && assert newParent.WF();
    && assert |newParent.activeBranches| == |newParent.children|;
    && assert 0 <= newChildId < |newParent.children|;
    && newParent.activeBranches[newChildId] == |newParent.branches|
  }

  predicate ValidLookupHasCU(v: Variables, cache: CacheIfc.Variables, lookup: TrunkPath, cu: CU)
  {
    && lookup.Valid(v, cache)
    && cu in lookup.CUs()
  }


 function {:opaque} IReads(v: Variables, cache: CacheIfc.Variables) : set<CU> {
   set cu:CU |
     && cu in CUsInDisk()
     && (exists lookup :: ValidLookupHasCU(v, cache, lookup, cu))
    :: cu
 }

 function IReadsSeq(v: Variables, cache: CacheIfc.Variables) : seq<CU> {
   ArbitrarySequentialization(IReads(v, cache))
 }


  predicate CUIsAllocatable(v: Variables, cache: CacheIfc.Variables, cu: CU)
  {
    && cu in CUsInDisk()
    // TODO : we have to make sure the cu is not in the frozen/persistent copies of the tree nor in the journal
    && cu !in IReads(v, cache)

  }

  // Internal operation; noop -- atomic
  predicate Flush(v: Variables, v': Variables, cache: CacheIfc.Variables, cacheOps: CacheIfc.Ops, sk: Skolem)
  {
    && sk.FlushStep?
    && var flush := sk.flush;
    && flush.Valid(v, cache)
    // TODO keep the parent's trunkId, but move the child, so that other nodes' outbound links
    // to existing child don't change.
    && FlushesNodes(flush.ParentNode(), flush.ChildStep().na, flush.newParent.node, flush.newChild)
    && flush.newParent.id == flush.ParentStep().na.id  // parent keeps its id
    && true // UnusedId(flush.newChild.id) child gets id unallocated in eph ind tbl
    && CUIsAllocatable(v, cache, flush.newParent.cu)
    && CUIsAllocatable(v, cache, flush.newChild.cu)
    && cacheOps == [
      CacheIfc.Write(flush.newParent.cu, marshalTrunkNode(flush.newParent.node)),
      CacheIfc.Write(flush.newChild.cu, marshalTrunkNode(flush.newChild.node))
      ]
    && v' == v.(indTbl := v.indTbl
      [flush.ParentStep().na.id := flush.newParent.cu]
      [flush.newChild.id := flush.newChild.cu])  // TODO breaks other dag neighbors
  }

  // the newNode must contain all the messages in the oldNode and memBuffer combined.
  // merge the two memBuffer has the most uptodate updates
  // QUESTION : Why do we need this??
  predicate MergeBuffer(oldNode: TrunkNode, memBuffer: map<Key, Message>, newNode: TrunkNode)
  {
    && MapUnionPreferA(memBuffer, oldNode.AllMessages()) == newNode.AllMessages()
  }

  // Internal
  // drain mem buffer into a B+tree in the root trunk node
  predicate DrainMemBuffer(v: Variables, v': Variables, cache: CacheIfc.Variables, cacheOps: CacheIfc.Ops, sk:Skolem)
  {
    && sk.DrainMemBufferStep?
    && var oldRoot := sk.oldRoot;
    && var newRoot := sk.newRoot;
    && oldRoot.id == RootId()
    && oldRoot.Valid(v, cache)
    && newRoot.id == RootId()
    // when we're done, newRoot.Valid(v', cache')

    && CUIsAllocatable(v, cache, newRoot.cu)
    && MergeBuffer(oldRoot.node, v.memBuffer, newRoot.node)
    && cacheOps == [ CacheIfc.Write(newRoot.cu, marshalTrunkNode(newRoot.node)) ]
    && v' == v.(
      indTbl := v.indTbl[RootId() := newRoot.cu],
      memBuffer := map[]
      )
  }

  // QUESTION: What is this supposed to do???
  predicate EquivalentNodes(a: TrunkNode, b: TrunkNode) {
    true // TODO
  }

  // Internal operation; noop
  // Rearrange mem buffers in some node
  predicate CompactBranch(v: Variables, v': Variables, cache: CacheIfc.Variables, cacheOps: CacheIfc.Ops, sk: Skolem)
  {
    && sk.CompactBranchStep?
    && var r := sk.receipt;
    && r.Valid(v, cache)
    && CUIsAllocatable(v, cache, r.newna.cu)
    && EquivalentNodes(r.Oldna().node, r.newna.node)  // Buffer replacements
      // TODO need to establish replacement B+tree is correct
    // check that we update the trunknode we're compacting in the cache
    && cacheOps == [ CacheIfc.Write(r.newna.cu, marshalTrunkNode(r.newna.node)) ]
    && v' == v.(indTbl := v.indTbl[r.newna.id := r.newna.cu])
  }

  // TODO: Sowmya check when this freeze happens and why
  predicate Freeze(v: Variables, v': Variables)
  {
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
    // Sowmya : BranchTrees are immutable, so I don't think this step is necessary?
    //|| BranchInternal(v, v', cache, cacheOps, sk) // memBuffer doesn't change
    || CompactBranch(v, v', cache, cacheOps, sk) // trunk update
  }

  predicate CommitStart(v: Variables, v': Variables, cache: CacheIfc.Variables, sb: Superblock, newBoundaryLSN: LSN)
  {
    && v.frozen.Frozen?
    && KnowFrozenIsClean(v, sb, cache)
    && sb.endSeq == v.frozen.endSeq
    && v' == v
  }

  predicate CommitComplete(v: Variables, v': Variables, cache: CacheIfc.Variables, sb: Superblock)
  {
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

  function Alloc(v: Variables, cache: CacheIfc.Variables, sb: Superblock) : set<CU>
  {
    {}  // TODO: this will make proving framing really hard.
  }
}
