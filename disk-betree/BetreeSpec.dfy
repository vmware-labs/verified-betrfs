include "BlockInterface.dfy"  
include "../lib/sequences.dfy"
include "../lib/Maps.dfy"
include "MapSpec.dfy"
include "Graph.dfy"
include "Message.dfy"

abstract module BetreeGraph refines Graph {
  import MS = MapSpec
  import M = Message

  type Value = M.Value

  type Key = MS.Key
  type BufferEntry = M.Message
  type Buffer = imap<Key, BufferEntry>
  datatype Node = Node(children: imap<Key, Reference>, buffer: Buffer)

  function Successors(node: Node) : iset<Reference>
  {
    iset k | k in node.children :: node.children[k]
  }
}

abstract module BetreeBlockInterface refines BlockInterface {
  import G = BetreeGraph
}

abstract module BetreeSpec {
  import MS = MapSpec
  import opened G = BetreeGraph
  import opened Sequences
  import opened Maps

  export Spec provides BetreeStep, ValidBetreeStep, BetreeStepReads, BetreeStepOps, BetreeStepUI, G
  export Internal reveals *

  export extends Spec // Default export-style is Spec

  predicate BufferIsDefining(entry: BufferEntry) {
    && entry.Define?
  }

  predicate BufferDefinesValue(log: BufferEntry, value: Value) {
    && BufferIsDefining(log)
    && log.value == value
  }
  
  predicate WFNode(node: Node) {
    && (forall k :: k in node.buffer)
    && (forall k :: k !in node.children ==> BufferIsDefining(node.buffer[k]))
  }

  // Now we define the state machine

  //// Query

  type Layer = G.ReadOp
  type Lookup = seq<Layer>

  datatype LookupQuery = LookupQuery(key: Key, value: Value, lookup: Lookup)

  predicate ValidLayerIndex(lookup: Lookup, idx: int) {
    && 0 <= idx < |lookup|
  }

  predicate LookupVisitsWFNodes(lookup: Lookup) {
    forall i :: 0 <= i < |lookup| ==> WFNode(lookup[i].node)
  }

  predicate LookupFollowsChildRefAtLayer(key: Key, lookup: Lookup, idx: int)
  requires ValidLayerIndex(lookup, idx) && idx < |lookup| - 1;
  requires key in lookup[idx].node.children;
  {
    lookup[idx].node.children[key] == lookup[idx+1].ref
  }

  predicate LookupFollowsChildRefs(key: Key, lookup: Lookup) {
    && (forall idx :: ValidLayerIndex(lookup, idx) && idx < |lookup| - 1 ==> key in lookup[idx].node.children)
    && (forall idx :: ValidLayerIndex(lookup, idx) && idx < |lookup| - 1 ==> LookupFollowsChildRefAtLayer(key, lookup, idx))
  }

  function InterpretLookup(lookup: Lookup, key: Key) : G.M.Message
  requires LookupVisitsWFNodes(lookup)
  {
    if |lookup| == 0 then G.M.Update(G.M.NopDelta()) else G.M.Merge(InterpretLookup(DropLast(lookup), key), Last(lookup).node.buffer[key])
  }

  predicate WFLookupForKey(lookup: Lookup, key: Key)
  {
    && |lookup| > 0
    && lookup[0].ref == Root()
    && LookupFollowsChildRefs(key, lookup)
    && LookupVisitsWFNodes(lookup)
  }

  predicate ValidQuery(q: LookupQuery) {
    && WFLookupForKey(q.lookup, q.key)
    && BufferDefinesValue(InterpretLookup(q.lookup, q.key), q.value)
  }

  function QueryReads(q: LookupQuery): seq<ReadOp> {
    q.lookup
  }

  function QueryOps(q: LookupQuery): seq<Op> {
    []
  }

  //// Insert

  function AddMessageToBuffer(buffer: Buffer, key: Key, msg: BufferEntry) : Buffer
    requires key in buffer
  {
    buffer[key := G.M.Merge(msg, buffer[key])]
  }
  
  function AddMessageToNode(node: Node, key: Key, msg: BufferEntry) : Node
    requires WFNode(node)
  {
    Node(node.children, AddMessageToBuffer(node.buffer, key, msg))
  }

  datatype MessageInsertion = MessageInsertion(key: Key, msg: BufferEntry, oldroot: Node)

  predicate ValidInsertion(ins: MessageInsertion) {
    && WFNode(ins.oldroot)
  }

  function InsertionReads(ins: MessageInsertion): seq<ReadOp>
  requires ValidInsertion(ins)
  {
    [G.ReadOp(Root(), ins.oldroot)]
  }

  function InsertionOps(ins: MessageInsertion) : seq<Op>
  requires ValidInsertion(ins)
  {
    var newroot := AddMessageToNode(ins.oldroot, ins.key, ins.msg);
    var writeop := G.WriteOp(Root(), newroot);
    [writeop]
  }

  //// Flush

  datatype NodeFlush = NodeFlush(parentref: Reference, parent: Node, childref: Reference, child: Node, newchildref: Reference, movedKeys: iset<Key>)

  predicate ValidFlush(flush: NodeFlush)
  {
    && WFNode(flush.parent)
    && WFNode(flush.child)
    && forall key :: key in flush.movedKeys ==> IMapsTo(flush.parent.children, key, flush.childref)
  }

  function FlushReads(flush: NodeFlush) : seq<ReadOp>
  requires ValidFlush(flush)
  {
    [
      G.ReadOp(flush.parentref, flush.parent),
      G.ReadOp(flush.childref, flush.child)
    ]
  }

  function FlushOps(flush: NodeFlush) : seq<Op>
  requires ValidFlush(flush)
  {
    // TODO move all this junk into the NodeFlush object
    var parentref := flush.parentref;
    var parent := flush.parent;
    var childref := flush.childref;
    var child := flush.child;
    var newchildref := flush.newchildref;
    var newbuffer := imap k :: (if k in flush.movedKeys then G.M.Merge(parent.buffer[k], child.buffer[k]) else child.buffer[k]);
    var newchild := Node(child.children, newbuffer);
    var newparentbuffer := imap k :: (if k in flush.movedKeys then G.M.Update(G.M.NopDelta()) else parent.buffer[k]);
    var newparentchildren := imap k | k in parent.children :: (if k in flush.movedKeys then newchildref else parent.children[k]);
    var newparent := Node(newparentchildren, newparentbuffer);
    var allocop := G.AllocOp(newchildref, newchild);
    var writeop := G.WriteOp(parentref, newparent);
    [allocop, writeop]
  }

  //// Grow

  datatype RootGrowth = RootGrowth(oldroot: Node, newchildref: Reference)

  predicate ValidGrow(growth: RootGrowth)
  {
    true
  }

  function GrowReads(growth: RootGrowth) : seq<ReadOp>
  requires ValidGrow(growth)
  {
    [G.ReadOp(Root(), growth.oldroot)]
  }

  function GrowOps(growth: RootGrowth) : seq<Op>
  requires ValidGrow(growth)
  {
    var newroot := Node(
        imap key | MS.InDomain(key) :: growth.newchildref,
        imap key | MS.InDomain(key) :: G.M.Update(G.M.NopDelta()));
    var allocop := G.AllocOp(growth.newchildref, growth.oldroot);
    var writeop := G.WriteOp(Root(), newroot);
    [allocop, writeop]
  }

  //// Redirect
  
  datatype Redirect = Redirect(
    parentref: Reference,
    old_parent: Node,
    old_childrefs: seq<Reference>,
    old_children: imap<Reference, Node>,
    
    new_parent: Node,
    new_childref: Reference,
    new_child: Node,
    
    keys: iset<Key>
  )

  predicate ValidRedirect(redirect: Redirect) {
    && WFNode(redirect.old_parent)
    && WFNode(redirect.new_parent)
    && WFNode(redirect.new_child)

    // Consistency of old_parent, old_childrefs, old_children, and keys
    && (forall ref :: ref in IMapRestrict(redirect.old_parent.children, redirect.keys).Values <==> ref in redirect.old_childrefs)
    && redirect.old_children.Keys == IMapRestrict(redirect.old_parent.children, redirect.keys).Values

    // Defines new_parent
    && redirect.new_parent.buffer == redirect.old_parent.buffer
    && (forall key :: key in redirect.keys ==> IMapsTo(redirect.new_parent.children, key, redirect.new_childref))
    && (forall key :: key !in redirect.keys ==> IMapsAgreeOnKey(redirect.new_parent.children, redirect.old_parent.children, key))


    // The buffer of the new child has to agree with the buffers of the old children on the keys that were routed to them.
    && (forall key :: key in redirect.keys * redirect.old_parent.children.Keys ==>
       redirect.old_parent.children[key] in redirect.old_children && IMapsAgreeOnKey(redirect.new_child.buffer, redirect.old_children[redirect.old_parent.children[key]].buffer, key))

    // The children of the new child must agree with the children of the old children on the keys that were routed to them.
    && (forall key :: key in redirect.keys * redirect.old_parent.children.Keys ==>
       redirect.old_parent.children[key] in redirect.old_children && IMapsAgreeOnKey(redirect.new_child.children, redirect.old_children[redirect.old_parent.children[key]].children, key))

    // The new child can't have any children other than the ones mentioned above.
    && redirect.new_child.children.Values == IMapRestrict(redirect.new_child.children, redirect.keys * redirect.old_parent.children.Keys).Values
  }

  function RedirectChildReads(childrefs: seq<Reference>, children: imap<Reference, Node>) : (readops: seq<ReadOp>)
    requires forall ref :: ref in childrefs ==> ref in children
    ensures |readops| == |childrefs|
    ensures forall i :: 0 <= i < |childrefs| ==> readops[i] == ReadOp(childrefs[i], children[childrefs[i]])
  {
    if childrefs == [] then []
    else RedirectChildReads(DropLast(childrefs), children) + [ ReadOp(Last(childrefs), children[Last(childrefs)]) ]
  }
    
  
  function RedirectReads(redirect: Redirect) : seq<ReadOp>
    requires ValidRedirect(redirect)
  {
    [ ReadOp(redirect.parentref, redirect.old_parent) ]
      + RedirectChildReads(redirect.old_childrefs, redirect.old_children)
  }

  function RedirectOps(redirect: Redirect) : seq<Op>
    requires ValidRedirect(redirect)
  {
    [
      G.AllocOp(redirect.new_childref, redirect.new_child),
      G.WriteOp(redirect.parentref, redirect.new_parent)
    ]
  }
  
  //// Split

  datatype NodeFusion = NodeFusion(
    parentref: Reference,
    fused_childref: Reference,
    left_childref: Reference,
    right_childref: Reference,
    fused_parent: Node,
    split_parent: Node,
    fused_child: Node,
    left_child: Node,
    right_child: Node,
    
    left_keys: iset<Key>,
    right_keys: iset<Key>
  )

  predicate ValidFusion(fusion: NodeFusion)
  {
    && fusion.left_keys !! fusion.right_keys
    && (forall key :: key in fusion.left_keys ==> IMapsTo(fusion.fused_parent.children, key, fusion.fused_childref))
    && (forall key :: key in fusion.left_keys ==> IMapsTo(fusion.split_parent.children, key, fusion.left_childref))

    && (forall key :: key in fusion.right_keys ==> IMapsTo(fusion.fused_parent.children, key, fusion.fused_childref))
    && (forall key :: key in fusion.right_keys ==> IMapsTo(fusion.split_parent.children, key, fusion.right_childref))

    && (forall key :: (key !in fusion.left_keys) && (key !in fusion.right_keys) ==>
      IMapsAgreeOnKey(fusion.split_parent.children, fusion.fused_parent.children, key))

    && fusion.fused_parent.buffer == fusion.split_parent.buffer

    && (forall key :: key in fusion.left_keys ==> IMapsAgreeOnKey(fusion.fused_child.children, fusion.left_child.children, key))
    && (forall key :: key in fusion.left_keys ==> IMapsAgreeOnKey(fusion.fused_child.buffer, fusion.left_child.buffer, key))

    && (forall key :: key in fusion.right_keys ==> IMapsAgreeOnKey(fusion.fused_child.children, fusion.right_child.children, key))
    && (forall key :: key in fusion.right_keys ==> IMapsAgreeOnKey(fusion.fused_child.buffer, fusion.right_child.buffer, key))
  }

  predicate ValidSplit(fusion: NodeFusion)
  {
    && WFNode(fusion.fused_parent)
    && WFNode(fusion.fused_child)
    && WFNode(fusion.left_child)
    && WFNode(fusion.right_child)
    && ValidFusion(fusion)
    && fusion.left_child.children.Values <= fusion.fused_child.children.Values
    && fusion.right_child.children.Values <= fusion.fused_child.children.Values
  }

  function SplitReads(fusion: NodeFusion) : seq<ReadOp>
  requires ValidSplit(fusion)
  {
    [
      ReadOp(fusion.parentref, fusion.fused_parent),
      ReadOp(fusion.fused_childref, fusion.fused_child)
    ]
  }

  function SplitOps(fusion: NodeFusion) : seq<Op>
  requires ValidSplit(fusion)
  {
    [
      G.AllocOp(fusion.left_childref, fusion.left_child),
      G.AllocOp(fusion.right_childref, fusion.right_child),
      G.WriteOp(fusion.parentref, fusion.split_parent)
    ]
  }

  //// Merge

  predicate ValidMerge(fusion: NodeFusion)
  {
    ValidFusion(fusion)
    && fusion.fused_child.children == IMapUnion(IMapRestrict(fusion.left_child.children, fusion.left_keys), IMapRestrict(fusion.right_child.children, fusion.right_keys))
  }

  function MergeReads(fusion: NodeFusion) : seq<ReadOp>
  requires ValidMerge(fusion)
  {
    [
      ReadOp(fusion.parentref, fusion.split_parent),
      ReadOp(fusion.left_childref, fusion.left_child),
      ReadOp(fusion.right_childref, fusion.right_child)
    ]
  }

  function MergeOps(fusion: NodeFusion) : seq<Op>
  requires ValidMerge(fusion)
  {
    [
      G.AllocOp(fusion.fused_childref, fusion.fused_child),
      G.WriteOp(fusion.parentref, fusion.fused_parent)
    ]
  }

  //// All together

  datatype BetreeStep =
    | BetreeQuery(q: LookupQuery)
    | BetreeInsert(ins: MessageInsertion)
    | BetreeFlush(flush: NodeFlush)
    | BetreeGrow(growth: RootGrowth)
    | BetreeSplit(fusion: NodeFusion)
    | BetreeMerge(fusion: NodeFusion)

  predicate ValidBetreeStep(step: BetreeStep)
  {
    match step {
      case BetreeQuery(q) => ValidQuery(q)
      case BetreeInsert(ins) => ValidInsertion(ins)
      case BetreeFlush(flush) => ValidFlush(flush)
      case BetreeGrow(growth) => ValidGrow(growth)
      case BetreeSplit(fusion) => ValidSplit(fusion)
      case BetreeMerge(fusion) => ValidMerge(fusion)
    }
  }

  function BetreeStepReads(step: BetreeStep) : seq<ReadOp>
  requires ValidBetreeStep(step)
  {
    match step {
      case BetreeQuery(q) => QueryReads(q)
      case BetreeInsert(ins) => InsertionReads(ins)
      case BetreeFlush(flush) => FlushReads(flush)
      case BetreeGrow(growth) => GrowReads(growth)
      case BetreeSplit(fusion) => SplitReads(fusion)
      case BetreeMerge(fusion) => MergeReads(fusion)
    }
  }

  function BetreeStepOps(step: BetreeStep) : seq<Op>
  requires ValidBetreeStep(step)
  {
    match step {
      case BetreeQuery(q) => QueryOps(q)
      case BetreeInsert(ins) => InsertionOps(ins)
      case BetreeFlush(flush) => FlushOps(flush)
      case BetreeGrow(growth) => GrowOps(growth)
      case BetreeSplit(fusion) => SplitOps(fusion)
      case BetreeMerge(fusion) => MergeOps(fusion)
    }
  }

  predicate BetreeStepUI(step: BetreeStep, uiop: MS.UI.Op<Value>) {
    match step {
      case BetreeQuery(q) => uiop == MS.UI.GetOp(q.key, q.value)
      case BetreeInsert(ins) => ins.msg.Define? && uiop == MS.UI.PutOp(ins.key, ins.msg.value)
      case BetreeFlush(flush) => uiop.NoOp?
      case BetreeGrow(growth) => uiop.NoOp?
      case BetreeSplit(fusion) => uiop.NoOp?
      case BetreeMerge(fusion) => uiop.NoOp?
    }
  }
}
