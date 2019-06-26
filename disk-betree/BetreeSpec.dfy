include "BlockInterface.dfy"  
include "../lib/sequences.dfy"
include "../lib/Maps.dfy"
include "MapSpec.dfy"
include "Graph.dfy"
include "Message.dfy"

module BetreeGraph refines Graph {
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

module BetreeBlockInterface refines BlockInterface {
  import G = BetreeGraph
}

module BetreeSpec {
  import MS = MapSpec
  import opened G = BetreeGraph
  import opened Sequences
  import opened Maps

  export Spec provides BetreeStep, ValidBetreeStep, BetreeStepReads, BetreeStepOps, G
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

  datatype NodeFlush = NodeFlush(parentref: Reference, parent: Node, childref: Reference, child: Node, newchildref: Reference)

  predicate ValidFlush(flush: NodeFlush)
  {
    && WFNode(flush.parent)
    && WFNode(flush.child)
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
    var movedKeys := iset k | k in parent.children && parent.children[k] == childref;
    var newbuffer := imap k :: (if k in movedKeys then G.M.Merge(parent.buffer[k], child.buffer[k]) else child.buffer[k]);
    var newchild := Node(child.children, newbuffer);
    var newparentbuffer := imap k :: (if k in movedKeys then G.M.Update(G.M.NopDelta()) else parent.buffer[k]);
    var newparentchildren := imap k | k in parent.children :: (if k in movedKeys then newchildref else parent.children[k]);
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
    | BetreeInsert(ins: MessageInsertion)
    | BetreeFlush(flush: NodeFlush)
    | BetreeGrow(growth: RootGrowth)
    | BetreeSplit(fusion: NodeFusion)
    | BetreeMerge(fusion: NodeFusion)

  predicate ValidBetreeStep(step: BetreeStep)
  {
    match step {
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
      case BetreeInsert(ins) => InsertionOps(ins)
      case BetreeFlush(flush) => FlushOps(flush)
      case BetreeGrow(growth) => GrowOps(growth)
      case BetreeSplit(fusion) => SplitOps(fusion)
      case BetreeMerge(fusion) => MergeOps(fusion)
    }
  }
}
