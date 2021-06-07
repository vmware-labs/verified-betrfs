// Copyright 2018-2021 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, and University of Washington
// SPDX-License-Identifier: BSD-2-Clause

include "../Betree/BlockInterface.i.dfy"  
include "../lib/Base/Sequences.i.dfy"
include "../lib/Base/Maps.i.dfy"
include "../MapSpec/MapSpec.s.dfy"
include "../Betree/Graph.i.dfy"
include "../lib/Base/Message.i.dfy"
include "../lib/Base/total_order.i.dfy"
//
// Defines the basic B-e-tree-shaped operations.
//
// * A Query is satisfied by examining enough of the tree to observe a
//   terminating message list.
// * Insert shoves a single message into the root.
// * Flush moves a bundle of messages from a node to one of its children.
// * Grow inserts a new layer at the top of the tree to admit growth.
// * Redirect replaces a subtree with a semantically-equivalent one.
//    'Merge' and 'Split' are both special cases.
//

module BetreeGraph refines Graph {
  import M = ValueMessage
  import opened KeyType
  import opened ValueType

  type BufferEntry = M.Message
  type Buffer = imap<Key, BufferEntry>
  datatype Edge = Edge(edgeKey: Key, ref: Reference)
  datatype Node = Node(children: imap<Key, Edge>, buffer: Buffer)

  function Successors(node: Node) : iset<Reference>
  {
    iset k | k in node.children :: node.children[k].ref
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
  import opened KeyType
  import opened ValueType
  import UI
  import Keyspace = Lexicographic_Byte_Order

  export Spec provides BetreeStep, ValidBetreeStep, BetreeStepReads, BetreeStepOps, BetreeStepUI, G, UI
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
    && (forall k:Key :: k in node.buffer)
    && (forall k:Key :: k !in node.children ==> BufferIsDefining(node.buffer[k]))
  }

  // Now we define the state machine

  //// Edge
  predicate ChildMapsToRef(m: imap<Key, Edge>, k: Key, result: Reference) {
    && k in m
    && m[k].ref == result
  }

  predicate ChildMapsToEdge(m: imap<Key, Edge>, k: Key, result: Key) {
    && k in m
    && m[k].edgeKey == result
  }
 
  //// Query

  datatype Layer = Layer(readOp: G.ReadOp, currentKey: Key)
  type Lookup = seq<Layer>

  //// Query

  datatype LookupQuery = LookupQuery(key: Key, value: Value, lookup: Lookup)

  predicate ValidLayerIndex(lookup: Lookup, idx: int) {
    && 0 <= idx < |lookup|
  }

  predicate LookupVisitsWFNodes(lookup: Lookup) {
    forall i :: 0 <= i < |lookup| ==> WFNode(lookup[i].readOp.node)
  }

  predicate LookupFollowsChildRefAtLayer(lookup: Lookup, idx: int)
    requires 0 <= idx < |lookup| - 1;
  {
    ChildMapsToRef(lookup[idx].readOp.node.children, lookup[idx].currentKey, lookup[idx+1].readOp.ref)
  }

  predicate LookupFollowsChildRefs(lookup: Lookup) {
    (forall idx :: 0 <= idx < |lookup| - 1 ==> LookupFollowsChildRefAtLayer(lookup, idx))
  }

  predicate LookupFollowsEdgeAtLayer(lookup: Lookup, idx: int)
    requires 0 <= idx < |lookup| - 1;
  {
    ChildMapsToEdge(lookup[idx].readOp.node.children, lookup[idx].currentKey, lookup[idx+1].currentKey)
  }

  predicate LookupFollowsEdges(lookup: Lookup) {
    (forall idx :: 0 <= idx < |lookup| - 1 ==> LookupFollowsEdgeAtLayer(lookup, idx))
  }

  predicate WFLookupForKey(lookup: Lookup, key: Key)
  {
    && |lookup| > 0
    && lookup[0].readOp.ref == Root()
    && lookup[0].currentKey == key
    && LookupFollowsChildRefs(lookup)
    && LookupFollowsEdges(lookup)
    && LookupVisitsWFNodes(lookup)
  }

  function InterpretLookup(lookup: Lookup) : G.M.Message
  requires LookupVisitsWFNodes(lookup)
  {
    if |lookup| == 0
    then
        G.M.Update(G.M.NopDelta())
    else
        G.M.Merge(InterpretLookup(DropLast(lookup)), Last(lookup).readOp.node.buffer[Last(lookup).currentKey])
  }

  predicate ValidQuery(q: LookupQuery) {
    && WFLookupForKey(q.lookup, q.key)
    && BufferDefinesValue(InterpretLookup(q.lookup), q.value)
  }

  function LayersToReadOps(lookup: seq<Layer>): (result: seq<ReadOp>)
    ensures |lookup| == |result|
    ensures forall idx :: 0 <= idx < |lookup| ==> lookup[idx].readOp == result[idx]
  {
    if |lookup| == 0
    then
        []
    else
        LayersToReadOps(DropLast(lookup)) + [Last(lookup).readOp]
  }

  function QueryReads(q: LookupQuery): seq<ReadOp> {
    LayersToReadOps(q.lookup)
  }

  function QueryOps(q: LookupQuery): seq<Op> {
    []
  }

  //// Successor

  datatype SuccQuery = SuccQuery(
      start: UI.RangeStart,
      results: seq<UI.SuccResult>,
      end: UI.RangeEnd,
      lookup: Lookup)

  predicate LookupKeyValue(l: Lookup, key: Key, value: Value)
  {
    && WFLookupForKey(l, key)
    && BufferDefinesValue(InterpretLookup(l), value)
  }

  predicate SamePathWithKeyValue(l: Lookup, l': Lookup, key: Key, value: Value)
  {
    && |l| == |l'|
    && (forall i | 0 <= i < |l'| :: l[i].readOp == l'[i].readOp)
    && LookupKeyValue(l', key, value)
  }

  predicate ValidSuccQuery(q: SuccQuery)
  {
    && MS.NonEmptyRange(q.start, q.end)
    && (forall r | r in q.results :: (exists lookup :: SamePathWithKeyValue(q.lookup, lookup, r.key, r.value)))
    && (forall i | 0 <= i < |q.results| :: MS.InRange(q.start, q.results[i].key, q.end))
    && (forall i | 0 <= i < |q.results| :: q.results[i].value != MS.EmptyValue())
    && (forall i, j | 0 <= i < j < |q.results| :: Keyspace.lt(q.results[i].key, q.results[j].key))
    && (forall key | MS.InRange(q.start, key, q.end) ::
        (forall i | 0 <= i < |q.results| :: q.results[i].key != key) ==>
          (exists lookup :: SamePathWithKeyValue(q.lookup, lookup, key, MS.EmptyValue())))
  }

  function SuccQueryReads(q: SuccQuery) : seq<ReadOp>
  {
    LayersToReadOps(q.lookup)
  }

  function SuccQueryOps(q: SuccQuery) : seq<Op>
  {
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

  function InsertionOps(ins: MessageInsertion) : seq<Op>    // jonh: rename Op to UpdateOp?
  requires ValidInsertion(ins)
  {
    var newroot := AddMessageToNode(ins.oldroot, ins.key, ins.msg);
    var writeop := G.WriteOp(Root(), newroot);
    [writeop]
  }

  //// Flush

  datatype NodeFlush = NodeFlush(
      parentref: Reference,
      parent: Node,
      newparent: Node,
      childref: Reference,
      child: Node,
      newchildref: Reference,
      newchild: Node,
      movedkeys: iset<Key>,
      flushedkeys: iset<Key>)

  predicate ValidFlush(flush: NodeFlush)
  {
    && WFNode(flush.parent)
    && WFNode(flush.child)
    && WFNode(flush.newparent)
    && WFNode(flush.newchild)
    // TODO(jonh): replace this with "<="
    // flushed keys are within moved keys and exist in parent's children
    && (forall key | key in flush.flushedkeys :: key in flush.movedkeys)
    && (forall key | key in flush.movedkeys :: key in flush.parent.children && ChildMapsToRef(flush.parent.children, key, flush.childref))
    && ValidFlushNewParent(flush)
    && ValidFlushNewChild(flush)
  }

  predicate ValidFlushNewParent(flush: NodeFlush)
  requires WFNode(flush.parent)
  requires (forall key | key in flush.flushedkeys :: key in flush.parent.children)
  {
    && (flush.newparent.buffer == (imap k: Key :: if k in flush.flushedkeys then G.M.Update(G.M.NopDelta()) else flush.parent.buffer[k]))
    && (forall key | key in flush.movedkeys :: IMapsTo(flush.newparent.children, key, Edge(key, flush.newchildref)))
    && (forall key | key !in flush.movedkeys :: IMapsAgreeOnKey(flush.newparent.children, flush.parent.children, key))
  }

  predicate ValidFlushNewChild(flush: NodeFlush)
  requires WFNode(flush.parent)
  requires WFNode(flush.child)
  requires (forall key | key in flush.movedkeys :: key in flush.parent.children)
  {
    && var tmpbuffer := imap k | k in flush.movedkeys :: flush.child.buffer[flush.parent.children[k].edgeKey];
    && var newbuffer := imap k | k in flush.movedkeys :: if k in flush.flushedkeys then G.M.Merge(flush.parent.buffer[k], tmpbuffer[k]) else tmpbuffer[k];
    && (forall key | key in flush.movedkeys :: IMapsAgreeOnKey(flush.newchild.buffer, newbuffer, key))
    && flush.newchild.children == (imap k | k in flush.movedkeys && flush.parent.children[k].edgeKey in flush.child.children :: flush.child.children[flush.parent.children[k].edgeKey])
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
    var allocop := G.AllocOp(flush.newchildref, flush.newchild);
    var writeop := G.WriteOp(flush.parentref, flush.newparent);
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
        imap key | MS.InDomain(key) :: Edge(key, growth.newchildref),
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
    new_childrefs: seq<Reference>,
    new_children: imap<Reference, Node>,
    
    keys: iset<Key>
  )

  predicate WFRedirect(redirect: Redirect) {
    var old_parent_children_ref := imap k | k in redirect.old_parent.children :: redirect.old_parent.children[k].ref;
    var new_parent_children_ref := imap k | k in redirect.new_parent.children :: redirect.new_parent.children[k].ref;
  
    && WFNode(redirect.old_parent)
    && (forall key | key in redirect.old_children :: WFNode(redirect.old_children[key]))
    && WFNode(redirect.new_parent)
    && (forall key | key in redirect.new_children :: WFNode(redirect.new_children[key]))
    && (forall key | key in redirect.keys :: key in redirect.old_parent.children && key in redirect.new_parent.children)

    // Consistency of old_parent, old_childrefs, old_children, and keys 
    && (forall ref :: ref in IMapRestrict(old_parent_children_ref, redirect.keys).Values <==> ref in redirect.old_childrefs)
    && redirect.old_children.Keys == IMapRestrict(old_parent_children_ref, redirect.keys).Values

    // Consistency of new_parent, new_childrefs, new_children, and keys
    && (forall ref :: ref in IMapRestrict(new_parent_children_ref, redirect.keys).Values ==> ref in redirect.new_childrefs)
    && redirect.new_children.Keys == (iset ref | ref in redirect.new_childrefs)
  }

  predicate ValidRedirectNewParent(redirect: Redirect) 
    requires WFRedirect(redirect)
  {
    // Defines new_parent
    && redirect.new_parent.buffer == redirect.old_parent.buffer
    && (forall key :: key in redirect.keys ==> redirect.new_parent.children[key].ref in redirect.new_childrefs)
    && (forall key :: key in redirect.keys ==> redirect.new_parent.children[key].edgeKey == key)
    && (forall key :: key !in redirect.keys ==> IMapsAgreeOnKey(redirect.new_parent.children, redirect.old_parent.children, key))
  }

  predicate ValidRedirectNewChildren(redirect: Redirect) 
    requires WFRedirect(redirect) 
    requires ValidRedirectNewParent(redirect)
  {
    // The buffer of the new child has to agree with the buffers of the old children on the keys that were routed to them
    // things to agree on, edge translation from parent will be pushed to child, buffer content will reflect that update
    // The children of the new child must agree with the children of the old children on the keys that were routed to them.
    (forall key :: key in redirect.keys ==>
      && redirect.old_parent.children[key].ref in redirect.old_children
      && var newchild := redirect.new_children[redirect.new_parent.children[key].ref];
      && var oldchild := redirect.old_children[redirect.old_parent.children[key].ref];
      && var edgekey := redirect.old_parent.children[key].edgeKey; // translated key
      && newchild.buffer[key] == oldchild.buffer[edgekey] // indexing using parent's key
      && ((key in newchild.children) <==> (edgekey in oldchild.children))
      && ((key in newchild.children) ==> newchild.children[key] == oldchild.children[edgekey]))
  }

  predicate ValidRedirectNewGrandchildrenCheckKey(redirect: Redirect, key: Key, childref: Reference, edgeref: Reference) 
    requires childref in redirect.new_children
  {
    && ChildMapsToRef(redirect.new_parent.children, key, childref)
    && ChildMapsToRef(redirect.new_children[childref].children, key, edgeref)
    && key in redirect.keys
    && key in redirect.old_parent.children
  }

  predicate {:opaque} ValidRedirectNewGrandchildren(redirect: Redirect)
    requires WFRedirect(redirect)
    requires ValidRedirectNewParent(redirect)
    requires ValidRedirectNewChildren(redirect)
  {
    // The new child can't have any children other than the ones mentioned above.
    //&& (forall new_child | new_child in redirect.new_children.Values ::
    //  new_child.children.Values == IMapRestrict(new_child.children, redirect.keys * redirect.old_parent.children.Keys).Values)
    (forall childref, edge | childref in redirect.new_children && edge in redirect.new_children[childref].children.Values ::
      exists key :: ValidRedirectNewGrandchildrenCheckKey(redirect, key, childref, edge.ref))
  }

  predicate {:opaque} ValidRedirect(redirect: Redirect) {
    && WFRedirect(redirect)
    && ValidRedirectNewParent(redirect)
    && ValidRedirectNewChildren(redirect)
    && ValidRedirectNewGrandchildren(redirect)
  }

  function RedirectChildReads(childrefs: seq<Reference>, children: imap<Reference, Node>) : (readops: seq<ReadOp>)
    requires forall ref :: ref in childrefs ==> ref in children
    ensures |readops| == |childrefs|
    ensures forall i :: 0 <= i < |childrefs| ==> readops[i] == ReadOp(childrefs[i], children[childrefs[i]])
  {
    if childrefs == [] then []
    else RedirectChildReads(DropLast(childrefs), children) + [ ReadOp(Last(childrefs), children[Last(childrefs)]) ]
  }
  
  function {:opaque} RedirectReads(redirect: Redirect) : (res: seq<ReadOp>)
    requires ValidRedirect(redirect)
    ensures |res| == |redirect.old_childrefs| + 1
  {
    assert (forall ref :: ref in redirect.old_childrefs ==> ref in redirect.old_children) by 
    { reveal_ValidRedirect(); }
 
    [ ReadOp(redirect.parentref, redirect.old_parent) ]
      + RedirectChildReads(redirect.old_childrefs, redirect.old_children)
  }

  function RedirectChildAllocs(childrefs: seq<Reference>, children: imap<Reference, Node>) : (ops: seq<Op>)
    requires forall ref :: ref in childrefs ==> ref in children
    ensures |ops| == |childrefs|
    ensures forall i :: 0 <= i < |childrefs| ==> ops[i] == AllocOp(childrefs[i], children[childrefs[i]])
  {
    if childrefs == [] then []
    else RedirectChildAllocs(DropLast(childrefs), children) + [ AllocOp(Last(childrefs), children[Last(childrefs)]) ]
  }

  function {:opaque} RedirectOps(redirect: Redirect) : seq<Op>
    requires ValidRedirect(redirect)
  {
    assert (forall ref :: ref in redirect.new_childrefs ==> ref in redirect.new_children) by 
    { reveal_ValidRedirect(); }

    RedirectChildAllocs(redirect.new_childrefs, redirect.new_children)
    + [ G.WriteOp(redirect.parentref, redirect.new_parent) ]
  }

  /// Clone

  datatype Clone = Clone(
    oldroot: Node,
    newroot: Node,
    new_to_old:imap<Key, Key> 
  )
  
  predicate ValidClone(clone: Clone)
  {
    && WFNode(clone.oldroot)
    && WFNode(clone.newroot)

    // new = new keys that will have contents of the old keys
    // require 1. old buffer entries are flushed 2. old values are oldroot's children
    && (forall k | k in clone.new_to_old :: IMapsTo(clone.oldroot.buffer, clone.new_to_old[k], G.M.Update(G.M.NopDelta())))
    && (forall k | k in clone.new_to_old :: clone.new_to_old[k] in clone.oldroot.children)

    // newroot's buffer and children requirments 
    && (forall k | k in clone.new_to_old :: IMapsTo(clone.newroot.buffer, k, G.M.Update(G.M.NopDelta())))
    && (forall k | k !in clone.new_to_old :: IMapsAgreeOnKey(clone.newroot.buffer, clone.oldroot.buffer, k))
    && (forall k | k in clone.new_to_old :: IMapsTo(clone.newroot.children, k, clone.oldroot.children[clone.new_to_old[k]]))
    && (forall k | k !in clone.new_to_old :: IMapsAgreeOnKey(clone.newroot.children, clone.oldroot.children, k))
  }

  function CloneReads(clone: Clone) : seq<ReadOp>
  requires ValidClone(clone)
  {
    [G.ReadOp(Root(), clone.oldroot)]
  }

  function CloneOps(clone: Clone) : seq<Op>
  requires ValidClone(clone)
  {
    [G.WriteOp(Root(), clone.newroot)]
  }

  //// All together

  datatype BetreeStep =
    | BetreeQuery(q: LookupQuery)
    | BetreeSuccQuery(sq: SuccQuery)
    | BetreeInsert(ins: MessageInsertion)
    | BetreeFlush(flush: NodeFlush)
    | BetreeGrow(growth: RootGrowth)
    | BetreeRedirect(redirect: Redirect)
    | BetreeClone(clone: Clone)

  // jonh: can this be called 'Next' at this layer?
  predicate ValidBetreeStep(step: BetreeStep)
  {
    match step {
      case BetreeQuery(q) => ValidQuery(q)
      case BetreeSuccQuery(sq) => ValidSuccQuery(sq)
      case BetreeInsert(ins) => ValidInsertion(ins)
      case BetreeFlush(flush) => ValidFlush(flush)
      case BetreeGrow(growth) => ValidGrow(growth)
      case BetreeRedirect(redirect) => ValidRedirect(redirect)
      case BetreeClone(clone) => ValidClone(clone)
    }
  }

  function BetreeStepReads(step: BetreeStep) : seq<ReadOp>
  requires ValidBetreeStep(step)
  {
    match step {
      case BetreeQuery(q) => QueryReads(q)
      case BetreeSuccQuery(sq) => SuccQueryReads(sq)
      case BetreeInsert(ins) => InsertionReads(ins)
      case BetreeFlush(flush) => FlushReads(flush)
      case BetreeGrow(growth) => GrowReads(growth)
      case BetreeRedirect(redirect) => RedirectReads(redirect)
      case BetreeClone(clone) => CloneReads(clone)
    }
  }

  function BetreeStepOps(step: BetreeStep) : seq<Op>
  requires ValidBetreeStep(step)
  {
    match step {
      case BetreeQuery(q) => QueryOps(q)
      case BetreeSuccQuery(sq) => SuccQueryOps(sq)
      case BetreeInsert(ins) => InsertionOps(ins)
      case BetreeFlush(flush) => FlushOps(flush)
      case BetreeGrow(growth) => GrowOps(growth)
      case BetreeRedirect(redirect) => RedirectOps(redirect)
      case BetreeClone(clone) => CloneOps(clone)
    }
  }

  predicate BetreeStepUI(step: BetreeStep, uiop: UI.Op) {
    match step {
      case BetreeQuery(q) => uiop == UI.GetOp(q.key, q.value)
      case BetreeSuccQuery(sq) => uiop == UI.SuccOp(sq.start, sq.results, sq.end)
      case BetreeInsert(ins) => ins.msg.Define? && uiop == UI.PutOp(ins.key, ins.msg.value)
      case BetreeFlush(flush) => uiop.NoOp?
      case BetreeGrow(growth) => uiop.NoOp?
      case BetreeRedirect(redirect) => uiop.NoOp?
      case BetreeClone(clone) => uiop.CloneOp? && clone.new_to_old == MS.CloneMap(uiop.from, uiop.to)
    }
  }
}
