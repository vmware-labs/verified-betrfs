include "../Betree/BlockInterface.i.dfy"  
include "../lib/Base/sequences.i.dfy"
include "../lib/Base/Maps.s.dfy"
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
//   (when do we use that?)
//

module BetreeGraph refines Graph {
  import M = ValueMessage
  import opened KeyType
  import opened ValueType

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
    requires 0 <= idx < |lookup| - 1;
  {
    IMapsTo(lookup[idx].node.children, key, lookup[idx+1].ref)
  }

  predicate LookupFollowsChildRefs(key: Key, lookup: Lookup) {
    //&& (forall idx :: ValidLayerIndex(lookup, idx) && idx < |lookup| - 1 ==> key in lookup[idx].node.children)
    && (forall idx :: 0 <= idx < |lookup| - 1 ==> LookupFollowsChildRefAtLayer(key, lookup, idx))
  }

  predicate WFLookupForKey(lookup: Lookup, key: Key)
  {
    && |lookup| > 0
    && lookup[0].ref == Root()
    && LookupFollowsChildRefs(key, lookup)
    && LookupVisitsWFNodes(lookup)
  }

  function InterpretLookup(lookup: Lookup, key: Key) : G.M.Message
  requires LookupVisitsWFNodes(lookup)
  {
    if |lookup| == 0
    then
        G.M.Update(G.M.NopDelta())
    else
        G.M.Merge(InterpretLookup(DropLast(lookup), key), Last(lookup).node.buffer[key])
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

  //// Successor

  datatype SuccQuery = SuccQuery(
      start: UI.RangeStart,
      results: seq<UI.SuccResult>,
      end: UI.RangeEnd,
      lookup: Lookup)

  predicate LookupKeyValue(l: Lookup, key: Key, value: Value)
  {
    && WFLookupForKey(l,key)
    && BufferDefinesValue(InterpretLookup(l, key), value)
  }

  predicate ValidSuccQuery(q: SuccQuery)
  {
    && MS.NonEmptyRange(q.start, q.end)
    && (forall i | 0 <= i < |q.results| :: LookupKeyValue(q.lookup, q.results[i].key, q.results[i].value))
    && (forall i | 0 <= i < |q.results| :: q.results[i].value != MS.EmptyValue())
    && (forall i | 0 <= i < |q.results| :: MS.InRange(q.start, q.results[i].key, q.end))
    && (forall i, j | 0 <= i < j < |q.results| :: Keyspace.lt(q.results[i].key, q.results[j].key))
    && (forall key | MS.InRange(q.start, key, q.end) ::
        (forall i | 0 <= i < |q.results| :: q.results[i].key != key) ==>
        LookupKeyValue(q.lookup, key, MS.EmptyValue())
      )
  }

  function SuccQueryReads(q: SuccQuery) : seq<ReadOp>
  {
    q.lookup
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

  datatype NodeFlush = NodeFlush(parentref: Reference, parent: Node, childref: Reference, child: Node, newchildref: Reference, movedKeys: iset<Key>, flushedKeys: iset<Key>)

  predicate ValidFlush(flush: NodeFlush)
  {
    && WFNode(flush.parent)
    && WFNode(flush.child)
    // TODO(jonh): replace this with "<="
    && (forall key | key in flush.flushedKeys :: key in flush.movedKeys)
    && (forall key | key in flush.movedKeys :: IMapsTo(flush.parent.children, key, flush.childref))
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
    var newbuffer := imap k :: (if k in flush.flushedKeys then G.M.Merge(parent.buffer[k], child.buffer[k]) else child.buffer[k]);
    var newchild := Node(child.children, newbuffer);
    var newparentbuffer := imap k :: (if k in flush.flushedKeys then G.M.Update(G.M.NopDelta()) else parent.buffer[k]);
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
    new_childrefs: seq<Reference>,
    new_children: imap<Reference, Node>,
    
    keys: iset<Key>
  )

  predicate ValidRedirect(redirect: Redirect) {
    && WFNode(redirect.old_parent)
    && (forall node :: node in redirect.old_children.Values ==> WFNode(node))
    && WFNode(redirect.new_parent)
    && (forall node :: node in redirect.new_children.Values ==> WFNode(node))

    // Consistency of old_parent, old_childrefs, old_children, and keys
    && (forall ref :: ref in IMapRestrict(redirect.old_parent.children, redirect.keys).Values <==> ref in redirect.old_childrefs)
    && redirect.old_children.Keys == IMapRestrict(redirect.old_parent.children, redirect.keys).Values

    // Consistency of new_parent, new_childrefs, new_children, and keys
    && (forall ref :: ref in IMapRestrict(redirect.new_parent.children, redirect.keys).Values ==> ref in redirect.new_childrefs)
    && redirect.new_children.Keys == (iset ref | ref in redirect.new_childrefs)

    // Defines new_parent
    && redirect.new_parent.buffer == redirect.old_parent.buffer
    && (forall key :: key in redirect.keys ==> key in redirect.new_parent.children)
    && (forall key :: key in redirect.keys ==> redirect.new_parent.children[key] in redirect.new_childrefs)
    && (forall key :: key !in redirect.keys ==> IMapsAgreeOnKey(redirect.new_parent.children, redirect.old_parent.children, key))


    // The buffer of the new child has to agree with the buffers of the old children on the keys that were routed to them.
    && (forall key :: key in redirect.keys * redirect.old_parent.children.Keys ==>
       && redirect.old_parent.children[key] in redirect.old_children
       && redirect.new_parent.children[key] in redirect.new_children
       && IMapsAgreeOnKey(
          redirect.new_children[redirect.new_parent.children[key]].buffer,
          redirect.old_children[redirect.old_parent.children[key]].buffer,
          key))

    // The children of the new child must agree with the children of the old children on the keys that were routed to them.
    && (forall key :: key in redirect.keys * redirect.old_parent.children.Keys ==>
       && redirect.old_parent.children[key] in redirect.old_children
       && redirect.new_parent.children[key] in redirect.new_children
       && IMapsAgreeOnKey(
          redirect.new_children[redirect.new_parent.children[key]].children,
          redirect.old_children[redirect.old_parent.children[key]].children,
          key))

    // The new child can't have any children other than the ones mentioned above.
    //&& (forall new_child | new_child in redirect.new_children.Values ::
    //  new_child.children.Values == IMapRestrict(new_child.children, redirect.keys * redirect.old_parent.children.Keys).Values)
    && (forall childref, ref | childref in redirect.new_children && ref in redirect.new_children[childref].children.Values ::
        exists key ::
          && IMapsTo(redirect.new_parent.children, key, childref)
          && IMapsTo(redirect.new_children[childref].children, key, ref)
          && key in redirect.keys
          && key in redirect.old_parent.children
       )
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
 
  function RedirectChildAllocs(childrefs: seq<Reference>, children: imap<Reference, Node>) : (ops: seq<Op>)
    requires forall ref :: ref in childrefs ==> ref in children
    ensures |ops| == |childrefs|
    ensures forall i :: 0 <= i < |childrefs| ==> ops[i] == AllocOp(childrefs[i], children[childrefs[i]])
  {
    if childrefs == [] then []
    else RedirectChildAllocs(DropLast(childrefs), children) + [ AllocOp(Last(childrefs), children[Last(childrefs)]) ]
  }

  function RedirectOps(redirect: Redirect) : seq<Op>
    requires ValidRedirect(redirect)
  {
    RedirectChildAllocs(redirect.new_childrefs, redirect.new_children)
    + [ G.WriteOp(redirect.parentref, redirect.new_parent) ]
  }
  
  //// All together

  datatype BetreeStep =
    | BetreeQuery(q: LookupQuery)
    | BetreeSuccQuery(sq: SuccQuery)
    | BetreeInsert(ins: MessageInsertion)
    | BetreeFlush(flush: NodeFlush)
    | BetreeGrow(growth: RootGrowth)
    | BetreeRedirect(redirect: Redirect)

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
    }
  }
}
