include "BlockInterface.dfy"  
include "../lib/sequences.dfy"
include "../lib/Maps.dfy"
include "MapSpec.dfy"

abstract module DiskBetree {
  import MS: MapSpec
  import BI : BlockInterface
  import opened Sequences
  import opened Maps
  
  type Key = MS.Key
    
  datatype BufferEntry<Value> = Insertion(value: Value)

  type Buffer<Value> = imap<Key, seq<BufferEntry<Value>>>
  //datatype Slot = Slot(child: BI.Reference, buffer: Buffer);
  datatype Node<Value> = Node(children: imap<Key, BI.Reference>, buffer: Buffer<Value>)

  datatype Layer<Value> = Layer(ref: BI.Reference, node: Node<Value>, accumulatedBuffer: seq<BufferEntry>)
  type Lookup<Value> = seq<Layer>

  predicate BufferIsDefining(log: seq<BufferEntry>) {
    && |log| > 0
  }

  predicate BufferDefinesValue<Value>(log: seq<BufferEntry>, value: Value) {
    && BufferIsDefining(log)
    && log[0].value == value
  }
  
  predicate WFNode(node: Node) {
    && (forall k :: k in node.buffer)
    && (forall k :: k !in node.children ==> BufferIsDefining(node.buffer[k]))
  }

  predicate LookupFollowsChildRefs(key: Key, lookup: Lookup) {
    && (forall i :: 0 <= i < |lookup| - 1 ==> key in lookup[i].node.children)
    && (forall i :: 0 <= i < |lookup| - 1 ==> lookup[i].node.children[key] == lookup[i+1].ref)
  }
  
  predicate LookupRespectsDisk<Value>(view: BI.View<Node<Value>>, lookup: Lookup) {
    forall i :: 0 <= i < |lookup| ==> IMapsTo(view, lookup[i].ref, lookup[i].node)
  }

  predicate LookupVisitsWFNodes(lookup: Lookup) {
    forall i :: 0 <= i < |lookup| ==> WFNode(lookup[i].node)
  }

  predicate LookupAccumulatesMessages(key: Key, lookup: Lookup) {
    && |lookup| > 0
    && LookupVisitsWFNodes(lookup)
    && lookup[0].accumulatedBuffer == lookup[0].node.buffer[key]
    && (forall i :: 0 < i < |lookup| ==> lookup[i].accumulatedBuffer == lookup[i-1].accumulatedBuffer + lookup[i].node.buffer[key])
  }

  predicate IsPathFromRootLookup<Value>(k: Constants, view: BI.View<Node<Value>>, key: Key, lookup: Lookup) {
    && |lookup| > 0
    && lookup[0].ref == BI.Root(k.bck)
    && LookupRespectsDisk(view, lookup)
    && LookupFollowsChildRefs(key, lookup)
  }

  predicate IsSatisfyingLookup<Value>(k: Constants, view: BI.View<Node<Value>>, key: Key, value: Value, lookup: Lookup) {
    && IsPathFromRootLookup(k, view, key, lookup)
    && LookupVisitsWFNodes(lookup)
    && LookupAccumulatesMessages(key, lookup)
    && BufferDefinesValue(Last(lookup).accumulatedBuffer, value)
  }

  function Successors(node: Node) : iset<BI.Reference>
  {
    iset k | k in node.children :: node.children[k]
  }
  
  // Now we define the state machine
  
  datatype Constants = Constants(bck: BI.Constants)
  datatype Variables<Value> = Variables(bcv: BI.Variables<Node<Value>>)

  function EmptyNode<Value>() : Node {
    var buffer := imap key | MS.InDomain(key) :: [Insertion(MS.EmptyValue())];
    Node(imap[], buffer)
  }
    
  predicate Init(k: Constants, s: Variables) {
    && BI.Init(k.bck, s.bcv)
    && IMapsTo(BI.ViewOf(k.bck, s.bcv), BI.Root(k.bck), EmptyNode())
  }
    
  predicate Query<Value>(k: Constants, s: Variables, s': Variables, key: Key, value: Value, lookup: Lookup) {
    && s == s'
    && IsSatisfyingLookup(k, BI.ViewOf(k.bck, s.bcv), key, value, lookup)
  }

  function AddMessageToBuffer(buffer: Buffer, key: Key, msg: BufferEntry) : Buffer
    requires key in buffer
  {
    buffer[key := [msg] + buffer[key]]
  }
  
  function AddMessageToNode(node: Node, key: Key, msg: BufferEntry) : Node
    requires WFNode(node)
  {
    Node(node.children, AddMessageToBuffer(node.buffer, key, msg))
  }
  
  predicate InsertMessage<Value>(k: Constants, s: Variables, s': Variables, key: Key, msg: BufferEntry, oldroot: Node) {
    && IMapsTo(BI.ViewOf(k.bck, s.bcv), BI.Root(k.bck), oldroot)
    && WFNode(oldroot)
    && var newroot := AddMessageToNode(oldroot, key, msg);
    && BI.Apply(k.bck, s.bcv, s'.bcv, BI.WriteOp(BI.Root(k.bck), newroot, Successors(newroot)))
  }

  predicate Flush<Value>(k: Constants, s: Variables, s': Variables, parentref: BI.Reference, parent: Node, childref: BI.Reference, child: Node, newchildref: BI.Reference) {
    var movedKeys := iset k | k in parent.children && parent.children[k] == childref;
    && IMapsTo(BI.ViewOf(k.bck, s.bcv), parentref, parent)
    && IMapsTo(BI.ViewOf(k.bck, s.bcv), childref, child)
    && WFNode(parent)
    && WFNode(child)
    && var newbuffer := imap k :: (if k in movedKeys then parent.buffer[k] + child.buffer[k] else child.buffer[k]);
    && var newchild := Node(child.children, newbuffer);
    && var newparentbuffer := imap k :: (if k in movedKeys then [] else parent.buffer[k]);
    && var newparentchildren := imap k | k in parent.children :: (if k in movedKeys then newchildref else parent.children[k]);
    && var newparent := Node(newparentchildren, newparentbuffer);
    && var allocop := BI.AllocOp(newchild, Successors(newchild), newchildref);
    && var writeop := BI.WriteOp(parentref, newparent, Successors(newparent));
    && BI.Apply2(k.bck, s.bcv, s'.bcv, allocop, writeop)
  }

  predicate Grow(k: Constants, s: Variables, s': Variables, oldroot: Node, newchildref: BI.Reference) {
    && IMapsTo(BI.ViewOf(k.bck, s.bcv), BI.Root(k.bck), oldroot)
    && var newchild := oldroot;
    && var newroot := Node(
        imap key | MS.InDomain(key) :: newchildref,
        imap key | MS.InDomain(key) :: []);
    && var allocop := BI.AllocOp(newchild, Successors(newchild), newchildref);
    && var writeop := BI.WriteOp(BI.Root(k.bck), newroot, Successors(newroot));
    && BI.Apply2(k.bck, s.bcv, s'.bcv, allocop, writeop)
  }

  datatype Step<Value(!new)> =
    | QueryStep(key: Key, value: Value, lookup: Lookup)
    | InsertMessageStep(key: Key, msg: BufferEntry, oldroot: Node)
    | FlushStep(parentref: BI.Reference, parent: Node, childref: BI.Reference, child: Node, newchildref: BI.Reference)
    | GrowStep(oldroot: Node, newchildref: BI.Reference)

  predicate NextStep(k: Constants, s: Variables, s': Variables, step: Step) {
    match step {
      case QueryStep(key, value, lookup) => Query(k, s, s', key, value, lookup)
      case InsertMessageStep(key, msg, oldroot) => InsertMessage(k, s, s', key, msg, oldroot)
      case FlushStep(parentref, parent, childref, child, newchildref) => Flush(k, s, s', parentref, parent, childref, child, newchildref)
      case GrowStep(oldroot, newchildref) => Grow(k, s, s', oldroot, newchildref)
    }
  }

  predicate Next<Value(!new)>(k: Constants, s: Variables, s': Variables) {
    exists step: Step :: NextStep(k, s, s', step)
  }
}
