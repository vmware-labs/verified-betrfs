include "BlockCache.dfy"  
include "../lib/sequences.dfy"
include "MapSpec.dfy"

abstract module DiskBetree {
  import MS: MapSpec
  import BC : BlockCache
  import opened Sequences
  
  type Key = MS.Key
    
  datatype BufferEntry<Value> = Insertion(value: Value)

  type Buffer<Value> = imap<Key, seq<BufferEntry<Value>>>
  //datatype Slot = Slot(child: BC.Reference, buffer: Buffer);
  datatype Node<Value> = Node(children: imap<Key, BC.Reference>, buffer: Buffer<Value>)

  datatype Layer<Value> = Layer(ref: BC.Reference, node: Node<Value>, accumulatedBuffer: seq<BufferEntry>)
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

  predicate IsSatisfyingLookup<Value>(k: Constants, s: Variables, key: Key, value: Value, lookup: Lookup) {
    && |lookup| > 0
    && lookup[0].ref == BC.Root(k.bcc)
    && (forall i :: 0 <= i < |lookup| - 1 ==> key in lookup[i].node.children && lookup[i].node.children[key] == lookup[i+1].ref)
    && (forall i :: 0 <= i < |lookup| ==> BC.Read(k.bcc, s.bcv, lookup[i].ref) == lookup[i].node)
    && (forall i :: 0 <= i < |lookup| ==> WFNode(lookup[i].node))
    && lookup[0].accumulatedBuffer == lookup[0].node.buffer[key]
    && (forall i :: 0 < i < |lookup| ==> lookup[i].accumulatedBuffer == lookup[i-1].accumulatedBuffer + lookup[i].node.buffer[key])
    && BufferDefinesValue(Last(lookup).accumulatedBuffer, value)
  }

  function Successors(node: Node) : iset<BC.Reference>
  {
    iset k | k in node.children :: node.children[k]
  }
  
  // Now we define the state machine
  
  datatype Constants = Constants(bcc: BC.Constants)
  datatype Variables<Value> = Variables(bcv: BC.Variables<Node<Value>>)

  function EmptyNode<Value>() : Node {
    var buffer := imap key | MS.InDomain(key) :: [Insertion(MS.EmptyValue())];
    Node(imap[], buffer)
  }
    
  predicate Init(k: Constants, s: Variables) {
    && BC.Init(k.bcc, s.bcv)
    && BC.Read(k.bcc, s.bcv, BC.Root(k.bcc)) == EmptyNode()
  }
    
  predicate Query<Value>(k: Constants, s: Variables, s': Variables, key: Key, value: Value, lookup: Lookup) {
    && s == s'
    && IsSatisfyingLookup(k, s, key, value, lookup)
  }

  predicate InsertMessage<Value>(k: Constants, s: Variables, s': Variables, key: Key, value: Value, oldroot: Node) {
    && BC.Read(k.bcc, s.bcv, BC.Root(k.bcc)) == oldroot
    && WFNode(oldroot)
    && var newroot := Node(oldroot.children, oldroot.buffer[key := [Insertion(value)] + oldroot.buffer[key]]);
    && WFNode(oldroot)
    && BC.Apply(k.bcc, s.bcv, s'.bcv, BC.WriteOp(BC.Root(k.bcc), newroot, Successors(newroot)))
  }

  predicate Flush<Value>(k: Constants, s: Variables, s': Variables, parentref: BC.Reference, parent: Node, childref: BC.Reference, child: Node, newchildref: BC.Reference) {
    var movedKeys := iset k | k in parent.children && parent.children[k] == childref;
    && BC.Read(k.bcc, s.bcv, parentref) == parent
    && BC.Read(k.bcc, s.bcv, childref) == child
    && WFNode(parent)
    && WFNode(child)
    && var newbuffer := imap k :: (if k in movedKeys then parent.buffer[k] + child.buffer[k] else child.buffer[k]);
    && var newchild := Node(child.children, newbuffer);
    && var newparentbuffer := imap k :: (if k in movedKeys then [] else parent.buffer[k]);
    && var newparent := Node(parent.children, newparentbuffer);
    && var allocop := BC.AllocOp(newchild, Successors(newchild), newchildref);
    && var writeop := BC.WriteOp(parentref, newparent, Successors(newparent));
    && BC.Apply2(k.bcc, s.bcv, s'.bcv, allocop, writeop)
  }

  predicate Grow(k: Constants, s: Variables, s': Variables, oldroot: Node, newchildref: BC.Reference) {
    && BC.Read(k.bcc, s.bcv, BC.Root(k.bcc)) == oldroot
    && var newchild := oldroot;
    && var newroot := Node(imap key | MS.InDomain(key) :: newchildref, imap[]);
    && var allocop := BC.AllocOp(newchild, Successors(newchild), newchildref);
    && var writeop := BC.WriteOp(BC.Root(k.bcc), newroot, Successors(newroot));
    && BC.Apply2(k.bcc, s.bcv, s'.bcv, allocop, writeop)
  }

  datatype Step<Value(!new)> =
    | QueryStep(key: Key, value: Value, lookup: Lookup)
    | InsertMessageStep(key: Key, value: Value, oldroot: Node)
    | FlushStep(parentref: BC.Reference, parent: Node, childref: BC.Reference, child: Node, newchildref: BC.Reference)
    | GrowStep(oldroot: Node, newchildref: BC.Reference)

  predicate NextStep(k: Constants, s: Variables, s': Variables, step: Step) {
    match step {
      case QueryStep(key, value, lookup) => Query(k, s, s', key, value, lookup)
      case InsertMessageStep(key, value, oldroot) => InsertMessage(k, s, s', key, value, oldroot)
      case FlushStep(parentref, parent, childref, child, newchildref) => Flush(k, s, s', parentref, parent, childref, child, newchildref)
      case GrowStep(oldroot, newchildref) => Grow(k, s, s', oldroot, newchildref)
    }
  }

  predicate Next<Value(!new)>(k: Constants, s: Variables, s': Variables) {
    exists step: Step :: NextStep(k, s, s', step)
  }
}
