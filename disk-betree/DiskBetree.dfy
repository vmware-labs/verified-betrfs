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

  function Root(k: Constants) : BI.Reference {
    BI.Root(k.bck)
  }

  datatype Layer<Value> = Layer(ref: BI.Reference, node: Node<Value>)
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

  predicate {:opaque} LookupFollowsChildRefs(key: Key, lookup: Lookup) {
    && (forall i :: 0 <= i < |lookup| - 1 ==> IMapsTo(lookup[i].node.children, key, lookup[i+1].ref))
  }
  
  lemma LookupFollowsChildRefsAtLayer(key: Key, lookup: Lookup, i: int)
    requires LookupFollowsChildRefs(key, lookup)
    requires 0 <= i < |lookup| - 1
    ensures IMapsTo(lookup[i].node.children, key, lookup[i+1].ref)
  {
    reveal_LookupFollowsChildRefs();
  }
  
  predicate LookupRespectsDisk<Value>(view: BI.View<Node<Value>>, lookup: Lookup) {
    forall i :: 0 <= i < |lookup| ==> IMapsTo(view, lookup[i].ref, lookup[i].node)
  }

  predicate LookupVisitsWFNodes(lookup: Lookup) {
    forall i :: 0 <= i < |lookup| ==> WFNode(lookup[i].node)
  }

  predicate IsPathFromRootLookup<Value>(k: Constants, view: BI.View<Node<Value>>, key: Key, lookup: Lookup) {
    && |lookup| > 0
    && lookup[0].ref == Root(k)
    && LookupRespectsDisk(view, lookup)
    && LookupFollowsChildRefs(key, lookup)
  }

  function TotalLog<Value>(lookup: Lookup<Value>, key: Key) : seq<BufferEntry<Value>>
  requires LookupVisitsWFNodes(lookup);
  {
    if |lookup| == 0 then [] else TotalLog(lookup[..|lookup|-1], key) + lookup[|lookup|-1].node.buffer[key]
  }

  predicate IsSatisfyingLookup<Value>(k: Constants, view: BI.View<Node<Value>>, key: Key, value: Value, lookup: Lookup) {
    && IsPathFromRootLookup(k, view, key, lookup)
    && LookupVisitsWFNodes(lookup)
    && BufferDefinesValue(TotalLog(lookup, key), value)
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
    && BI.Init(k.bck, s.bcv, EmptyNode())
  }
    
  predicate Query<Value>(k: Constants, s: Variables, s': Variables, key: Key, value: Value, lookup: Lookup) {
    && s == s'
    && IsSatisfyingLookup(k, s.bcv.view, key, value, lookup)
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
    && IMapsTo(s.bcv.view, Root(k), oldroot)
    && WFNode(oldroot)
    && var newroot := AddMessageToNode(oldroot, key, msg);
    && BI.Write(k.bck, s.bcv, s'.bcv, Root(k), newroot, Successors(newroot))
  }

  predicate Flush<Value>(k: Constants, s: Variables, s': Variables, parentref: BI.Reference, parent: Node, childref: BI.Reference, child: Node, newchildref: BI.Reference) {
    var movedKeys := iset k | k in parent.children && parent.children[k] == childref;
    && IMapsTo(s.bcv.view, parentref, parent)
    && IMapsTo(s.bcv.view, childref, child)
    && WFNode(parent)
    && WFNode(child)
    && var newbuffer := imap k :: (if k in movedKeys then parent.buffer[k] + child.buffer[k] else child.buffer[k]);
    && var newchild := Node(child.children, newbuffer);
    && var newparentbuffer := imap k :: (if k in movedKeys then [] else parent.buffer[k]);
    && var newparentchildren := imap k | k in parent.children :: (if k in movedKeys then newchildref else parent.children[k]);
    && var newparent := Node(newparentchildren, newparentbuffer);
    && var allocop := BI.AllocStep(newchild, Successors(newchild), newchildref);
    && var writeop := BI.WriteStep(parentref, newparent, Successors(newparent));
    && BI.Transaction(k.bck, s.bcv, s'.bcv, [allocop, writeop])
  }

  predicate Grow(k: Constants, s: Variables, s': Variables, oldroot: Node, newchildref: BI.Reference) {
    && IMapsTo(s.bcv.view, Root(k), oldroot)
    && var newchild := oldroot;
    && var newroot := Node(
        imap key | MS.InDomain(key) :: newchildref,
        imap key | MS.InDomain(key) :: []);
    && var allocop := BI.AllocStep(newchild, Successors(newchild), newchildref);
    && var writeop := BI.WriteStep(Root(k), newroot, Successors(newroot));
    && BI.Transaction(k.bck, s.bcv, s'.bcv, [allocop, writeop])
  }

  datatype NodeFusion<Value> = NodeFusion(
    parentref: BI.Reference,
    fused_childref: BI.Reference,
    left_childref: BI.Reference,
    right_childref: BI.Reference,
    fused_parent: Node,
    split_parent: Node,
    fused_child: Node,
    left_child: Node,
    right_child: Node,
    
    left_keys: iset<Key>,
    right_keys: iset<Key>
  )

  predicate ValidFusion<Value>(fusion: NodeFusion<Value>)
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

  predicate Split(k: Constants, s: Variables, s': Variables, fusion: NodeFusion)
  {
    && IMapsTo(s.bcv.view, fusion.parentref, fusion.fused_parent)
    && IMapsTo(s.bcv.view, fusion.fused_childref, fusion.fused_child)
    && ValidFusion(fusion)
    && WFNode(fusion.fused_parent)
    && WFNode(fusion.fused_child)
    && WFNode(fusion.left_child)
    && WFNode(fusion.right_child)
    && var allocop_left := BI.AllocStep(fusion.left_child, Successors(fusion.left_child), fusion.left_childref);
    && var allocop_right := BI.AllocStep(fusion.right_child, Successors(fusion.right_child), fusion.right_childref);
    && var writeop := BI.WriteStep(fusion.parentref, fusion.split_parent, Successors(fusion.split_parent));
    && BI.Transaction(k.bck, s.bcv, s'.bcv, [allocop_left, allocop_right, writeop])
  }

  predicate Merge(k: Constants, s: Variables, s': Variables, fusion: NodeFusion)
  {
    && IMapsTo(s.bcv.view, fusion.parentref, fusion.split_parent)
    && IMapsTo(s.bcv.view, fusion.left_childref, fusion.left_child)
    && IMapsTo(s.bcv.view, fusion.right_childref, fusion.right_child)
    && ValidFusion(fusion)
    && var allocop := BI.AllocStep(fusion.fused_child, Successors(fusion.fused_child), fusion.fused_childref);
    && var writeop := BI.WriteStep(fusion.parentref, fusion.fused_parent, Successors(fusion.fused_parent));
    && BI.Transaction(k.bck, s.bcv, s'.bcv, [allocop, writeop])
  }

  predicate GC(k: Constants, s: Variables, s': Variables, refs: iset<BI.Reference>) {
    BI.GC(k.bck, s.bcv, s'.bcv, refs)
  }
  
  datatype Step<Value(!new)> =
    | QueryStep(key: Key, value: Value, lookup: Lookup)
    | InsertMessageStep(key: Key, msg: BufferEntry, oldroot: Node)
    | FlushStep(parentref: BI.Reference, parent: Node, childref: BI.Reference, child: Node, newchildref: BI.Reference)
    | GrowStep(oldroot: Node, newchildref: BI.Reference)
    | SplitStep(fusion: NodeFusion)
    | GCStep(refs: iset<BI.Reference>)
    
  predicate NextStep(k: Constants, s: Variables, s': Variables, step: Step) {
    match step {
      case QueryStep(key, value, lookup) => Query(k, s, s', key, value, lookup)
      case InsertMessageStep(key, msg, oldroot) => InsertMessage(k, s, s', key, msg, oldroot)
      case FlushStep(parentref, parent, childref, child, newchildref) => Flush(k, s, s', parentref, parent, childref, child, newchildref)
      case GrowStep(oldroot, newchildref) => Grow(k, s, s', oldroot, newchildref)
      case SplitStep(fusion) => Split(k, s, s', fusion)
      case GCStep(refs) => GC(k, s, s', refs)
    }
  }

  predicate Next<Value(!new)>(k: Constants, s: Variables, s': Variables) {
    exists step: Step :: NextStep(k, s, s', step)
  }
}
