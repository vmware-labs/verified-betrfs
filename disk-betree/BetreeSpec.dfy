include "BlockInterface.dfy"  
include "../lib/sequences.dfy"
include "../lib/Maps.dfy"
include "MapSpec.dfy"
include "Graph.dfy"

module BetreeGraph refines Graph {
  import MS = MapSpec

  type Value(!new)

  type Key = MS.Key
  datatype BufferEntry = Insertion(value: Value)
  type Buffer = imap<Key, seq<BufferEntry>>
  datatype Node = Node(children: imap<Key, Reference>, buffer: Buffer)

  function Successors(node: Node) : iset<Reference>
  {
    iset k | k in node.children :: node.children[k]
  }
}

module BetreeBlockInterface refines BlockInterface {
  import G = BetreeGraph
}

module BetreeSpecCommon {

  import MS = MapSpec
  import opened G = BetreeGraph
  import opened Sequences
  import opened Maps

  predicate BufferIsDefining(log: seq<BufferEntry>) {
    && |log| > 0
  }

  predicate BufferDefinesValue(log: seq<BufferEntry>, value: Value) {
    && BufferIsDefining(log)
    && log[0].value == value
  }
  
  predicate WFNode(node: Node) {
    && (forall k :: k in node.buffer)
    && (forall k :: k !in node.children ==> BufferIsDefining(node.buffer[k]))
  }

  // Now we define the state machine
  

  function EmptyNode() : Node {
    var buffer := imap key | MS.InDomain(key) :: [Insertion(MS.EmptyValue())];
    Node(imap[], buffer)
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
}

module BetreeSpec refines BetreeSpecCommon {
  import Tr = BetreeBlockInterface

  predicate InsertMessage(k: Tr.Constants, s: Tr.Variables, s': Tr.Variables, key: Key, msg: BufferEntry, oldroot: Node) {
    && Tr.Reads(k, s, Root(), oldroot)
    && WFNode(oldroot)
    && var newroot := AddMessageToNode(oldroot, key, msg);
    && var writeop := G.WriteOp(Root(), newroot);
    && Tr.Transaction(k, s, s', [writeop])
  }

  predicate Flush(k: Tr.Constants, s: Tr.Variables, s': Tr.Variables, parentref: Reference, parent: Node, childref: Reference, child: Node, newchildref: Reference) {
    var movedKeys := iset k | k in parent.children && parent.children[k] == childref;
    && Tr.Reads(k, s, parentref, parent)
    && Tr.Reads(k, s, childref, child)
    && WFNode(parent)
    && WFNode(child)
    && var newbuffer := imap k :: (if k in movedKeys then parent.buffer[k] + child.buffer[k] else child.buffer[k]);
    && var newchild := Node(child.children, newbuffer);
    && var newparentbuffer := imap k :: (if k in movedKeys then [] else parent.buffer[k]);
    && var newparentchildren := imap k | k in parent.children :: (if k in movedKeys then newchildref else parent.children[k]);
    && var newparent := Node(newparentchildren, newparentbuffer);
    && var allocop := G.AllocOp(newchildref, newchild);
    && var writeop := G.WriteOp(parentref, newparent);
    && Tr.Transaction(k, s, s', [allocop, writeop])
  }

  predicate Grow(k: Tr.Constants, s: Tr.Variables, s': Tr.Variables, oldroot: Node, newchildref: Reference) {
    && Tr.Reads(k, s, Root(), oldroot)
    && var newchild := oldroot;
    && var newroot := Node(
        imap key | MS.InDomain(key) :: newchildref,
        imap key | MS.InDomain(key) :: []);
    && var allocop := G.AllocOp(newchildref, newchild);
    && var writeop := G.WriteOp(Root(), newroot);
    && Tr.Transaction(k, s, s', [allocop, writeop])
  }

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

  predicate Split(k: Tr.Constants, s: Tr.Variables, s': Tr.Variables, fusion: NodeFusion)
  {
    && Tr.Reads(k, s, fusion.parentref, fusion.fused_parent)
    && Tr.Reads(k, s, fusion.fused_childref, fusion.fused_child)
    && ValidFusion(fusion)
    && WFNode(fusion.fused_parent)
    && WFNode(fusion.fused_child)
    && WFNode(fusion.left_child)
    && WFNode(fusion.right_child)
    && var allocop_left := G.AllocOp(fusion.left_childref, fusion.left_child);
    && var allocop_right := G.AllocOp(fusion.right_childref, fusion.right_child);
    && var writeop := G.WriteOp(fusion.parentref, fusion.split_parent);
    && Tr.Transaction(k, s, s', [allocop_left, allocop_right, writeop])
  }

  predicate Merge(k: Tr.Constants, s: Tr.Variables, s': Tr.Variables, fusion: NodeFusion)
  {
    && Tr.Reads(k, s, fusion.parentref, fusion.split_parent)
    && Tr.Reads(k, s, fusion.left_childref, fusion.left_child)
    && Tr.Reads(k, s, fusion.right_childref, fusion.right_child)
    && ValidFusion(fusion)
    && var allocop := G.AllocOp(fusion.fused_childref, fusion.fused_child);
    && var writeop := G.WriteOp(fusion.parentref, fusion.fused_parent);
    && Tr.Transaction(k, s, s', [allocop, writeop])
  }
}
