include "../lib/Base/total_order.i.dfy"
include "IndirectionTable.i.dfy"
include "AllocationTable.i.dfy"
include "AllocationTableMachine.i.dfy"
include "MsgSeq.i.dfy"
include "SplinterTree.i.dfy"
include "Message.s.dfy"
include "Interp.s.dfy"

abstract module BtreeModel {
  type Key = Keys.Element
  type Value


  datatype NodeState = None | OnDisk; // Might need arguments ???

  // Node in the btree
  // A node can either contain a key-value mapping (LEAF) or a sequence of
  // pivots to provide an ordering of the children
  datatype Node =
    | Leaf(linear keys: seq<Key>, values: seq<Value>, state: NodeState)
    | Index(linear pivots: seq<Key>, children: lseq<Node>)




}
