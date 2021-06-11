include "../lib/Base/total_order.i.dfy"
include "IndirectionTable.i.dfy"
include "AllocationTable.i.dfy"
include "AllocationTableMachine.i.dfy"
include "MsgSeq.i.dfy"
include "SplinterTree.i.dfy"
include "Message.s.dfy"
include "Interp.s.dfy"

/*

  In our splinter datastructure there's two possible things that could be btrees
  The current branch in the membuffer (fully in memory -- but we can asynchronously persist the working branch to disk) and the branch trees in the splinter tree on disk

  Incorporation : Process of updating the splinter tree pointers such that the current branch (is persisted on disk) and added to the splinter tree root

*/
abstract module BtreeModel {
  type Key = Keys.Element
  type Value

  datatype BtreeState = Active | Frozen;
  datatype NodeState = None | OnDisk; // Might need arguments ???

  // Node in the btree
  // A node can either contain a key-value mapping (LEAF) or a sequence of
  // pivots to provide an ordering of the children
  datatype Node =
    | Leaf(linear keys: seq<Key>, values: seq<Value>, state: NodeState)
    | Index(linear pivots: seq<Key>, children: lseq<Node>, state: NodeState)

  datatype Variables = Variables(root : Node, state: BtreeState)


}
