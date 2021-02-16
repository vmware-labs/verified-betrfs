include "../Betree/Graph.i.dfy"
include "../lib/Base/Message.i.dfy"
include "../lib/Buckets/BoundedPivotsLib.i.dfy"
include "../lib/Buckets/BucketsLib.i.dfy"

module PivotBetreeGraph refines Graph {
  import opened Options
  import opened ValueMessage
  import opened KeyType
  import opened BucketsLib
  import opened BoundedPivotsLib

  import Keyspace = Lexicographic_Byte_Order
  import KeyspaceImpl = Lexicographic_Byte_Order_Impl

  datatype Node = Node(
      pivotTable: PivotTable,
      children: Option<seq<Reference>>,
      buckets: seq<Bucket>)

  function Successors(node: Node) : iset<Reference>
  {
    if node.children.Some? then (
      iset i | 0 <= i < |node.children.value| :: node.children.value[i]
    ) else (
      iset{}
    )
  }
}
