include "../lib/total_order.s.dfy"

abstract module CrashableMap {
  import Keyspace : Bounded_Total_Order
  type Key = Keyspace.Element
}

abstract module BtreeSpec {
  import CMap : CrashableMap
  type Key = CMap.Key
}

abstract module BtreeInv {
  import opened Spec : BtreeSpec
}

abstract module BtreeRefinement {
  import opened BtreeSpec
  import opened BtreeInv
}

abstract module BtreeImpl {
  import opened BtreeSpec
  import opened BtreeInv
}

module IntegerCrashableMap refines CrashableMap {
  import Keyspace = Bounded_Integer_Order
}

module IntegerBtreeSpec refines BtreeSpec {
  import CMap = IntegerCrashableMap

  predicate foo(key: Key) { key == CMap.Keyspace.Element(5) }
}

module IntegerBtreeInv refines BtreeInv {
  import opened Spec = IntegerBtreeSpec
}
