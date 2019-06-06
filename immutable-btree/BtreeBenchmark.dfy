include "../lib/total_order.dfy"
include "BtreeSpec.dfy"
include "BtreeInv.dfy"  
//include "BtreeImpl.dfy"

module Bounded_Integer_Order refines Bounded_Total_Order {
  import Base_Order = Integer_Order
}

module Integer_BtreeSpec refines BtreeSpec {
  import Keyspace = Bounded_Integer_Order
}

module Integer_BtreeInv refines BtreeInv {
  import opened Spec = Integer_BtreeSpec
}

method Main() {
    var nInsertions := 1000 * 1000 * 10;
    var i := 0;
    while i < nInsertions
    {
        var v := (i * 1073741827) % nInsertions;
        i := i + 1;
    }
}

