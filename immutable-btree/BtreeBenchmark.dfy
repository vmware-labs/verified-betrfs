include "../lib/total_order.s.dfy"
include "CrashSafeMap.dfy"
include "BtreeSpec.dfy"
include "BtreeInv.dfy"  
include "BtreeImpl.dfy"  

module IntegerCrashSafeMap refines CrashSafeMap {
  import Keyspace = Bounded_Integer_Order
}

module IntegerBtreeSpec refines BtreeSpec {
  import CSMap = IntegerCrashSafeMap
}

module IntegerBtreeInv refines BtreeInv {
  import opened Spec = IntegerBtreeSpec
}

module IntegerBtreeImpl refines BtreeImpl {
  import opened Inv = IntegerBtreeInv
}

method Main() {
    var tree := IntegerBtreeImpl.empty();

    var nInsertions := 1000;
    var i := 0;
    while i < nInsertions
    invariant IntegerBtreeInv.Invariant(
        IntegerBtreeSpec.Constants(),
        IntegerBtreeSpec.Variables(tree));
    {
        var v := (i * 1073741827) % nInsertions;
        var w := (i * 1234141827) % nInsertions;
        i := i + 1;

        var k := Bounded_Integer_Order.Element(v);

        ghost var oldtree := tree;
        tree := IntegerBtreeImpl.put(tree, k, w);

        IntegerBtreeInv.PutPreservesInvariant(
          IntegerBtreeSpec.Constants(),
          IntegerBtreeSpec.Variables(oldtree),
          IntegerBtreeSpec.Variables(tree), k, w);
    }
}

