include "../lib/total_order.dfy"
include "BtreeSpec.dfy"
include "BtreeInv.dfy"  
include "BtreeImpl.dfy"  
//include "BtreeImpl.dfy"

method Main() {
    var tree := BtreeImpl.empty();

    var nInsertions := 10;
    var i := 0;
    while i < nInsertions
    invariant BtreeInv.Invariant(
        BtreeSpec.Constants(),
        BtreeSpec.Variables(tree));
    {
        var v := (i * 1073741827) % nInsertions;
        var w := (i * 1234141827) % nInsertions;
        i := i + 1;

        var k := Bounded_Integer_Order.Element(v);

        ghost var oldtree := tree;
        tree := BtreeImpl.put(tree, k, w);

        BtreeInv.PutPreservesInvariant(
          BtreeSpec.Constants(),
          BtreeSpec.Variables(oldtree),
          BtreeSpec.Variables(tree), k, w);
    }
}

