include "../lib/total_order.dfy"
include "BtreeSpec.dfy"
include "BtreeInv.dfy"  
//include "BtreeImpl.dfy"

method Main() {
    var tree = BtreeImpl.empty();

    var nInsertions := 1000 * 1000 * 10;
    var i := 0;
    while i < nInsertions
    invariant WFTree(tree)
    {
        var v := (i * 1073741827) % nInsertions;
        var w := (i * 1234141827) % nInsertions;
        i := i + 1;

        var k = Bounded_Integer_Order.Element(v);

        tree = BtreeImpl.put(tree, k, w);
    }
}

