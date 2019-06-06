include "../lib/total_order.dfy"
include "BtreeImple.dfy"

module Integer_BTree refines BtreeImpl {
    import Keyspace = Integer_Order
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

