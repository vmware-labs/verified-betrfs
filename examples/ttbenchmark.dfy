include "tttree.i.dfy"

module Integer_TTTree refines TwoThreeTree {
    import Keyspace = Integer_Order
}

module Seq_Int_TTTree refines TwoThreeTree {
    import Keyspace = Seq_Int_Lex_Order
}

module Seq_Char_TTTree refines TwoThreeTree {
    import Keyspace = Seq_Char_Lex_Order
}

module String_TTTree refines TwoThreeTree {
    import Keyspace = String_Lex_Order
}


method Main() {
    var nInsertions := 1000 * 1000 * 10;
    var t := Integer_TTTree.Tree.EmptyTree;
    var i := 0;
    while i < nInsertions
        invariant Integer_TTTree.TTTree(t);
    {
        var v := (i * 1073741827) % nInsertions;
        t := Integer_TTTree.Insert(t, v, v*v);
        i := i + 1;
    }
}

// Local Variables:
// tab-width: 4
// End:

