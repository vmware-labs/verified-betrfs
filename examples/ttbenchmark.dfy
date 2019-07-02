include "../lib/NativeTypes.dfy"
include "tttree.dfy"

import opened NT = NativeTypes

module uint64_Order refines Total_Order {
  import opened NativeTypes
  type Element = uint64

  predicate method lte(a: Element, b: Element) {
    reveal_ltedef();
    ltedef(a, b)
  }

  predicate method {:opaque} ltedef(a: Element, b: Element) {
    a <= b
  }
}

module uint64_TTTree refines TwoThreeTree {
  import Keyspace = uint64_Order
}

// module Integer_TTTree refines TwoThreeTree {
//     import Keyspace = Integer_Order
// }

// module Seq_Int_TTTree refines TwoThreeTree {
//     import Keyspace = Seq_Int_Lex_Order
// }

// module Seq_Char_TTTree refines TwoThreeTree {
//     import Keyspace = Seq_Char_Lex_Order
// }

// module String_TTTree refines TwoThreeTree {
//     import Keyspace = String_Lex_Order
// }

method Main() {
    var nInsertions: uint64 := 1000 * 1000 * 10;
    var t := uint64_TTTree.Tree.EmptyTree;
    var i: uint64 := 0;
    while i < nInsertions
        invariant uint64_TTTree.TTTree(t);
    {
        var v: uint64 := (i * 1073741827) % nInsertions;
        t := uint64_TTTree.Insert(t, v, v);
        i := i + 1;
    }
}

// Local Variables:
// tab-width: 4
// End:

