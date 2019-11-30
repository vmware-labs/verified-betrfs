include "MutableBtree.dfy"

abstract module MutableBtreeBulkOperations {
  import opened NativeTypes
  import opened MB : MutableBtree

  method NumElements(node: Node) returns (count: uint64)
    requires WFShape(node)
    requires BS.WF(I(node))
    requires BS.NumElements(I(node)) < Uint64UpperBound()
    ensures count as int == BS.NumElements(I(node))
    decreases node.height
  {
    if node.contents.Leaf? {
      count := node.contents.nkeys;
    } else {
      ghost var inode := I(node);
      count := 0;
      ghost var icount: int := 0;
      
      var i: uint64 := 0;
      while i < node.contents.nchildren
        invariant i <= node.contents.nchildren
        invariant icount == BS.NumElementsOfChildren(inode.children[..i])
        invariant icount < Uint64UpperBound()
        invariant count == icount as uint64
      {
        ghost var ichildcount := BS.NumElements(inode.children[i]);
        assert inode.children[..i+1][..i] == inode.children[..i];
        BS.NumElementsOfChildrenNotZero(inode);
        BS.NumElementsOfChildrenDecreases(inode.children, (i+1) as int);
        icount := icount + ichildcount;
        
        var childcount: uint64 := NumElements(node.contents.children[i]);
        count := count + childcount;
        i := i + 1;
      }
      assert inode.children[..node.contents.nchildren] == inode.children;
    }
  }

  method ToSeq(node: Node, keys: array<Key>, values: array<Value>, start: uint64) returns (nextstart: uint64)
    requires WFShape(node)
    requires BS.WF(I(node))
    requires keys.Length == values.Length
    requires 0 <= start as int < keys.Length
    requires start as int + BS.NumElements(I(node)) <= keys.Length
    requires start as int + BS.NumElements(I(node)) < Uint64UpperBound()
    requires keys !in node.repr
    requires values !in node.repr
    requires keys != values
    ensures nextstart as int == start as int + BS.NumElements(I(node))
    ensures forall i :: 0 <= i < start ==> keys[i] == old(keys[i]);
    ensures forall i :: 0 <= i < start ==> values[i] == old(values[i]);
    ensures keys[start..nextstart] == BS.ToSeq(I(node)).0
    // ensures values[start..nextstart] == BS.ToSeq(I(node)).1
    ensures forall i :: nextstart as int <= i < keys.Length ==> keys[i] == old(keys[i]);
    ensures forall i :: nextstart as int <= i < values.Length ==> values[i] == old(values[i]);
    modifies keys, values
    decreases node.height
  {
    if node.contents.Leaf? {
      Arrays.Memcpy(keys, start, node.contents.keys[..node.contents.nkeys]); // FIXME: remove conversion to seq
      Arrays.Memcpy(values, start, node.contents.values[..node.contents.nkeys]); // FIXME: remove conversion to seq
      nextstart := start + node.contents.nkeys;
    } else {
      forall i | 0 <= i < node.contents.nchildren
        ensures BS.NumElementsOfChildren(I(node).children[..i]) <= BS.NumElements(I(node))
      {
        BS.NumElementsOfChildrenNotZero(I(node));
        BS.NumElementsOfChildrenDecreases(I(node).children, i as int);
      }
      
      nextstart := start;
      ghost var inextstart := start as int;
      var i: uint64 := 0;
      while i < node.contents.nchildren
        invariant 0 <= i <= node.contents.nchildren
        invariant inextstart == start as int + BS.NumElementsOfChildren(I(node).children[..i])
        invariant nextstart as int == inextstart
        //invariant start as int <= inextstart
        invariant i < node.contents.nchildren ==> inextstart < keys.Length
        invariant forall i :: 0 <= i < start ==> keys[i] == old(keys[i])
        invariant forall i :: 0 <= i < start ==> values[i] == old(values[i])
        //invariant keys[start..inextstart] == BS.Seq.Flatten(BS.ToSeqChildren(I(node).children[..i]).0)
        // invariant values[start..inextstart] == BS.Seq.Flatten(BS.ToSeqChildren(I(node).children[..i]).1)
        invariant forall i :: inextstart <= i < keys.Length ==> keys[i] == old(keys[i])
        invariant forall i :: inextstart <= i < values.Length ==> values[i] == old(values[i])
      {
        BS.NumElementsOfChildrenNotZero(I(node));
        BS.NumElementsOfChildrenDecreases(I(node).children, i as int);
        assert inextstart < keys.Length;
        
        assert I(node).children[..i+1][..i] == I(node).children[..i];
        inextstart := inextstart + BS.NumElements(I(node).children[i]);
        BS.NumElementsOfChildrenDecreases(I(node).children, i as int + 1);
        
        //assert BS.NumElementsOfChildren(I(node).children[..i]) + BS.NumElements(I(node.contents.children[i])) ==
        //BS.NumElementsOfChildren(I(node).children[..i+1]);
        //assert BS.NumElementsOfChildren(I(node).children[..i+1]) <= BS.NumElements(I(node));
        //assert inextstart as int + BS.NumElements(I(node.contents.children[i])) == start as int +
        //  BS.NumElementsOfChildren(I(node).children[..i+1]);
        //assert inextstart as int + BS.NumElements(I(node.contents.children[i])) <= keys.Length;

        //assert I(node.contents.children[i]) == I(node).children[i];
        //assert keys.Length == old(keys.Length);
        ghost var oldnextstart := nextstart;
        nextstart := ToSeq(node.contents.children[i], keys, values, nextstart);

        //assert keys[start..oldnextstart] == BS.Seq.Flatten(BS.ToSeqChildren(I(node).children[..i]).0);
        //assert keys[oldnextstart..nextstart] == BS.ToSeq(I(node.contents.children[i])).0;

        // forall j | 0 <= j < |keys[start..inextstart]|
        //   ensures keys[start..inextstart][j] == BS.Seq.Flatten(BS.ToSeqChildren(I(node).children[..i+1]).0)[j]
        // {
        //   assume false;
        // }
      
        // var nextstep := NumElements(node.contents.children[i]);
        // assert nextstart as int + nextstep as int == inextstart;
        // assert inextstart < Uint64UpperBound();
        // nextstart := nextstart + nextstep;
        i := i + 1;
        //assume false;
        //assume keys[start..inextstart] == BS.Seq.Flatten(BS.ToSeqChildren(I(node).children[..i]).0);
      }
      assert I(node).children[..node.contents.nchildren] == I(node).children;
      //nextstart := inextstart as uint64;
      //assume false;
    }
  }
}
