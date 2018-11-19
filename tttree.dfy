include "total_order.dfy"
include "lexical.dfy"
include "map_utils.dfy"
include "mathematics.dfy"

abstract module TwoThreeTree {
    import Keyspace : Total_Order
    import Maps = Map_Utils
    import Math = Mathematics
    
    datatype Node<Value> =
        Leaf(key: Keyspace.Element, value: Value) |
        TwoNode(left: Node, pivot: Keyspace.Element, right: Node) |
        ThreeNode(left: Node, pivota: Keyspace.Element,
                  middle: Node, pivotb: Keyspace.Element,
                  right: Node)

    function SubtreeAllKeys(tree: Node) : set<Keyspace.Element>
        ensures SubtreeAllKeys(tree) != {};
    {
        match tree {
            case Leaf(key, value) => {key}
            case TwoNode(left, pivot, right) => SubtreeAllKeys(left) + {pivot} + SubtreeAllKeys(right)
            case ThreeNode(left, pivota, middle, pivotb, right) =>
                SubtreeAllKeys(left) + {pivota} + SubtreeAllKeys(middle) + {pivotb} + SubtreeAllKeys(right)
        }
    }

    predicate ContentsAreLessThan(tree: Node, pivot: Keyspace.Element) {
        forall lv :: lv in SubtreeAllKeys(tree) ==> Keyspace.lt(lv, pivot)
    }

    predicate ContentsAreGreaterEqualThan(pivot: Keyspace.Element, tree: Node) {
        forall lv :: lv in SubtreeAllKeys(tree) ==> !Keyspace.lt(lv, pivot)
    }

    predicate {:opaque} TreeIsOrdered(tree: Node)
        ensures TreeIsOrdered(tree) && tree.TwoNode? ==>
            ContentsAreLessThan(tree.left, tree.pivot) &&
            ContentsAreGreaterEqualThan(tree.pivot, tree.right);
        ensures TreeIsOrdered(tree) && tree.ThreeNode? ==>
            Keyspace.lt(tree.pivota, tree.pivotb) &&
            ContentsAreLessThan(tree.left, tree.pivota) &&
            ContentsAreGreaterEqualThan(tree.pivota, tree.middle) &&
            ContentsAreLessThan(tree.middle, tree.pivotb) &&
            ContentsAreGreaterEqualThan(tree.pivotb, tree.right);
        ensures tree.Leaf? ==> TreeIsOrdered(tree);
    {
        if tree.Leaf?
            then true
        else if tree.TwoNode?
            then
            ContentsAreLessThan(tree.left, tree.pivot) &&
            ContentsAreGreaterEqualThan(tree.pivot, tree.right) &&
            TreeIsOrdered(tree.left) &&
            TreeIsOrdered(tree.right)
        else
            Keyspace.lt(tree.pivota, tree.pivotb) &&
            ContentsAreLessThan(tree.left, tree.pivota) &&
            ContentsAreGreaterEqualThan(tree.pivota, tree.middle) &&
            ContentsAreLessThan(tree.middle, tree.pivotb) &&
            ContentsAreGreaterEqualThan(tree.pivotb, tree.right) &&
            TreeIsOrdered(tree.left) &&
            TreeIsOrdered(tree.middle) &&
            TreeIsOrdered(tree.right)
    }

    function SubtreeContents<Value>(tree: Node<Value>) : map<Keyspace.Element, Value>
        requires TreeIsOrdered(tree);
        ensures SubtreeContents(tree).Keys <= SubtreeAllKeys(tree);
        ensures SubtreeContents(tree) != map[];
    {
        if tree.Leaf? then
            var r := map[tree.key := tree.value];
            assert tree.key in r; // observe that r is not friggin empty
            r
        else if tree.TwoNode? then
            reveal_TreeIsOrdered();
            assert SubtreeContents(tree.left).Keys !! SubtreeContents(tree.right).Keys; // observe
            Maps.disjoint_union(SubtreeContents(tree.left), SubtreeContents(tree.right))
        else
            reveal_TreeIsOrdered();
            assert SubtreeContents(tree.left).Keys
                !! SubtreeContents(tree.middle).Keys
                !! SubtreeContents(tree.right).Keys; // observe
            Maps.disjoint_union3(SubtreeContents(tree.left),
                                 SubtreeContents(tree.middle), 
                                 SubtreeContents(tree.right))
    }

    datatype QueryResult<Value> = KeyDoesNotExist | ValueForKey(value: Value)

    function method QuerySubtree<Value>(tree: Node<Value>, key: Keyspace.Element) : QueryResult<Value>
        requires TreeIsOrdered(tree);
        ensures QuerySubtree(tree, key) == KeyDoesNotExist <==>
            (key !in SubtreeContents(tree));
            ensures QuerySubtree(tree, key).ValueForKey? <==>
                (key in SubtreeContents(tree) && SubtreeContents(tree)[key] == QuerySubtree(tree, key).value);
    {
        reveal_TreeIsOrdered();
        if tree.Leaf? && tree.key == key then
            ValueForKey(tree.value)
        else if tree.Leaf? && tree.key != key then
            KeyDoesNotExist
        else if tree.TwoNode? && Keyspace.lt(key, tree.pivot) then
            QuerySubtree(tree.left, key)
        else if tree.TwoNode? && !Keyspace.lt(key, tree.pivot) then
            QuerySubtree(tree.right, key)
        else if tree.ThreeNode? && Keyspace.lt(key, tree.pivota) then
            QuerySubtree(tree.left, key)
        else if tree.ThreeNode? && Keyspace.lt(key, tree.pivotb) then
            QuerySubtree(tree.middle, key)
        else
            QuerySubtree(tree.right, key)
    }

    function {:opaque} minHeight(tree: Node) : int
    {
        if tree.Leaf?
            then 0
        else if tree.TwoNode?
            then 1 + Math.min(minHeight(tree.left), minHeight(tree.right))
        else 
            1 + Math.min(minHeight(tree.left), Math.min(minHeight(tree.middle), minHeight(tree.right)))
    }

    function {:opaque} maxHeight(tree: Node) : int
    {
        if tree.Leaf?
            then 0
        else if tree.TwoNode?
            then 1 + Math.max(maxHeight(tree.left), maxHeight(tree.right))
        else
            1 + Math.max(maxHeight(tree.left), Math.max(maxHeight(tree.middle), maxHeight(tree.right)))
    }

    predicate balanced(tree: Node) {
        minHeight(tree) == maxHeight(tree)
    }
    
    predicate {:opaque} recursivelyBalanced(tree: Node)
        ensures recursivelyBalanced(tree) ==> balanced(tree);
        ensures tree.Leaf? ==> recursivelyBalanced(tree);
    {
        reveal_minHeight();
        reveal_maxHeight();
           balanced(tree)
        && (!tree.Leaf? ==> recursivelyBalanced(tree.left) && recursivelyBalanced(tree.right))
        && (tree.ThreeNode? ==> recursivelyBalanced(tree.middle))
    }

    predicate TTSubtree(tree: Node) {
           TreeIsOrdered(tree)
        && recursivelyBalanced(tree)
    }

    function Height(tree: Node) : int
        requires(balanced(tree));
    {
        minHeight(tree)
    }

    function method mkTwoNode(t1: Node, pivot: Keyspace.Element, t2: Node) : Node
        requires TTSubtree(t1);
        requires TTSubtree(t2);
        requires Height(t1) == Height(t2);
        requires ContentsAreLessThan(t1, pivot);
        requires ContentsAreGreaterEqualThan(pivot, t2);
        requires SubtreeContents(t1).Keys !! SubtreeContents(t2).Keys; // Should be implied, but dafny can't always see it
        ensures TTSubtree(mkTwoNode(t1, pivot, t2));
        ensures SubtreeAllKeys(mkTwoNode(t1, pivot, t2)) == SubtreeAllKeys(t1) + { pivot } + SubtreeAllKeys(t2);
        ensures SubtreeContents(mkTwoNode(t1, pivot, t2)) ==
            Maps.disjoint_union(SubtreeContents(t1), SubtreeContents(t2));
        ensures Height(mkTwoNode(t1, pivot, t2)) == Height(t1) + 1;
    {
        reveal_TreeIsOrdered();
        reveal_recursivelyBalanced();
        reveal_minHeight();
        reveal_maxHeight();
        TwoNode(t1, pivot, t2)
    }

    function method mkThreeNode(t1: Node, pivota: Keyspace.Element,
        t2: Node, pivotb: Keyspace.Element, t3: Node) : Node
        requires TTSubtree(t1);
        requires TTSubtree(t2);
        requires TTSubtree(t3);
        requires Height(t1) == Height(t2) == Height(t3);
        requires Keyspace.lt(pivota, pivotb);
        requires ContentsAreLessThan(t1, pivota);
        requires ContentsAreGreaterEqualThan(pivota, t2);
        requires ContentsAreLessThan(t2, pivotb);
        requires ContentsAreGreaterEqualThan(pivotb, t3);
        requires SubtreeContents(t1).Keys !! SubtreeContents(t2).Keys !! SubtreeContents(t3).Keys; // Should be implied, but dafny can't always see it
        ensures TTSubtree(mkThreeNode(t1, pivota, t2, pivotb, t3));
        ensures SubtreeAllKeys(mkThreeNode(t1, pivota, t2, pivotb, t3)) ==
            SubtreeAllKeys(t1) + { pivota } + SubtreeAllKeys(t2) + { pivotb } + SubtreeAllKeys(t3);
        ensures SubtreeContents(mkThreeNode(t1, pivota, t2, pivotb, t3)) ==
            Maps.disjoint_union3(SubtreeContents(t1), SubtreeContents(t2), SubtreeContents(t3));
        ensures Height(mkThreeNode(t1, pivota, t2, pivotb, t3)) == Height(t1) + 1;
    {
        reveal_TreeIsOrdered();
        reveal_recursivelyBalanced();
        reveal_minHeight();
        reveal_maxHeight();
        ThreeNode(t1, pivota, t2, pivotb, t3)
    }

    datatype InsertionResult<Value> =
        Split(tree: Node<Value>) |
        DidntSplit(tree: Node<Value>)

    predicate ValidInsertionResult<Value>(result: InsertionResult<Value>, tree: Node<Value>,
                                          key: Keyspace.Element, value: Value)
        requires TTSubtree(tree);
    {
        TTSubtree(result.tree) &&
           (SubtreeAllKeys(result.tree) == SubtreeAllKeys(tree) + {key}) &&
           (SubtreeContents(result.tree) == SubtreeContents(tree)[key := value]) &&
           (result.Split? ==> result.tree.TwoNode?) &&
           (result.Split? ==> Height(result.tree) == Height(tree) + 1) &&
           (result.DidntSplit? ==> Height(result.tree) == Height(tree))
    }

    method InsertIntoLeaf<Value>(tree: Node<Value>, key: Keyspace.Element, value: Value)
        returns (result: InsertionResult<Value>)
        requires TTSubtree(tree);
        requires tree.Leaf?;
        ensures ValidInsertionResult(result, tree, key, value);
    {
        reveal_minHeight();
        reveal_maxHeight();
        reveal_recursivelyBalanced();
        if tree.key == key {
            result := DidntSplit(Leaf(key, value));
        } else if Keyspace.lt(tree.key, key) {
            var newright := Leaf(key, value);
            var newtree := mkTwoNode(tree, key, newright);
            result := Split(newtree);
        } else {
            var newleft := Leaf(key, value);
            var newtree := mkTwoNode(newleft, tree.key, tree);
            result := Split(newtree);
        }
        reveal_TreeIsOrdered();
    }

    lemma childrenAreSubtrees<Value>(tree: Node<Value>)
        requires TTSubtree(tree);
        ensures !tree.Leaf? ==> TTSubtree(tree.left);
        ensures !tree.Leaf? ==> TTSubtree(tree.right);
        ensures tree.ThreeNode? ==> TTSubtree(tree.middle);
    {
        reveal_recursivelyBalanced();
        reveal_TreeIsOrdered();
    }

    lemma childHeightsEqual<Value>(tree: Node<Value>)
        requires TTSubtree(tree);
        ensures !tree.Leaf? ==> balanced(tree.left);
        ensures !tree.Leaf? ==> balanced(tree.right);
        ensures !tree.Leaf? ==> (Height(tree.left) == Height(tree.right));
        ensures tree.ThreeNode? ==> (balanced(tree.middle) && Height(tree.left) == Height(tree.middle));
        ensures !tree.Leaf? ==> (Height(tree.left) == Height(tree) - 1);
    {
        reveal_recursivelyBalanced();
        reveal_TreeIsOrdered();
        reveal_minHeight();
        reveal_maxHeight();
    }

    method InsertIntoTwoNodeLeft<Value>(tree: Node<Value>, key: Keyspace.Element, value: Value)
        returns (result: InsertionResult<Value>)
        requires TTSubtree(tree);
        requires tree.TwoNode?;
        requires Keyspace.lt(key, tree.pivot);
        ensures ValidInsertionResult(result, tree, key, value);
        decreases tree, 0;
    {
        childrenAreSubtrees(tree);
        childHeightsEqual(tree);
        var subresult := InsertIntoSubtree(tree.left, key, value);
        childrenAreSubtrees(subresult.tree);
        childHeightsEqual(subresult.tree);
        if !subresult.Split? {
            result := DidntSplit(mkTwoNode(subresult.tree, tree.pivot, tree.right));
        } else {
            result := DidntSplit(mkThreeNode(subresult.tree.left, subresult.tree.pivot,
                                            subresult.tree.right, tree.pivot,
                                            tree.right));
        }
    }

    method InsertIntoTwoNodeRight<Value>(tree: Node<Value>, key: Keyspace.Element, value: Value)
        returns (result: InsertionResult<Value>)
        requires TTSubtree(tree);
        requires tree.TwoNode?;
        requires key == tree.pivot || Keyspace.lt(tree.pivot, key);
        ensures ValidInsertionResult(result, tree, key, value);
        decreases tree, 0;
    {
        childrenAreSubtrees(tree);
        childHeightsEqual(tree);
        var subresult := InsertIntoSubtree(tree.right, key, value);
        childrenAreSubtrees(subresult.tree);
        childHeightsEqual(subresult.tree);
        if !subresult.Split? {
            result := DidntSplit(mkTwoNode(tree.left, tree.pivot, subresult.tree));
        } else {
            result := DidntSplit(mkThreeNode(tree.left, tree.pivot,
                                            subresult.tree.left, subresult.tree.pivot,
                                            subresult.tree.right));
        }
    }

    method InsertIntoTwoNode<Value>(tree: Node<Value>, key: Keyspace.Element, value: Value)
     returns (result: InsertionResult<Value>)
     requires TTSubtree(tree);
     requires tree.TwoNode?;
     ensures ValidInsertionResult(result, tree, key, value);
     decreases tree, 1;
    {
        if Keyspace.lt(key, tree.pivot) {
            result := InsertIntoTwoNodeLeft(tree, key, value);
        } else {
            result := InsertIntoTwoNodeRight(tree, key, value);
        }
    }
    
    method InsertIntoThreeNodeLeft<Value>(tree: Node<Value>, key: Keyspace.Element, value: Value)
     returns (result: InsertionResult<Value>)
     requires TTSubtree(tree);
     requires tree.ThreeNode?;
     requires Keyspace.lt(key, tree.pivota);
     ensures ValidInsertionResult(result, tree, key, value);
     decreases tree, 0;
    {
        childrenAreSubtrees(tree);
        childHeightsEqual(tree);
        var subresult := InsertIntoSubtree(tree.left, key, value);
        childrenAreSubtrees(subresult.tree);
        childHeightsEqual(subresult.tree);
        if !subresult.Split? {
            result := DidntSplit(mkThreeNode(subresult.tree, tree.pivota,
                                            tree.middle, tree.pivotb,
                                            tree.right));
        } else {
            var newright := mkTwoNode(tree.middle, tree.pivotb, tree.right);
            var newtree := mkTwoNode(subresult.tree, tree.pivota, newright);
            result := Split(newtree);
        }
    }

    method InsertIntoThreeNodeMiddle<Value>(tree: Node<Value>, key: Keyspace.Element, value: Value)
     returns (result: InsertionResult<Value>)
     requires TTSubtree(tree);
     requires tree.ThreeNode?;
     requires (tree.pivota == key || Keyspace.lt(tree.pivota, key));
     requires Keyspace.lt(key, tree.pivotb);
     ensures ValidInsertionResult(result, tree, key, value);
     decreases tree, 0;
    {
        childrenAreSubtrees(tree);
        childHeightsEqual(tree);
        var subresult := InsertIntoSubtree(tree.middle, key, value);
        childrenAreSubtrees(subresult.tree);
        childHeightsEqual(subresult.tree);
        if !subresult.Split? {
            result := DidntSplit(mkThreeNode(tree.left, tree.pivota,
                                          subresult.tree, tree.pivotb,
                                                    tree.right));
        } else {
            var newleft := mkTwoNode(tree.left, tree.pivota, subresult.tree.left);
            var newright := mkTwoNode(subresult.tree.right, tree.pivotb, tree.right);
            var newtree := mkTwoNode(newleft, subresult.tree.pivot, newright);
            result := Split(newtree);
        }
    }

    method InsertIntoThreeNodeRight<Value>(tree: Node<Value>, key: Keyspace.Element, value: Value)
     returns (result: InsertionResult<Value>)
     requires TTSubtree(tree);
     requires tree.ThreeNode?;
     requires tree.pivotb == key || Keyspace.lt(tree.pivotb, key);
     ensures ValidInsertionResult(result, tree, key, value);
     decreases tree, 0;
    {
        childrenAreSubtrees(tree);
        childHeightsEqual(tree);
        var subresult := InsertIntoSubtree(tree.right, key, value);
        childrenAreSubtrees(subresult.tree);
        childHeightsEqual(subresult.tree);
        if !subresult.Split? {
            result := DidntSplit(mkThreeNode(tree.left, tree.pivota,
                                  tree.middle, tree.pivotb,
                                                    subresult.tree));
        } else {
            var newleft := mkTwoNode(tree.left, tree.pivota, tree.middle);
            var newtree := mkTwoNode(newleft, tree.pivotb, subresult.tree);
            result := Split(newtree);
        }
    }

    method InsertIntoThreeNode<Value>(tree: Node<Value>, key: Keyspace.Element, value: Value)
     returns (result: InsertionResult<Value>)
     requires TTSubtree(tree);
     requires tree.ThreeNode?;
     ensures ValidInsertionResult(result, tree, key, value);
     decreases tree, 1;
    {
        if Keyspace.lt(key, tree.pivota) {
            result := InsertIntoThreeNodeLeft(tree, key, value);
        } else if Keyspace.lt(key, tree.pivotb) {
            result := InsertIntoThreeNodeMiddle(tree, key, value);
        } else {
            result := InsertIntoThreeNodeRight(tree, key, value);
        }
    }
    
    method InsertIntoSubtree<Value>(tree: Node<Value>, key: Keyspace.Element, value: Value)
     returns (result: InsertionResult<Value>)
     requires TTSubtree(tree);
     ensures ValidInsertionResult(result, tree, key, value);
     decreases tree, 3;
    {
        if tree.Leaf? {
            result := InsertIntoLeaf(tree, key, value);
        } else if tree.TwoNode? {
            result := InsertIntoTwoNode(tree, key, value);
        } else {
            result := InsertIntoThreeNode(tree, key, value);
        }
    }
    
    
    // datatype DeletionResult<Value> =
    //  NothingLeft |
    //  Merged(tree: Node<Value>) |
    //  DidntMerge(tree: Node<Value>)

    // predicate ValidDeletionResult<Value>(result: DeletionResult<Value>, tree: Node<Value>,
    //  key: Keyspace.Element)
    //  requires TTSubtree(tree);
    // {
    //  if result.NothingLeft? then
    //      tree.Leaf? && tree.key == key
    //  else 
    //   TTSubtree(result.tree) &&
    //   (SubtreeAllKeys(result.tree) <= SubtreeAllKeys(tree)) &&
    //   (SubtreeContents(result.tree).Keys == SubtreeContents(tree).Keys - {key}) && 
    //   (forall x :: x in SubtreeContents(result.tree) ==>
    //   SubtreeContents(result.tree)[x] == SubtreeContents(tree)[x]) &&
    //   (result.Merged? ==> !tree.Leaf?) &&
    //   (result.Merged? ==> Height(result.tree) == Height(tree) - 1) &&
    //   (!result.Merged? ==> Height(result.tree) == Height(tree))
    // }
        
    // method DeleteFromLeaf<Value>(tree: Node<Value>, key: Keyspace.Element)
    //  returns (result: DeletionResult<Value>)
    //  requires TTSubtree(tree);
    //  requires tree.Leaf?;
    //  ensures ValidDeletionResult(result, tree, key);
    // {
    //  if tree.key == key {
    //      result := NothingLeft;
    //  } else {
    //      result := DidntMerge(tree);
    //  }
    // }

    // method DeleteFromTwoNodeLeft<Value>(tree: Node<Value>, key: Keyspace.Element)
    //  returns (result: DeletionResult<Value>)
    //  requires TTSubtree(tree);
    //  requires tree.TwoNode?;
    //  requires Keyspace.lt(key, tree.pivot);
    //  ensures ValidDeletionResult(result, tree, key);
    //  decreases tree, 0;
    // {
    //  var subresult := DeleteFromSubtree(tree.left, key);
    //  if subresult.NothingLeft? {
    //      result := Merged(tree.right);
    //  } else if subresult.DidntMerge? {
    //      result := DidntMerge(mkTwoNode(subresult.tree, tree.pivot, tree.right));
    //  } else {
    //      if tree.right.TwoNode? {
    //          result := Merged(mkThreeNode(subresult.tree, tree.pivot,
    //                                        tree.right.left, tree.right.pivot, 
    //                                                                  tree.right.right));
    //      } else {
    //          assert !tree.left.Leaf?;
    //          assert tree.right.ThreeNode?;
    //          var newleft := mkTwoNode(subresult.tree, tree.pivot, tree.right.left);
    //          var newright := mkTwoNode(tree.right.middle, tree.right.pivotb, tree.right.right);
    //          var newtree := mkTwoNode(newleft, tree.right.pivota, newright);
    //          result := DidntMerge(newtree);
    //      }
    //  }
    // }

    // method DeleteFromSubtree<Value>(tree: Node<Value>, key: Keyspace.Element)
    //  returns (result: DeletionResult<Value>)
    //  requires TTSubtree(tree);
    //  ensures ValidDeletionResult(result, tree, key);
    //  decreases tree, 3;
    // {
    //  assume ValidDeletionResult(result, tree, key);
    //  // if tree.Leaf? {
    //  //  result := DeleteFromLeaf(tree, key);
    //  // } else if tree.TwoNode? {
    //  //  result := DeleteFromTwoNode(tree, key);
    //  // } else {
    //  //  result := DeleteFromThreeNode(tree, key);
    //   // }
    // }
    
    datatype Tree<Value> = EmptyTree | NonEmptyTree(root: Node<Value>)
    
    predicate TTTree<Value>(tree: Tree<Value>) {
        tree.EmptyTree? || TTSubtree(tree.root)
    }

    function Contents<Value>(tree: Tree<Value>) : map<Keyspace.Element, Value>
        requires TTTree(tree);
    {
        if tree.EmptyTree?
            then map[]
        else
            SubtreeContents(tree.root)
    }

    function method Query<Value>(tree: Tree<Value>, key: Keyspace.Element) : QueryResult<Value>
        requires(TTTree(tree));
        ensures Query(tree, key) == KeyDoesNotExist <==>
            (key !in Contents(tree));
            ensures Query(tree, key).ValueForKey? <==>
                (key in Contents(tree) && Contents(tree)[key] == Query(tree, key).value);
    {
        if tree.EmptyTree? then
            KeyDoesNotExist
        else
            QuerySubtree(tree.root, key)
    }

    method Insert<Value>(tree: Tree<Value>, key: Keyspace.Element, value: Value) returns (newtree: Tree<Value>)
        requires TTTree(tree);
        ensures TTTree(newtree);
        ensures Contents(newtree) == Contents(tree)[key := value];
        ensures newtree.NonEmptyTree?;
    {
        if tree.EmptyTree? {
            assert TTSubtree(Leaf(key, value));
            newtree := NonEmptyTree(Leaf(key, value));
        } else {
            var result := InsertIntoSubtree(tree.root, key, value);
            newtree := NonEmptyTree(result.tree);
        }
    }

// datatype DeletionResult = DeletionResult(tree: Tree, merged: bool)

// function DeleteFromSubtree(tree: Tree, key: int) : DeletionResult
//  requires TTTree(tree);
//  ensures TTTree(result.tree);
//  ensures Contents(result.tree) == Contents(tree) - {key};
// {
//  if tree.EmptyTree? then
//      DeletionResult(EmptyTree, false)
//  else
//      match tree.root {
//          case Leaf(v) =>
//              if v == key then DeletionResult(EmptyTree, true)
//              else DeletionResult(tree, false)
//          case TwoNode(left, pivot, right) =>
//              if key < pivot then {
//                  var subresult := DeleteFromSubtree(left, key);
//                  if !subresult.merged then
//                      DeletionResult(NonEmptyTree(subresult.root, tree.root.pivot, tree.root.right))
//                  else

//              } else {
//              }
//      }
// }

}

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
    var nInsertions := 1000 * 1000;
    var t := Integer_TTTree.Tree<int>.EmptyTree;
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
