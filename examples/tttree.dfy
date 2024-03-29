// Copyright 2018-2021 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, and University of Washington
// SPDX-License-Identifier: BSD-2-Clause

include "../lib/total_order.s.dfy"
include "../lib/lexical.i.dfy"
include "../lib/Maps.i.dfy"
include "../lib/mathematics.i.dfy"

abstract module TwoThreeTree {
    import Keyspace : Total_Order
    import Maps = Maps
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
            Maps.MapDisjointUnion(SubtreeContents(tree.left), SubtreeContents(tree.right))
        else
            reveal_TreeIsOrdered();
            assert SubtreeContents(tree.left).Keys
                !! SubtreeContents(tree.middle).Keys
                !! SubtreeContents(tree.right).Keys; // observe
            Maps.MapDisjointUnion3(SubtreeContents(tree.left),
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

    function method MinKVPair<Value>(tree: Node<Value>) : (Keyspace.Element, Value)
        requires TreeIsOrdered(tree);
        ensures MinKVPair(tree).0 in SubtreeContents(tree).Keys;
        ensures MinKVPair(tree).1 == SubtreeContents(tree)[MinKVPair(tree).0];
        ensures forall x :: x in SubtreeAllKeys(tree) ==> Keyspace.lte(MinKVPair(tree).0, x);
    {
        reveal_TreeIsOrdered();
        if tree.Leaf? then (tree.key, tree.value)
        else MinKVPair(tree.left)
    }
    
    function {:opaque} minHeight(tree: Node) : int
        ensures minHeight(tree) >= 0;
        ensures tree.Leaf? <==> minHeight(tree) == 0;
    {
        if tree.Leaf?
            then 0
        else if tree.TwoNode?
            then 1 + Math.min(minHeight(tree.left), minHeight(tree.right))
        else 
            1 + Math.min(minHeight(tree.left), Math.min(minHeight(tree.middle), minHeight(tree.right)))
    }

    function {:opaque} maxHeight(tree: Node) : int
        ensures maxHeight(tree) >= 0;
        ensures tree.Leaf? <==> maxHeight(tree) == 0;
    {
        if tree.Leaf?
            then 0
        else if tree.TwoNode?
            then 1 + Math.max(maxHeight(tree.left), maxHeight(tree.right))
        else
            1 + Math.max(maxHeight(tree.left), Math.max(maxHeight(tree.middle), maxHeight(tree.right)))
    }

    lemma minHeightLTEmaxHeight(tree: Node)
        ensures minHeight(tree) <= maxHeight(tree);
    {
        reveal_minHeight();
        reveal_maxHeight();
    }
    
    predicate balanced(tree: Node) {
        minHeight(tree) == maxHeight(tree)
    }

    lemma childrenAreBalanced(tree: Node)
        requires balanced(tree);
        ensures !tree.Leaf? ==> balanced(tree.left);
        ensures !tree.Leaf? ==> balanced(tree.right);
        ensures tree.ThreeNode? ==> balanced(tree.middle);
        ensures !tree.Leaf? ==> minHeight(tree.left) == minHeight(tree) - 1;
        ensures !tree.Leaf? ==> minHeight(tree.right) == minHeight(tree) - 1;
        ensures tree.ThreeNode? ==> minHeight(tree.middle) == minHeight(tree) - 1;
    {
        reveal_minHeight();
        reveal_maxHeight();
        if !tree.Leaf? {
            minHeightLTEmaxHeight(tree.left);
            minHeightLTEmaxHeight(tree.right);
        }
        if tree.ThreeNode? {
            minHeightLTEmaxHeight(tree.middle);
        }
    }    
    
    predicate TTSubtree(tree: Node) {
        TreeIsOrdered(tree)
      && balanced(tree)
    }

    lemma childrenAreSubtrees<Value>(tree: Node<Value>)
        requires TTSubtree(tree);
        ensures !tree.Leaf? ==> TTSubtree(tree.left);
        ensures !tree.Leaf? ==> TTSubtree(tree.right);
        ensures tree.ThreeNode? ==> TTSubtree(tree.middle);
    {
        childrenAreBalanced(tree);
        reveal_TreeIsOrdered();
    }

    function method Height(tree: Node) : int
        requires balanced(tree);
        ensures Height(tree) == minHeight(tree);
    {
        childrenAreBalanced(tree);
        if tree.Leaf? then 0
        else 1 + Height(tree.left)
    }

    function method mkTwoNode(t1: Node, pivot: Keyspace.Element, t2: Node) : Node
        requires TTSubtree(t1);
        requires TTSubtree(t2);
        requires Height(t1) == Height(t2);
        requires ContentsAreLessThan(t1, pivot);
        requires ContentsAreGreaterEqualThan(pivot, t2);
        requires SubtreeContents(t1).Keys
               !! SubtreeContents(t2).Keys; // Should be implied, but dafny can't always see it
        ensures TTSubtree(mkTwoNode(t1, pivot, t2));
        ensures SubtreeAllKeys(mkTwoNode(t1, pivot, t2))
             == SubtreeAllKeys(t1) + { pivot } + SubtreeAllKeys(t2);
        ensures SubtreeContents(mkTwoNode(t1, pivot, t2)) ==
            Maps.MapDisjointUnion(SubtreeContents(t1), SubtreeContents(t2));
        ensures Height(mkTwoNode(t1, pivot, t2)) == Height(t1) + 1;
    {
        reveal_minHeight();
        reveal_maxHeight();
        reveal_TreeIsOrdered();
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
            Maps.MapDisjointUnion3(SubtreeContents(t1), SubtreeContents(t2), SubtreeContents(t3));
        ensures Height(mkThreeNode(t1, pivota, t2, pivotb, t3)) == Height(t1) + 1;
    {
        reveal_TreeIsOrdered();
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
        reveal_TreeIsOrdered();
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
        childrenAreBalanced(tree);
        var subresult := InsertIntoSubtree(tree.left, key, value);
        if !subresult.Split? {
            result := DidntSplit(mkTwoNode(subresult.tree, tree.pivot, tree.right));
        } else {
            childrenAreSubtrees(subresult.tree);
            childrenAreBalanced(subresult.tree);
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
        childrenAreBalanced(tree);
        var subresult := InsertIntoSubtree(tree.right, key, value);
        if !subresult.Split? {
            result := DidntSplit(mkTwoNode(tree.left, tree.pivot, subresult.tree));
        } else {
            childrenAreSubtrees(subresult.tree);
            childrenAreBalanced(subresult.tree);
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
        childrenAreBalanced(tree);
        var subresult := InsertIntoSubtree(tree.left, key, value);
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
        childrenAreBalanced(tree);
        var subresult := InsertIntoSubtree(tree.middle, key, value);
        if !subresult.Split? {
            result := DidntSplit(mkThreeNode(tree.left, tree.pivota,
                                          subresult.tree, tree.pivotb,
                                                    tree.right));
        } else {
            childrenAreSubtrees(subresult.tree);
            childrenAreBalanced(subresult.tree);
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
        childrenAreBalanced(tree);
        var subresult := InsertIntoSubtree(tree.right, key, value);
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
    
    
    datatype DeletionResult<Value> =
     NothingLeft |
     Merged(tree: Node<Value>) |
     DidntMerge(tree: Node<Value>)

    predicate ValidDeletionResult<Value>(result: DeletionResult<Value>, tree: Node<Value>,
     key: Keyspace.Element)
     requires TTSubtree(tree);
    {
     if result.NothingLeft? then
         tree.Leaf? && tree.key == key
     else 
      TTSubtree(result.tree) &&
      (SubtreeAllKeys(result.tree) <= SubtreeAllKeys(tree)) &&
      (SubtreeContents(result.tree).Keys == SubtreeContents(tree).Keys - {key}) && 
      (forall x :: x in SubtreeContents(result.tree) ==>
      SubtreeContents(result.tree)[x] == SubtreeContents(tree)[x]) &&
      (result.Merged? ==> !tree.Leaf?) &&
      (result.Merged? ==> Height(result.tree) == Height(tree) - 1) &&
      (!result.Merged? ==> Height(result.tree) == Height(tree))
    }
        
    method DeleteFromLeaf<Value>(tree: Node<Value>, key: Keyspace.Element)
     returns (result: DeletionResult<Value>)
     requires TTSubtree(tree);
     requires tree.Leaf?;
     ensures ValidDeletionResult(result, tree, key);
    {
     if tree.key == key {
         result := NothingLeft;
     } else {
         result := DidntMerge(tree);
     }
    }

    method DeleteFromTwoNodeLeft<Value>(tree: Node<Value>, key: Keyspace.Element)
     returns (result: DeletionResult<Value>)
     requires TTSubtree(tree);
     requires tree.TwoNode?;
     requires Keyspace.lt(key, tree.pivot);
     ensures ValidDeletionResult(result, tree, key);
     decreases tree, 0;
    {
        childrenAreSubtrees(tree);
        childrenAreBalanced(tree);
        var subresult := DeleteFromSubtree(tree.left, key);
        if subresult.NothingLeft? {
            result := Merged(tree.right);
        } else if subresult.DidntMerge? {
            result := DidntMerge(mkTwoNode(subresult.tree, tree.pivot, tree.right));
        } else {
            if tree.right.TwoNode? {
                childrenAreSubtrees(tree.right);
                childrenAreBalanced(tree.right);
                result := Merged(mkThreeNode(subresult.tree, tree.pivot,
                                            tree.right.left, tree.right.pivot, 
                                            tree.right.right));
            } else {
                childrenAreSubtrees(tree.right);
                childrenAreBalanced(tree.right);
                var newleft := mkTwoNode(subresult.tree, tree.pivot, tree.right.left);
                var newright := mkTwoNode(tree.right.middle, tree.right.pivotb, tree.right.right);
                var newtree := mkTwoNode(newleft, tree.right.pivota, newright);
                result := DidntMerge(newtree);
            }
        }
    }

    method DeleteFromTwoNodeRight<Value>(tree: Node<Value>, key: Keyspace.Element)
     returns (result: DeletionResult<Value>)
     requires TTSubtree(tree);
     requires tree.TwoNode?;
     requires Keyspace.lte(tree.pivot, key);
     ensures ValidDeletionResult(result, tree, key);
     decreases tree, 0;
    {
        childrenAreSubtrees(tree);
        childrenAreBalanced(tree);
        var subresult := DeleteFromSubtree(tree.right, key);
        if subresult.NothingLeft? {
            result := Merged(tree.left);
        } else if subresult.DidntMerge? {
            result := DidntMerge(mkTwoNode(tree.left, tree.pivot, subresult.tree));
        } else {
            if tree.left.TwoNode? {
                childrenAreSubtrees(tree.left);
                childrenAreBalanced(tree.left);
                result := Merged(mkThreeNode(tree.left.left, tree.left.pivot,
                                            tree.left.right, tree.pivot, 
                                            subresult.tree));
            } else {
                childrenAreSubtrees(tree.left);
                childrenAreBalanced(tree.left);
                var newleft := mkTwoNode(tree.left.left, tree.left.pivota, tree.left.middle);
                var newright := mkTwoNode(tree.left.right, tree.pivot, subresult.tree);
                var newtree := mkTwoNode(newleft, tree.left.pivotb, newright);
                result := DidntMerge(newtree);
            }
        }
    }

    method DeleteFromTwoNode<Value>(tree: Node<Value>, key: Keyspace.Element)
     returns (result: DeletionResult<Value>)
     requires TTSubtree(tree);
     requires tree.TwoNode?;
     ensures ValidDeletionResult(result, tree, key);
     decreases tree, 1;
    {
        if Keyspace.lt(key, tree.pivot) {
            result := DeleteFromTwoNodeLeft(tree, key);
        } else {
            result := DeleteFromTwoNodeRight(tree, key);
        }
    }

    method DeleteFromThreeNodeLeft<Value>(tree: Node<Value>, key: Keyspace.Element)
     returns (result: DeletionResult<Value>)
     requires TTSubtree(tree);
     requires tree.ThreeNode?;
     requires Keyspace.lt(key, tree.pivota);
     ensures ValidDeletionResult(result, tree, key);
     decreases tree, 0;
    {
        childrenAreSubtrees(tree);
        childrenAreBalanced(tree);
        var subresult := DeleteFromSubtree(tree.left, key);
        if subresult.NothingLeft? {
            result := DidntMerge(mkTwoNode(tree.middle, tree.pivotb, tree.right));
        } else if subresult.DidntMerge? {
            result := DidntMerge(mkThreeNode(subresult.tree, tree.pivota,
                                            tree.middle, tree.pivotb, 
                                            tree.right));
        } else {
            childrenAreSubtrees(tree.middle);
            childrenAreBalanced(tree.middle);
            if tree.middle.TwoNode? {
                var newleft := mkThreeNode(subresult.tree, tree.pivota,
                                          tree.middle.left, tree.middle.pivot,
                                          tree.middle.right);
                result := DidntMerge(mkTwoNode(newleft, tree.pivotb, tree.right));
            } else {
                var newleft := mkTwoNode(subresult.tree, tree.pivota, tree.middle.left);
                var newmiddle := mkTwoNode(tree.middle.middle, tree.middle.pivotb, tree.middle.right);
                var newtree := mkThreeNode(newleft, tree.middle.pivota, newmiddle, tree.pivotb, tree.right);
                result := DidntMerge(newtree);
            }
        }
    }

    method DeleteFromThreeNodeMiddle<Value>(tree: Node<Value>, key: Keyspace.Element)
     returns (result: DeletionResult<Value>)
     requires TTSubtree(tree);
     requires tree.ThreeNode?;
     requires Keyspace.lte(tree.pivota, key);
     requires Keyspace.lt(key, tree.pivotb);
     ensures ValidDeletionResult(result, tree, key);
     decreases tree, 0;
    {
        childrenAreSubtrees(tree);
        childrenAreBalanced(tree);
        var subresult := DeleteFromSubtree(tree.middle, key);
        if subresult.NothingLeft? {
            result := DidntMerge(mkTwoNode(tree.left, tree.pivotb, tree.right));
        } else if subresult.DidntMerge? {
            result := DidntMerge(mkThreeNode(tree.left, tree.pivota,
                                            subresult.tree, tree.pivotb, 
                                            tree.right));
        } else {
            childrenAreSubtrees(tree.left);
            childrenAreBalanced(tree.left);
            if tree.left.TwoNode? {
                var newleft := mkThreeNode(tree.left.left, tree.left.pivot,
                                          tree.left.right, tree.pivota,
                                          subresult.tree);
                result := DidntMerge(mkTwoNode(newleft, tree.pivotb, tree.right));
            } else {
                var newleft := mkTwoNode(tree.left.left, tree.left.pivota, tree.left.middle);
                var newmiddle := mkTwoNode(tree.left.right, tree.pivota, subresult.tree);
                var newtree := mkThreeNode(newleft, tree.left.pivotb, newmiddle, tree.pivotb, tree.right);
                result := DidntMerge(newtree);
            }
        }
    }

    method DeleteFromThreeNodeRight<Value>(tree: Node<Value>, key: Keyspace.Element)
     returns (result: DeletionResult<Value>)
     requires TTSubtree(tree);
     requires tree.ThreeNode?;
     requires Keyspace.lte(tree.pivotb, key);
     ensures ValidDeletionResult(result, tree, key);
     decreases tree, 0;
    {
        childrenAreSubtrees(tree);
        childrenAreBalanced(tree);
        var subresult := DeleteFromSubtree(tree.right, key);
        if subresult.NothingLeft? {
            result := DidntMerge(mkTwoNode(tree.left, tree.pivota, tree.middle));
        } else if subresult.DidntMerge? {
            result := DidntMerge(mkThreeNode(tree.left, tree.pivota,
                                            tree.middle, tree.pivotb, 
                                            subresult.tree));
        } else {
            childrenAreSubtrees(tree.middle);
            childrenAreBalanced(tree.middle);
            if tree.middle.TwoNode? {
                var newright := mkThreeNode(tree.middle.left, tree.middle.pivot,
                                          tree.middle.right, tree.pivotb,
                                          subresult.tree);
                result := DidntMerge(mkTwoNode(tree.left, tree.pivota, newright));
            } else {
                var newmiddle := mkTwoNode(tree.middle.left, tree.middle.pivota, tree.middle.middle);
                var newright := mkTwoNode(tree.middle.right, tree.pivotb, subresult.tree);
                var newtree := mkThreeNode(tree.left, tree.pivota, newmiddle, tree.middle.pivotb, newright);
                result := DidntMerge(newtree);
            }
        }
    }

    method DeleteFromThreeNode<Value>(tree: Node<Value>, key: Keyspace.Element)
     returns (result: DeletionResult<Value>)
     requires TTSubtree(tree);
     requires tree.ThreeNode?;
     ensures ValidDeletionResult(result, tree, key);
     decreases tree, 1;
    {
        if Keyspace.lt(key, tree.pivota) {
            result := DeleteFromThreeNodeLeft(tree, key);
        } else if Keyspace.lt(key, tree.pivotb) {
            result := DeleteFromThreeNodeMiddle(tree, key);
        } else {
            result := DeleteFromThreeNodeRight(tree, key);
        }
    }
    
    method DeleteFromSubtree<Value>(tree: Node<Value>, key: Keyspace.Element)
     returns (result: DeletionResult<Value>)
     requires TTSubtree(tree);
     ensures ValidDeletionResult(result, tree, key);
     decreases tree, 3;
    {
        if tree.Leaf? {
            result := DeleteFromLeaf(tree, key);
        } else if tree.TwoNode? {
            result := DeleteFromTwoNode(tree, key);
        } else {
            result := DeleteFromThreeNode(tree, key);
        }
    }

    // predicate ValidConcatenationResult<Value>(result: InsertionResult<Value>,
    //                                           root1: Node<Value>, 
    //                                           root2: Node<Value>)
    //     requires TTSubtree(root1);
    //     requires TTSubtree(root2);
    //     requires forall x, y :: x in SubtreeAllKeys(root1) && y in SubtreeAllKeys(root2) ==> Keyspace.lt(x, y);
    // {
    //       TTSubtree(result.tree)
    //     && SubtreeAllKeys(result.tree) == SubtreeAllKeys(root1) + SubtreeAllKeys(root2)
    //     && SubtreeContents(result.tree) ==
    //       Maps.MapDisjointUnion(SubtreeContents(root1), SubtreeContents(root2))
    //     && (result.Split? ==> result.tree.TwoNode?)
    //     && (result.Split? ==> Height(result.tree) == Math.max(Height(root1), Height(root2)) + 1)
    //     && (result.DidntSplit? ==> Height(result.tree) == Math.max(Height(root1), Height(root2)))
    // }
    
    // method ConcatenateSubtrees<Value>(root1: Node<Value>, root2: Node<Value>)
    //     returns (result: InsertionResult<Value>)
    //     requires TTSubtree(root1);
    //     requires TTSubtree(root2);
    //     requires forall x, y :: ((x in SubtreeAllKeys(root1)) && (y in SubtreeAllKeys(root2))) ==> Keyspace.lt(x, y);
    //     ensures ValidConcatenationResult(result, root1, root2);
    // {
    //     childrenAreSubtrees(root1);
    //     childrenAreBalanced(root1);
    //     childrenAreSubtrees(root2);
    //     childrenAreBalanced(root2);
    //     if Height(root1) == Height(root2) {
    //         result := Split(mkTwoNode(root1, MinKVPair(root2).0, root2));
    //     } else if Height(root1) > Height(root2) {
    //         var subresult := ConcatenateSubtrees(root1.right, root2);
    //         if subresult.DidntSplit? {
    //             if root1.TwoNode? {
    //                 result := DidntSplit(mkTwoNode(root1.left, root1.pivot, subresult.tree));
    //             } else {
    //                 result := DidntSplit(mkThreeNode(root1.left, root1.pivota,
    //                                                 root1.middle, root1.pivotb, 
    //                                                 subresult.tree));
    //             }
    //         } else {
    //             if root1.TwoNode? {
    //                 childrenAreSubtrees(subresult.tree);
    //                 childrenAreBalanced(subresult.tree);
    //                 result := DidntSplit(mkThreeNode(root1.left, root1.pivot,
    //                                                 subresult.tree.left, subresult.tree.pivot,
    //                                                 subresult.tree.right));
    //             } else {
    //                 var newleft := mkTwoNode(root1.left, root1.pivota, root1.middle);
    //                 var newtree := mkTwoNode(newleft, root1.pivotb, subresult.tree);
    //                 result := Split(newtree);
    //             }
    //         }
    //     } else {
    //         var subresult := ConcatenateSubtrees(root1, root2.left);
    //         if subresult.DidntSplit? {
    //             if root2.TwoNode? {
    //                 result := DidntSplit(mkTwoNode(subresult.tree, root2.pivot, root2.right));
    //             } else {
    //                 result := DidntSplit(mkThreeNode(subresult.tree, root2.pivota,
    //                                                 root2.middle, root2.pivotb,
    //                                                 root2.right));
    //             }
    //         } else {
    //             if root2.TwoNode? {
    //                 childrenAreSubtrees(subresult.tree);
    //                 childrenAreBalanced(subresult.tree);
    //                 result := DidntSplit(mkThreeNode(subresult.tree.left, subresult.tree.pivot,
    //                                                 subresult.tree.right, root2.pivot,
    //                                                 root2.right));
    //             } else {
    //                 var newright := mkTwoNode(root2.middle, root2.pivotb, root2.right);
    //                 var newtree := mkTwoNode(subresult.tree, root2.pivota, newright);
    //                 result := Split(newtree);
    //             }
    //         }
    //     }
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
            newtree := NonEmptyTree(Leaf(key, value));
        } else {
            var result := InsertIntoSubtree(tree.root, key, value);
            newtree := NonEmptyTree(result.tree);
        }
    }

    method Delete<Value>(tree: Tree<Value>, key: Keyspace.Element) returns (newtree: Tree<Value>)
        requires TTTree(tree);
        ensures TTTree(newtree);
        ensures Contents(newtree).Keys == Contents(tree).Keys - {key};
        ensures forall k :: k in Contents(newtree).Keys ==> Contents(newtree)[k] == Contents(tree)[k];
    {
        if tree.EmptyTree? {
            newtree := EmptyTree;
        } else {
            var result := DeleteFromSubtree(tree.root, key);
            if result.NothingLeft? {
                newtree := EmptyTree;
            } else {
                newtree := NonEmptyTree(result.tree);
            }
        }
    }
}

// Local Variables:
// tab-width: 4
// End:
