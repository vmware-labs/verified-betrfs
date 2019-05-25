include "total_order.dfy"
//include "lexical.dfy"
include "map_utils.dfy"
include "mathematics.dfy"
include "sequences.dfy"

abstract module ImmutableBTree {
    import Keyspace : Total_Order
    import Maps = Map_Utils
    import Math = Mathematics
    import opened Sequences
    
    function method min_pivots()   : int { 5 }
    function method max_pivots()   : int { 10 }
    function method min_leafsize() : int { 5 }
    function method max_leafsize() : int { 10 }

    datatype Node<Value> =
        Leaf(keys: seq<Keyspace.Element>, values: seq<Value>) |
        Index(pivots: seq<Keyspace.Element>, children: seq<Node>)

    function TreeAllKeysSeq(trees: seq<Node>) : set<Keyspace.Element>
    {
        if |trees| == 0 then {}
        else TreeAllKeys(trees[0]) + TreeAllKeysSeq(trees[1..])
    }
    
    function TreeAllKeys(tree: Node) : set<Keyspace.Element>
    {
        if tree.Leaf? then Set(tree.keys)
        else Set(tree.pivots) + TreeAllKeysSeq(tree.children)
    }

    function TreeDefinedKeysSeq(trees: seq<Node>) : set<Keyspace.Element>
        ensures TreeDefinedKeysSeq(trees) <= TreeAllKeysSeq(trees);
    {
        if |trees| == 0 then {}
        else TreeDefinedKeys(trees[0]) + TreeDefinedKeysSeq(trees[1..])
    }
    
    function TreeDefinedKeys(tree: Node) : set<Keyspace.Element>
        ensures TreeDefinedKeys(tree) <= TreeAllKeys(tree);
    {
        if tree.Leaf? then Set(tree.keys)
        else TreeDefinedKeysSeq(tree.children)
    }

    predicate WFTree(tree: Node) {
        if tree.Leaf? then
            && |tree.keys| > 0
            && |tree.keys| == |tree.values|
        else
            && |tree.pivots| > 0
            && |tree.children| == |tree.pivots| + 1
            && (forall i {:trigger WFTree(tree.children[i]) } :: 0 <= i <|tree.children| ==> WFTree(tree.children[i]))
    }

    predicate WFRoot(tree: Node) {
        tree.Leaf? || WFTree(tree)
    }
    
    function TreeContentsSeq<Value>(trees: seq<Node<Value>>) : map<Keyspace.Element, Value>
        requires forall i {:trigger WFTree(trees[i]) } :: 0 <= i < |trees| ==> WFTree(trees[i]);
        ensures TreeContentsSeq(trees).Keys == TreeDefinedKeysSeq(trees);
    {
        if |trees| == 0 then map[]
        else Maps.union(TreeContents(trees[0]), TreeContentsSeq(trees[1..]))
    }
    
    function TreeContents<Value>(tree: Node<Value>) : map<Keyspace.Element, Value>
        requires WFTree(tree);
        ensures TreeContents(tree).Keys == TreeDefinedKeys(tree);
    {
        if tree.Leaf? then
            map x : Keyspace.Element | x in tree.keys :: tree.values[IndexOf(tree.keys, x)]
        else
            TreeContentsSeq(tree.children)
    }

    predicate SubtreeLtNextPivot(tree: Node, child: int)
        requires WFTree(tree);
        requires tree.Index?;
        requires 0 <= child < |tree.pivots|;
    {
        Keyspace.SetAllLt(TreeAllKeys(tree.children[child]), {tree.pivots[child]})
    }
    
    predicate PivotLteNextSubtree(tree: Node, pivot: int)
        requires WFTree(tree);
        requires tree.Index?;
        requires 0 <= pivot < |tree.pivots|;
    {
        Keyspace.SetAllLte({tree.pivots[pivot]}, TreeAllKeys(tree.children[pivot+1]))
    }

    predicate SubtreeIsOrdered(tree: Node, child: int)
        requires WFTree(tree);
        requires tree.Index?;
        requires 0 <= child < |tree.children|;
    {
        TreeIsOrdered(tree.children[child])
    }
    
    predicate TreeIsOrdered(tree: Node)
        requires WFTree(tree);
    {
        if tree.Leaf? then
            && Keyspace.IsSorted(tree.keys)
            && NoDupes(tree.keys)
        else
            && Keyspace.IsSorted(tree.pivots)
            && NoDupes(tree.pivots)
            && (forall i :: 0 <= i < |tree.pivots|   ==> SubtreeLtNextPivot(tree, i))
            && (forall i :: 0 <= i < |tree.pivots|   ==> PivotLteNextSubtree(tree, i))
            && (forall i :: 0 <= i < |tree.children| ==> SubtreeIsOrdered(tree, i))
    }

    lemma TreeContentsSeqExistentialForm(trees: seq<Node>, key: Keyspace.Element)
        requires forall i {:trigger WFTree(trees[i]) } :: 0 <= i < |trees| ==> WFTree(trees[i]);
        requires key in TreeContentsSeq(trees);
        ensures exists i :: 0 <= i < |trees| && key in TreeContents(trees[i]) && TreeContentsSeq(trees)[key] == TreeContents(trees[i])[key];
    {
    }

    lemma TreeAllKeysSeqExistentialForm(trees: seq<Node>, key: Keyspace.Element)
        requires forall i {:trigger WFTree(trees[i]) } :: 0 <= i < |trees| ==> WFTree(trees[i]);
        ensures key in TreeAllKeysSeq(trees) <==>
            (exists i :: 0 <= i < |trees| && key in TreeAllKeys(trees[i]));
    {
    }

    lemma EvaluateIsCorrect(tree: Node, key: Keyspace.Element, pos: int)
        requires WFTree(tree);
        requires TreeIsOrdered(tree);
        requires tree.Index?;
        requires key in TreeContents(tree);
        requires -1 <= pos < |tree.pivots|;
        requires forall i :: 0 <= i <= pos ==> Keyspace.lte(tree.pivots[i], key);
        requires forall i :: pos < i < |tree.pivots| ==> Keyspace.lt(key, tree.pivots[i]);
        ensures key in TreeContents(tree.children[pos+1]);
        ensures TreeContents(tree)[key] == TreeContents(tree.children[pos+1])[key];
    {
        forall i | 0 <= i < |tree.children| && i != pos+1
            ensures key !in TreeAllKeys(tree.children[i]);
        {
            if i <= pos {
                assert SubtreeLtNextPivot(tree, i); // TRIGGER
            } else {
                assert PivotLteNextSubtree(tree, i-1); // TRIGGER
            }
        }
        TreeContentsSeqExistentialForm(tree.children, key); // OBSERVE
    }

    method Evaluate<Value>(tree: Node<Value>, key: Keyspace.Element) returns (val: Value)
        requires WFTree(tree);
        requires TreeIsOrdered(tree);
        requires key in TreeContents(tree);
        ensures val == TreeContents(tree)[key];
    {
        if tree.Leaf? {
            var pos := Keyspace.FindLargestLTE(tree.keys, key);
            assert key == tree.keys[pos]; // OBSERVE
            val := tree.values[pos];
        } else {
            var pos := Keyspace.FindLargestLTE(tree.pivots, key);
            EvaluateIsCorrect(tree, key, pos); // OBSERVE
            assert SubtreeIsOrdered(tree, pos+1); // TRIGGER
            val := Evaluate(tree.children[pos+1], key);
        }
    }

    function method Split(node: Node) : (Node, Keyspace.Element, Node)
        requires WFTree(node);
        requires node.Leaf? ==> |node.keys| >= 2;
        requires node.Index? ==> |node.pivots| >= 3;
        ensures WFTree(Split(node).0);
        ensures WFTree(Split(node).2);
    {
        if node.Leaf? then
            var half := |node.keys| / 2;
            (Leaf(node.keys[..half], node.values[..half]),
             node.keys[half],
             Leaf(node.keys[half..], node.values[half..]))
        else
            var half := (|node.pivots|) / 2;
            var new_left := Index(node.pivots[..half], node.children[..half+1]);
            var new_right := Index(node.pivots[half+1..], node.children[half+1..]);
            (new_left, node.pivots[half], new_right)
    }

    function method NeedsSplit(node: Node) : bool
        requires WFTree(node);
    {
        || (node.Leaf? && |node.keys| > max_leafsize())
        || (node.Index? && |node.pivots| > max_pivots())
    }
    
    method Define<Value>(tree: Node<Value>, key: Keyspace.Element, value: Value) returns (new_tree: Node<Value>)
        requires WFTree(tree);
        requires TreeIsOrdered(tree);
        ensures WFTree(new_tree);
        ensures TreeAllKeys(new_tree) == TreeAllKeys(tree) + {key};
        ensures TreeIsOrdered(new_tree);
        ensures TreeContents(new_tree) == TreeContents(tree)[key := value];
    {
        if tree.Leaf? {
            var pos := Keyspace.FindLargestLTE(tree.keys, key);
            if pos >= 0 && tree.keys[pos] == key {
                new_tree := Leaf(tree.keys, tree.values[pos := value]);
            } else {
                new_tree := Leaf(tree.keys[..pos+1]   + [key]   + tree.keys[pos+1..],
                                tree.values[..pos+1] + [value] + tree.values[pos+1..]);
                assert WFTree(new_tree); // TRIGGER
            } 
        } else {
            var pos := Keyspace.FindLargestLTE(tree.pivots, key);
            assert SubtreeIsOrdered(tree, pos+1); // TRIGGER
            var new_subtree := Define(tree.children[pos+1], key, value);
            var new_children := tree.children[..pos+1] + [new_subtree] + tree.children[pos+2..];

            forall key' | key' in TreeAllKeysSeq(tree.children) + {key}
              ensures key' in TreeAllKeysSeq(new_children)
            {
              if key' == key {
                assert key' in TreeAllKeys(new_subtree);
                assert key' in TreeAllKeys(new_children[pos+1]);
                TreeAllKeysSeqExistentialForm(new_children, key');
              } else {
                TreeAllKeysSeqExistentialForm(tree.children, key');
                var i :| 0 <= i < |tree.children| && key' in TreeAllKeys(tree.children[i]);
                if i < pos + 1 {
                  assert key' in TreeAllKeys(new_children[i]);
                } else if i == pos + 1 {
                  assert key' in TreeAllKeys(new_children[i]);
                } else {
                  assert key' in TreeAllKeys(new_children[i]);
                }
                TreeAllKeysSeqExistentialForm(new_children, key');
              }
            }
            assert TreeAllKeysSeq(tree.children) <= TreeAllKeysSeq(new_children);
            assert key in TreeAllKeysSeq(new_children);
            
            forall key' | key' in TreeAllKeysSeq(new_children)
              ensures key' in TreeAllKeysSeq(tree.children) + {key}
            {
              TreeAllKeysSeqExistentialForm(new_children, key');
              var i :| 0 <= i < |new_children| && key' in TreeAllKeys(new_children[i]);
              if i < pos + 1 {
                assert key' in TreeAllKeys(tree.children[i]);
              } else if i == pos + 1 {
                assert key' in TreeAllKeys(tree.children[i]) + {key};
              } else {
                assert key' in TreeAllKeys(tree.children[i]);
              }
              TreeAllKeysSeqExistentialForm(tree.children, key');
            }
            assert TreeAllKeysSeq(tree.children) + {key} >= TreeAllKeysSeq(new_children);
            assert TreeAllKeysSeq(tree.children) + {key} == TreeAllKeysSeq(new_children);

            new_tree := Index(tree.pivots, new_children);
            
            // if NeedsSplit(new_subtree) {
            //     var (new_left, new_pivot, new_right) := Split(new_subtree);
            //     assert new_pivot in TreeAllKeys(tree.children[pos+1]);
            //     new_tree := Index(tree.pivots[..pos+1] + [new_pivot] + tree.pivots[pos+1..],
            //                      tree.children[..pos+1] + [new_left, new_right] + tree.children[pos+2..]);
            // } else {
            // forall key' | key' in TreeAllKeys(new_tree)
            //     ensures key' in TreeAllKeys(tree) || key' == key;
            // {
            //     TreeAllKeysSeqExistentialForm(new_tree.children, key');
            // }
            // assert key in TreeAllKeysSeq(new_tree.children);
            // assert key in TreeAllKeys(new_tree);
            // }
        }
    }
}
