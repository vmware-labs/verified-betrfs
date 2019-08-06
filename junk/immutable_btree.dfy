include "total_order.s.dfy"
//include "lexical.dfy"
include "Maps.s.dfy"
include "mathematics.dfy"
include "sequences.s.dfy"

abstract module ImmutableBTree {
  import Keyspace : Total_Order
  import Maps = Maps
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
  
  lemma TreeAllKeysSeqExistentialForm(trees: seq<Node>, key: Keyspace.Element)
    requires forall i {:trigger WFTree(trees[i]) } :: 0 <= i < |trees| ==> WFTree(trees[i]);
    ensures key in TreeAllKeysSeq(trees) <==>
      (exists i :: 0 <= i < |trees| && key in TreeAllKeys(trees[i]));
  {
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
  
  lemma TreeDefinedKeysSeqExistentialForm(trees: seq<Node>, key: Keyspace.Element)
    requires forall i {:trigger WFTree(trees[i]) } :: 0 <= i < |trees| ==> WFTree(trees[i]);
    ensures key in TreeDefinedKeysSeq(trees) <==>
      (exists i :: 0 <= i < |trees| && key in TreeDefinedKeys(trees[i]));
  {
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
  
  lemma TreeContentsSeqExistentialForm<Value>(trees: seq<Node<Value> >, key: Keyspace.Element)
    requires forall i {:trigger WFTree(trees[i]) } :: 0 <= i < |trees| ==> WFTree(trees[i]);
    ensures key in TreeContentsSeq(trees) ==>
      (exists i :: 0 <= i < |trees|
      && key in TreeContents(trees[i])
      && TreeContentsSeq(trees)[key] == TreeContents(trees[i])[key]);
  {
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

  function method LeftChild(tree: Node, pivot_index: int) : Node
    requires WFTree(tree);
    requires tree.Index?;
    requires 0 <= pivot_index < |tree.pivots|;
  {
    tree.children[pivot_index]
  }
  
  function method RightChild(tree: Node, pivot_index: int) : Node
    requires WFTree(tree);
    requires tree.Index?;
    requires -1 <= pivot_index < |tree.pivots|;
  {
    tree.children[pivot_index+1]
  }
  
  predicate PivotLteNextSubtree(tree: Node, pivot: int)
    requires WFTree(tree);
    requires tree.Index?;
    requires 0 <= pivot < |tree.pivots|;
  {
    Keyspace.SetAllLte({tree.pivots[pivot]}, TreeAllKeys(RightChild(tree, pivot)))
  }

  predicate SubtreeLtNextPivot(tree: Node, pivot: int)
    requires WFTree(tree);
    requires tree.Index?;
    requires 0 <= pivot < |tree.pivots|;
  {
    Keyspace.SetAllLt(TreeAllKeys(LeftChild(tree, pivot)), {tree.pivots[pivot]})
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

  lemma EvaluateIsCorrect(tree: Node, key: Keyspace.Element, pos: int)
    requires WFTree(tree);
    requires TreeIsOrdered(tree);
    requires tree.Index?;
    requires key in TreeContents(tree);
    requires -1 <= pos < |tree.pivots|;
    requires 0 <= pos ==> Keyspace.lte(tree.pivots[pos], key);
    requires pos < |tree.pivots|-1 ==> Keyspace.lt(key, tree.pivots[pos+1]);
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
      val := tree.values[pos];
    } else {
      var pos := Keyspace.FindLargestLTE(tree.pivots, key);
      EvaluateIsCorrect(tree, key, pos); // OBSERVE
      assert SubtreeIsOrdered(tree, pos+1); // TRIGGER
      val := Evaluate(RightChild(tree, pos), key);
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
        assert forall i :: 0 <= i < pos+1 ==> Keyspace.lte(tree.keys[i], key);
        assert forall i :: pos + 1 <= i < |tree.keys| ==> Keyspace.lt(key, tree.keys[i]);
        new_tree := Leaf(tree.keys[..pos+1]   + [key]   + tree.keys[pos+1..],
                        tree.values[..pos+1] + [value] + tree.values[pos+1..]);
          assert WFTree(new_tree); // TRIGGER
      } 
    } else {
      var pos := Keyspace.FindLargestLTE(tree.pivots, key);
      assert SubtreeIsOrdered(tree, pos+1); // TRIGGER
      var new_subtree := Define(tree.children[pos+1], key, value);
      var new_children := tree.children[..pos+1] + [new_subtree] + tree.children[pos+2..];

      ///////////// Le proof for AllKeys //////////////////////////
      forall key' | key' in TreeAllKeysSeq(tree.children) + {key}
        ensures key' in TreeAllKeysSeq(new_children);
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
        ensures key' in TreeAllKeysSeq(tree.children) + {key};
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

      ///////////// Le proof for DefinedKeys //////////////////////////
      forall key' | key' in TreeDefinedKeysSeq(tree.children) + {key}
        ensures key' in TreeDefinedKeysSeq(new_children);
      {
        if key' == key {
          assert key' in TreeDefinedKeys(new_subtree);
          assert key' in TreeDefinedKeys(new_children[pos+1]);
          TreeDefinedKeysSeqExistentialForm(new_children, key');
        } else {
          TreeDefinedKeysSeqExistentialForm(tree.children, key');
          var i :| 0 <= i < |tree.children| && key' in TreeDefinedKeys(tree.children[i]);
          if i < pos + 1 {
            assert key' in TreeDefinedKeys(new_children[i]);
          } else if i == pos + 1 {
            assert key' in TreeDefinedKeys(new_children[i]);
          } else {
            assert key' in TreeDefinedKeys(new_children[i]);
          }
          TreeDefinedKeysSeqExistentialForm(new_children, key');
        }
      }
      assert TreeDefinedKeysSeq(tree.children) <= TreeDefinedKeysSeq(new_children);
      assert key in TreeDefinedKeysSeq(new_children);
      
      forall key' | key' in TreeDefinedKeysSeq(new_children)
        ensures key' in TreeDefinedKeysSeq(tree.children) + {key};
      {
        TreeDefinedKeysSeqExistentialForm(new_children, key');
        var i :| 0 <= i < |new_children| && key' in TreeDefinedKeys(new_children[i]);
        if i < pos + 1 {
          assert key' in TreeDefinedKeys(tree.children[i]);
        } else if i == pos + 1 {
          assert key' in TreeDefinedKeys(tree.children[i]) + {key};
        } else {
          assert key' in TreeDefinedKeys(tree.children[i]);
        }
        TreeDefinedKeysSeqExistentialForm(tree.children, key');
      }
      assert TreeDefinedKeysSeq(tree.children) + {key} >= TreeDefinedKeysSeq(new_children);
      assert TreeDefinedKeysSeq(tree.children) + {key} == TreeDefinedKeysSeq(new_children);

      new_tree := Index(tree.pivots, new_children);

      assert TreeAllKeys(new_tree) == TreeAllKeys(tree) + {key};
      assert TreeDefinedKeys(new_tree) == TreeDefinedKeys(tree) + {key};
      
      forall i | 0 <= i < |new_tree.pivots|
        ensures SubtreeLtNextPivot(new_tree, i);
        ensures PivotLteNextSubtree(new_tree, i);
      {
        if i < pos + 1 {
          assert SubtreeLtNextPivot(tree, i);
          assert PivotLteNextSubtree(tree, i);
        } else if i == pos + 1 {
          assert SubtreeLtNextPivot(tree, i);                
          assert PivotLteNextSubtree(tree, i);
        } else {
          assert SubtreeLtNextPivot(tree, i);
          assert PivotLteNextSubtree(tree, i);
        }
      }
        
      forall i | 0 <= i < |new_tree.children|
        ensures SubtreeIsOrdered(new_tree, i);
      {
        if i < pos + 1 {
          assert SubtreeIsOrdered(tree, i);
        } else if i == pos + 1 {
          assert SubtreeIsOrdered(new_tree, i);
        } else {
          assert SubtreeIsOrdered(tree, i);
        }
      }

      TreeContentsSeqExistentialForm(new_children, key);
      assert key in TreeDefinedKeys(new_tree);
      assert key in TreeContentsSeq(new_children);
      forall i | 0 <= i < |new_children| && i != pos+1
        ensures key !in TreeContents(new_children[i]);
      {
        if i < pos+1 {
          assert SubtreeLtNextPivot(new_tree, i);
          assert Keyspace.lte(new_tree.pivots[i], new_tree.pivots[pos]);
          Keyspace.SetLtLteTransitivity(TreeDefinedKeys(new_children[i]), {new_tree.pivots[pos]}, {key});
        } else {
          assert i > pos + 1;
          assert Keyspace.lte(new_tree.pivots[pos+1], new_tree.pivots[i-1]);
          assert PivotLteNextSubtree(new_tree, i-1);
          Keyspace.SetLtLteTransitivity({key}, {new_tree.pivots[pos+1]}, TreeDefinedKeys(new_children[i]));
        }
      }
      assert forall i :: 0 <= i < |new_children| && i != pos+1 ==> key !in TreeContents(new_children[i]);
      assert TreeContents(new_tree.children[pos+1])[key] == value;
      assert TreeContents(new_tree)[key] == value;
    }
  }
}
