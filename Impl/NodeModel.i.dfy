include "StateModel.i.dfy"

module NodeModel { 
  import opened Options
  import opened Sequences

  import opened KeyType
  import opened ValueMessage
  import opened BucketsLib
  import opened BucketWeights

  import opened StateModel
  import opened Bounds

  // TODO I think we can actually get rid of most of this.
  // StateModel Node and PivotBetree Node could just be replaced
  // with one type and we wouldn't need this conversion layer.

  function {:opaque} SplitParent(fused_parent: Node, pivot: Key, slot: int, left_childref: BT.G.Reference, right_childref: BT.G.Reference)
  : (res : Node)
  requires WFNode(fused_parent)
  requires 0 <= slot < |fused_parent.buckets|
  requires fused_parent.children.Some?
  {
    var pivots := Sequences.insert(fused_parent.pivotTable, pivot, slot);
    var buckets := SplitBucketInList(fused_parent.buckets, slot, pivot);
    Node(
      pivots,
      Some(replace1with2(fused_parent.children.value, left_childref, right_childref, slot)),
      buckets
    )
  }

  lemma SplitParentCorrect(parentref: BT.G.Reference, fused_parent: Node, pivot: Key, slot: int, left_childref: BT.G.Reference, right_childref: BT.G.Reference)
  requires WFNode(fused_parent)
  requires BT.WFNode(INode(fused_parent))
  requires 0 <= slot < |fused_parent.buckets|
  requires PivotsLib.PivotInsertable(fused_parent.pivotTable, slot, pivot)
  requires |fused_parent.buckets| <= MaxNumChildren() - 1
  requires fused_parent.children.Some?
  ensures
    && var res := SplitParent(fused_parent, pivot, slot, left_childref, right_childref);
    && WFNode(res)
    && var inode := INode(fused_parent);
    && var inode' := INode(res);
    && inode' == BT.SplitParent(inode, pivot, slot, left_childref, right_childref)
    && WeightBucketList(res.buckets) <= WeightBucketList(fused_parent.buckets)
  {
    reveal_SplitParent();
    var res := SplitParent(fused_parent, pivot, slot, left_childref, right_childref);
    WFSplitBucketInList(fused_parent.buckets, slot, pivot, fused_parent.pivotTable);
    WeightSplitBucketInListLe(fused_parent.buckets, slot, pivot);
    assert WFNode(res);
    assert INode(res) == BT.SplitParent(INode(fused_parent), pivot, slot, left_childref, right_childref);
  }


  function {:opaque} CutoffNodeAndKeepLeft(node: Node, pivot: Key) : (node': Node)
  requires WFNode(node)
  ensures |node'.buckets| == |node'.pivotTable| + 1
  ensures node'.children.Some? ==> |node'.buckets| == |node'.children.value|
  {
    var cLeft := Pivots.CutoffForLeft(node.pivotTable, pivot);
    var leftPivots := node.pivotTable[.. cLeft];
    var leftChildren := if node.children.Some? then Some(node.children.value[.. cLeft + 1]) else None;
    var splitBucket := SplitBucketLeft(node.buckets[cLeft], pivot);
    var leftBuckets := node.buckets[.. cLeft] + [splitBucket];
    Node(leftPivots, leftChildren, leftBuckets)
  }

  lemma CutoffNodeAndKeepLeftCorrect(node: Node, pivot: Key)
  requires WFNode(node)
  requires BT.WFNode(INode(node))
  ensures var node' := CutoffNodeAndKeepLeft(node, pivot);
    && WFNode(node')
    && INode(node') == BT.CutoffNodeAndKeepLeft(INode(node), pivot)
  {
    reveal_CutoffNodeAndKeepLeft();
    BT.reveal_CutoffNodeAndKeepLeft();
    var cLeft := Pivots.CutoffForLeft(node.pivotTable, pivot);
    var leftPivots := node.pivotTable[.. cLeft];
    var leftChildren := if node.children.Some? then Some(node.children.value[.. cLeft + 1]) else None;
    var splitBucket := SplitBucketLeft(node.buckets[cLeft], pivot);
    var leftBuckets := node.buckets[.. cLeft] + [splitBucket];
    Pivots.WFSlice(node.pivotTable, 0, cLeft);
    WFSplitBucketListLeft(node.buckets, node.pivotTable, cLeft, pivot);
    WeightSplitBucketListLeft(node.buckets, node.pivotTable, cLeft, pivot);
  }

  function {:opaque} CutoffNodeAndKeepRight(node: Node, pivot: Key)
  : (node': Node)
  requires WFNode(node)
  ensures |node'.buckets| == |node'.pivotTable| + 1
  ensures node'.children.Some? ==> |node'.buckets| == |node'.children.value|
  {
    var cRight := Pivots.CutoffForRight(node.pivotTable, pivot);
    var rightPivots := node.pivotTable[cRight ..];
    var rightChildren := if node.children.Some? then Some(node.children.value[cRight ..]) else None;
    var splitBucket := SplitBucketRight(node.buckets[cRight], pivot);
    var rightBuckets := [splitBucket] + node.buckets[cRight + 1 ..];
    Node(rightPivots, rightChildren, rightBuckets)
  }

  lemma CutoffNodeAndKeepRightCorrect(node: Node, pivot: Key)
  requires WFNode(node)
  requires BT.WFNode(INode(node))
  ensures var node' := CutoffNodeAndKeepRight(node, pivot);
    && WFNode(node')
    && INode(node') == BT.CutoffNodeAndKeepRight(INode(node), pivot)
  {
    reveal_CutoffNodeAndKeepRight();
    BT.reveal_CutoffNodeAndKeepRight();
    var cRight := Pivots.CutoffForRight(node.pivotTable, pivot);
    var rightPivots := node.pivotTable[cRight ..];
    var rightChildren := if node.children.Some? then Some(node.children.value[cRight ..]) else None;
    var splitBucket := SplitBucketRight(node.buckets[cRight], pivot);
    var rightBuckets := [splitBucket] + node.buckets[cRight + 1 ..];
    Pivots.WFSuffix(node.pivotTable, cRight);
    WFSplitBucketListRight(node.buckets, node.pivotTable, cRight, pivot);
    WeightSplitBucketListRight(node.buckets, node.pivotTable, cRight, pivot);
  }

  function {:opaque} CutoffNode(node: Node, lbound: Option<Key>, rbound: Option<Key>)
  : (node' : Node)
  requires WFNode(node)
  ensures |node'.buckets| == |node'.pivotTable| + 1
  ensures node'.children.Some? ==> |node'.buckets| == |node'.children.value|
  {
    match lbound {
      case None => (
        match rbound {
          case None => (
            node
          )
          case Some(rbound) => (
            CutoffNodeAndKeepLeft(node, rbound)
          )
        }
      )
      case Some(lbound) => (
        match rbound {
          case None => (
            CutoffNodeAndKeepRight(node, lbound)
          )
          case Some(rbound) => (
            var node1 := CutoffNodeAndKeepLeft(node, rbound);
            CutoffNodeAndKeepLeftCorrect(node, rbound); // we need WFNode(node1)
            CutoffNodeAndKeepRight(node1, lbound)
          )
        }
      )
    }
  }

  lemma CutoffNodeCorrect(node: Node, lbound: Option<Key>, rbound: Option<Key>)
  requires WFNode(node)
  requires BT.WFNode(INode(node))
  ensures var node' := CutoffNode(node, lbound, rbound);
    && WFNode(node')
    && INode(node') == BT.CutoffNode(INode(node), lbound, rbound)
  {
    reveal_CutoffNode();
    BT.reveal_CutoffNode();

    match lbound {
      case None => {
        match rbound {
          case None => {
          }
          case Some(rbound) => {
            CutoffNodeAndKeepLeftCorrect(node, rbound);
          }
        }
      }
      case Some(lbound) => {
        match rbound {
          case None => {
            CutoffNodeAndKeepRightCorrect(node, lbound);
          }
          case Some(rbound) => {
            var node1 := CutoffNodeAndKeepLeft(node, rbound);
            CutoffNodeAndKeepLeftCorrect(node, rbound);
            CutoffNodeAndKeepRightCorrect(node1, lbound);
          }
        }
      }
    }
  }

  function {:opaque} NodeInsertKeyValue(node: Node, key: Key, msg: Message) : Node
  requires WFNode(node)
  {
    var r := Pivots.Route(node.pivotTable, key);
    var bucket := node.buckets[r];
    var newBucket := BucketInsert(bucket, key, msg);
    node.(buckets := node.buckets[r := newBucket])
  }

  function {:opaque} SplitChildLeft(child: Node, num_children_left: int) : Node
  requires 0 <= num_children_left - 1 <= |child.pivotTable|
  requires child.children.Some? ==> 0 <= num_children_left <= |child.children.value|
  requires 0 <= num_children_left <= |child.buckets|
  {
    Node(
      child.pivotTable[ .. num_children_left - 1 ],
      if child.children.Some? then Some(child.children.value[ .. num_children_left ]) else None,
      child.buckets[ .. num_children_left ]
    )
  }

  function {:opaque} SplitChildRight(child: Node, num_children_left: int) : Node
  requires 0 <= num_children_left <= |child.pivotTable|
  requires child.children.Some? ==> 0 <= num_children_left <= |child.children.value|
  requires 0 <= num_children_left <= |child.buckets|
  {
    Node(
      child.pivotTable[ num_children_left .. ],
      if child.children.Some? then Some(child.children.value[ num_children_left .. ]) else None,
      child.buckets[ num_children_left .. ]
    )
  }

  lemma lemmaSplitChild(child: Node, num_children_left: int)
  requires WFNode(child)
  requires BT.WFNode(INode(child))
  requires 1 <= num_children_left <= |child.buckets| - 1
  ensures WFNode(SplitChildLeft(child, num_children_left))
  ensures WFNode(SplitChildRight(child, num_children_left))
  ensures INode(SplitChildLeft(child, num_children_left)) == BT.SplitChildLeft(INode(child), num_children_left)
  ensures INode(SplitChildRight(child, num_children_left)) == BT.SplitChildRight(INode(child), num_children_left)
  {
    reveal_SplitChildLeft();
    reveal_SplitChildRight();
    Pivots.WFSlice(child.pivotTable, 0, num_children_left - 1);
    Pivots.WFSuffix(child.pivotTable, num_children_left);
    WFBucketListSplitLeft(child.buckets, child.pivotTable, num_children_left);
    WFBucketListSplitRight(child.buckets, child.pivotTable, num_children_left);
    WeightBucketListSlice(child.buckets, 0, num_children_left);
    WeightBucketListSuffix(child.buckets, num_children_left);
    assert WFNode(SplitChildRight(child, num_children_left));
    assert WFNode(SplitChildLeft(child, num_children_left));
  }

  function {:opaque} CacheInsertKeyValue(cache: map<BT.G.Reference, Node>, ref: BT.G.Reference, key: Key, msg: Message) : map<BT.G.Reference, Node>
  requires ref in cache
  requires WFNode(cache[ref])
  {
    cache[ref := NodeInsertKeyValue(cache[ref], key, msg)]
  }

}
