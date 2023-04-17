module LinearInout2 {

linear datatype Tree = Leaf(val: bool) | Node(linear left: Tree, linear right: Tree) {
  linear method Free() {
    linear match this {
      case Node(left, right) => {
        left.Free();
        right.Free();
      }
      case Leaf(_) => {}
    }
  }
}

predicate LeavesHaveValue(tree: Tree, val: bool) {
  && (tree.Node? ==> LeavesHaveValue(tree.left, val) && LeavesHaveValue(tree.right, val))
  && (tree.Leaf? ==> tree.val == val)
}

method flip(linear inout tree: Tree)
ensures forall val: bool :: LeavesHaveValue(old_tree, val) ==> LeavesHaveValue(tree, !val)
{
  if tree.Leaf? {
    inout tree.val := !tree.val;
  } else if tree.Node? {
    flip(inout tree.left);
    flip(inout tree.right);
  } else {
    assert false;
  }
}

method Main() {
  linear var tree := Node(Leaf(false), Node(Leaf(false), Leaf(false)));
  assert LeavesHaveValue(tree, false);
  flip(inout tree);
  assert LeavesHaveValue(tree, true);
  tree.Free();
}

}
