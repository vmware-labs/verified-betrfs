method new_tree() returns (tree: Tree)
ensures is_valid_tree(tree)
ensures tree_set(tree) == {}
ensures fresh(tree)
{
  var t := new Tree;
  t.root := null;
  return t;
}

method contains(tree: Tree, value: uint64) returns (b: bool)
requires is_valid_tree(tree)
ensures is_valid_tree(tree)
ensures tree_set(tree) == old(tree_set(tree))
ensures b == (value in tree_set(tree))
{
  if (tree.root == null) {
    return false;
  } else {
    var node := tree.root;
    while (node != null)
    invariant is_valid_node(node)
    invariant (value in value_set(node)) ==> (value in value_set(tree.root))
    invariant (value in value_set(tree.root)) ==> (value in value_set(node))
    decreases |node_set(node)|
    {
      if (node.value == value) {
        return true;
      }
      if (value < node.value) {
        node := node.l;
      } else {
        node := node.r;
      }
    }
    return false;
  }
}
