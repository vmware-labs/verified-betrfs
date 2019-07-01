class Node
{
  var l: Node?;
  var r: Node?;
  var p: Node?; // parent

  var value: int;

  ghost var node_set: set<Node>;
}

function node_set(a: Node?): set<Node>
reads a
{
  if (a == null) then {} else a.node_set
}

predicate is_structurally_valid(a: Node?)
reads a
reads node_set(a)
decreases |node_set(a)|
{
  if (a == null) then
    true
  else (
    (a.l == null || a.l in a.node_set) &&
    (a.r == null || a.r in a.node_set) &&
    |node_set(a.l)| < |a.node_set| &&
    |node_set(a.r)| < |a.node_set| &&
    a.node_set == {a} + node_set(a.l) + node_set(a.r) &&
    is_structurally_valid(a.l) &&
    is_structurally_valid(a.r)
  )
}

function value_set(a: Node?): set<int>
reads a
reads node_set(a)
requires is_structurally_valid(a)
decreases |node_set(a)|
{
  if (a == null) then
    {}
  else
    {a.value} + value_set(a.l) + value_set(a.r)
}

predicate is_valid_node(a: Node?)
reads a
reads node_set(a)
decreases |node_set(a)|
{
  is_structurally_valid(a) && (
    if (a == null) then
      true
    else (
      (a.l == null || a.l.p == a) &&
      (a.r == null || a.r.p == a) &&
      (forall t: int :: t in value_set(a.l) ==> t < a.value) &&
      (forall t: int :: t in value_set(a.r) ==> t > a.value) &&
      is_valid_node(a.l) &&
      is_valid_node(a.r)
    )
  )
}

class Tree
{
  var root: Node?;
}

predicate is_valid_tree(tree: Tree)
reads tree
reads tree.root
reads node_set(tree.root)
{
  tree.root == null || (tree.root.p == null && is_valid_node(tree.root))
}

function tree_set(tree: Tree): set<int>
requires is_valid_tree(tree)
reads tree
reads tree.root
reads node_set(tree.root)
{
  value_set(tree.root)
}

function values_of_nodes(s: set<Node>): set<int>
reads s
{
  set node:Node | node in s :: node.value
}
