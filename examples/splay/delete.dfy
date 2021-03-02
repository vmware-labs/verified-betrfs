// Copyright 2018-2021 VMware, Inc.
// SPDX-License-Identifier: BSD-2-Clause

method find_node(root: Node, value: uint64) returns (out: Node?)
requires is_valid_node(root)
ensures value in value_set(root) ==> out != null
ensures value in value_set(root) ==> out in node_set(root)
ensures value in value_set(root) ==> out.value == value
ensures value !in value_set(root) ==> out == null
{
  var node := root;
  while (node != null)
  invariant is_valid_node(node)
  invariant node != null ==> node in node_set(root)
  invariant value in value_set(root) ==> value in value_set(node)
  invariant value in value_set(node) ==> value in value_set(root)
  decreases |node_set(node)|
  {
    node_set_contained(root, node);
    assert node_set(node) <= node_set(root);
    if (node.l != null) {
      assert node.l in node_set(root);
    }
    if (node.r != null) {
      assert node.r in node_set(root);
    }

    if (node.value == value) {
      return node;
    } else if (value < node.value) {
      node := node.l;
    } else {
      node := node.r;
    }
  }
  return null;
}

method get_max(root: Node) returns (out: Node)
requires is_valid_node(root)
ensures out in node_set(root)
ensures out.value in value_set(root)
ensures forall v:uint64 :: v in value_set(root) ==> out.value >= v
ensures is_valid_node(out)
{
  var node := root;
  while (node.r != null)
  invariant node != null
  invariant is_valid_node(node)
  invariant node.value in value_set(root)
  invariant node in node_set(root)
  invariant node_set(node) <= node_set(root)
  invariant value_set(node) <= value_set(root)
  invariant forall x:uint64 :: x in {node.value} + value_set(node.r) ==>
            forall y:uint64 :: y in value_set(root) - ({node.value} + value_set(node.r)) ==>
            x > y
  decreases |node_set(node)|
  {
    node := node.r;
  }

  assert forall x:uint64 :: x in {node.value} + value_set(node.r) ==>
         forall y:uint64 :: y in value_set(root) - ({node.value} + value_set(node.r)) ==>
         x > y;
  assert value_set(node.r) == {};
  assert {node.value} + value_set(node.r) == {node.value};
  assert value_set(root) - ({node.value} + value_set(node.r)) == value_set(root) - {node.value};
  assert forall x:uint64 :: x in {node.value} ==>
         forall y:uint64 :: y in value_set(root) - ({node.value} + value_set(node.r)) ==>
         x > y;
  assert forall x:uint64 :: x in {node.value} ==>
         forall y:uint64 :: y in value_set(root) - {node.value} ==>
         x > y;
  assert forall y:uint64 :: y in value_set(root) - {node.value} ==> node.value > y;
  assert forall y:uint64 :: y in value_set(root) - {node.value} ==> node.value >= y;
  assert forall y:uint64 :: y in {node.value} ==> node.value >= y;
  assert forall y:uint64 :: y in value_set(root) ==> node.value >= y;

  return node;
}

lemma
lemma_max_node_r_is_null(max_node: Node, vset: set<uint64>)
requires is_valid_node(max_node)
requires value_set(max_node) == vset
requires forall v:uint64 :: v in vset ==> max_node.value >= v
ensures max_node.r == null
ensures vset == {max_node.value} + value_set(max_node.l)
{
}

lemma
lemma_left_plus_right_is_correct(node: Node, left_vset: set<uint64>, right_vset: set<uint64>,
    all_values: set<uint64>, value: uint64)
requires is_valid_node(node)
requires node.value == value
requires left_vset == value_set(node.l)
requires right_vset == value_set(node.r)
requires all_values == value_set(node);
ensures left_vset + right_vset == all_values - {value}
{
  assert value !in left_vset;
  assert value !in right_vset;
  assert all_values == {value} + left_vset + right_vset;
  assert all_values - {value} == ({value} + left_vset + right_vset) - {value}
      == left_vset + right_vset;
}

lemma
lemma_max_node_is_structurally_valid(node: Node)
requires node.node_set == {node} + node_set(node.l) + node_set(node.r)
requires is_structurally_valid(node.l)
requires is_structurally_valid(node.r)
ensures is_structurally_valid(node)
{
  lemma_node_set_of_children_is_smaller(node);
}

lemma
lemma_max_node_has_correct_vset(
    max_node: Node,
    left_vset: set<uint64>,
    right_vset: set<uint64>,
    all_values: set<uint64>,
    value: uint64)
requires is_valid_node(max_node)
requires left_vset == {max_node.value} + value_set(max_node.l)
requires right_vset == value_set(max_node.r)
requires left_vset + right_vset == all_values - {value}
ensures value_set(max_node) == all_values - {value}
{
  assert value_set(max_node)
      == {max_node.value} + value_set(max_node.l) + value_set(max_node.r)
      == left_vset + value_set(max_node.r)
      == left_vset + right_vset
      == all_values - {value};
}

lemma lemma_node_r_not_in_max_node_l(node: Node, max_node: Node, left_vset: set<uint64>,
    value: uint64)
requires is_valid_node(max_node);
requires node.r != null
requires node.r.value > value
requires max_node.value < value
requires forall v:uint64 :: v in left_vset ==> max_node.value >= v;
ensures node.r !in node_set(max_node.l)
{
  if (node.r in node_set(max_node.l)) {
    node_set_to_value_set(node.r, max_node.l);
    assert node.r.value in value_set(max_node.l);
    assert node.r.value < max_node.value;
    assert node.r.value > node.r.value;
    assert false;
  }
}

method
{:fuel is_structurally_valid,0,0} {:fuel value_set,0,0}
delete(tree: Tree, value: uint64)
modifies tree, tree.root, if tree.root != null then tree.root.node_set else {}
requires is_valid_tree(tree)
ensures is_valid_tree(tree)
ensures tree_set(tree) == old(tree_set(tree)) - {value}
{
  ghost var all_nodes := node_set(tree.root);
  ghost var all_values := value_set(tree.root);

  null_value_set();

  if (tree.root != null) {
    var node := find_node(tree.root, value);
    if (node != null) {
      splay(node, /* ghosts: */ tree.root, value_set(tree.root));
      assert all_nodes == node_set(node);

      if (node.l == null) {
        if (node.r == null) {
          singleton_value_set(node);
          assert all_values == value_set(node)
                            == {node.value};
          assert all_values - {value} == {};
          
          tree.root := null;

          assert tree_set(tree) == value_set(null)
            == {}
            == all_values - {value};
        } else {
          right_is_in_node_set(node);

          tree.root := node.r;

          get_value_set(node);
          assert all_values == value_set(node)
              == {node.value} + value_set(node.r);
          assert node.value !in value_set(node.r);
          assert all_values - {value} ==
              all_values - {node.value} ==
              ({node.value} + value_set(node.r)) - {node.value} ==
              value_set(node.r);

          ghost var vsnl := value_set(node.r);
          lemma_modify_p_doesnt_affect_validity1(node.r, vsnl);
          node.r.p := null;
          lemma_modify_p_doesnt_affect_validity2(node.r, vsnl);

          assert all_values - {value} == value_set(node.r);
        }
      } else {
        if (node.r == null) {
          left_is_in_node_set(node);

          tree.root := node.l;

          get_value_set(node);
          assert all_values == value_set(node)
              == {node.value} + value_set(node.l);
          assert node.value !in value_set(node.l);
          assert all_values - {value} ==
              all_values - {node.value} ==
              ({node.value} + value_set(node.l)) - {node.value} ==
              value_set(node.l);

          ghost var vsnl := value_set(node.l);
          lemma_modify_p_doesnt_affect_validity1(node.l, vsnl);
          node.l.p := null;
          lemma_modify_p_doesnt_affect_validity2(node.l, vsnl);

          assert all_values - {value} == value_set(node.l);
        } else {
          left_is_in_node_set(node);
          right_is_in_node_set(node);

          right_not_in_left(node);
          assert node.r !in node_set(node.l);
          l_node_set_le_node_set(node);
          assert node_set(node.l) <= all_nodes;
          self_ne_left(node);
          assert node != node.l;
          left_ne_right(node);
          assert node.l != node.r;
          not_in_children(node);
          assert node !in node_set(node.l);
          left_not_in_right(node);
          assert is_valid_node(node.l);
          assert is_valid_node(node.r);
          sides_disjoint_forall(node);

          ghost var left_vset := value_set(node.l);
          ghost var right_vset := value_set(node.r);
          lemma_left_plus_right_is_correct(node, left_vset, right_vset, all_values, value);

          right_not_in_left(node);
          assert node.r !in node_set(node.l);

          right_is_gt(node);
          assert node.r.value > value;

          lemma_modify_p_doesnt_affect_validity1(node.l, left_vset);
          node.l.p := null;
          lemma_modify_p_doesnt_affect_validity2(node.l, left_vset);

          var max_node := get_max(node.l);
          assert left_vset == value_set(node.l);
          assert forall v:uint64 :: v in left_vset ==> max_node.value >= v;
          assert node.r !in node_set(node.l);

          assert is_valid_node(node.l);
          assert is_valid_node(node.r);

          splay(max_node, /* ghosts: */ node.l, left_vset);

          assert is_valid_node(max_node);
          assert is_valid_node(node.r);
          assert forall v:uint64 :: v in left_vset ==> max_node.value >= v;

          lemma_max_node_r_is_null(max_node, left_vset);

          assert is_valid_node(max_node.l);
          not_in_children(max_node);
          lemma_node_r_not_in_max_node_l(node, max_node, left_vset, value);
          assert node.r !in node_set(max_node.l);

          max_node.r := node.r;

          assert is_valid_node(max_node.l);
          assert max_node.r !in node_set(max_node.l);

          lemma_modify_p_doesnt_affect_validity1(max_node.r, right_vset);
          max_node.r.p := max_node;
          lemma_modify_p_doesnt_affect_validity2(max_node.r, right_vset);

          max_node.node_set := {max_node} + node_set(max_node.l) + node_set(max_node.r);
          tree.root := max_node;

          lemma_max_node_is_structurally_valid(max_node);
          lemma_max_node_has_correct_vset(max_node, left_vset, right_vset, all_values, value);
        }
      }
    }
  }
}
