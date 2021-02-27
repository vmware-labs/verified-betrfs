// Copyright 2018-2021 VMware, Inc.
// SPDX-License-Identifier: MIT

method
{:fuel is_structurally_valid,0,0} {:fuel value_set,0,0}
splay(node: Node,
    ghost root: Node,
    ghost full_value_set: set<uint64>)
modifies root.node_set
requires root.p == null
requires is_valid_node(root)
requires node in node_set(root)
requires value_set(root) == full_value_set
ensures node.p == null
ensures is_valid_node(node)
ensures value_set(node) == full_value_set
ensures node_set(node) == old(node_set(root))
ensures node.value == old(node.value)
{
  valid_subtree_is_valid(root, node);

  ghost var nsr := node_set(root);
  ghost var xval := node.value;

  child_set_size_le(root, node);
  assert |node_set(root)| - |node_set(node)| >= 0;

  if (node.p == null) {
    p_null_implies_root(root, node);
    assert node == root;
  }

  while (node.p != null)
  invariant is_valid_node(root)
  invariant is_valid_node(node)
  invariant node.p != null ==> node in node_set(root)
  invariant node.p != null ==> root.p == null
  invariant node.p != null ==> value_set(root) == full_value_set
  invariant node.p != null ==> nsr == node_set(root)
  invariant (if node.p != null then |node_set(root)| - |node_set(node)| else 0) >= 0
  invariant node.p == null ==> value_set(node) == full_value_set
  invariant node.p == null ==> node_set(node) == nsr
  invariant node.value == xval
  decreases if node.p != null then |node_set(root)| - |node_set(node)| + 1 else 0
  {
    var p := node.p;
    var g := p.p;

    ghost var old_decreases_value :=
      if node.p != null then |node_set(root)| - |node_set(node)| + 1 else 0;

    assert root != node;
    parent_is_in_set(root, node); // show p is in node_set(root)
    is_one_of_parents_children(root, node);

    if (g == null) {
      if (p.l == node) {
        if (node.r != null) { r_is_in_set(root, node); }

        zig_left(node, p, root, full_value_set, node_set(node), nsr, null);
      } else {
        assert p.r == node;
        if (node.l != null) { l_is_in_set(root, node); }

        zig_right(node, p, root, full_value_set, node_set(node), nsr, null);
      }
    } else {
      parent_is_in_set(root, p); // show g is in node_set(root)
      is_one_of_parents_children(root, p);
      if (g.p != null) {
        parent_is_in_set(root, g);
      }

      if (g.l == p) {
        if (p.l == node) {
          if (node.r != null) { r_is_in_set(root, node); }
          if (p.r != null) { r_is_in_set(root, p); }

          zig_zig_left(node, p, g, root, full_value_set, node_set(node), nsr, g.p);
        } else {
          assert p.r == node;
          if (node.l != null) { l_is_in_set(root, node); }
          if (node.r != null) { r_is_in_set(root, node); }

          zig_zag_left(node, p, g, root, full_value_set, node_set(node), nsr, g.p);
        }
      } else {
        assert g.r == p;
        if (p.l == node) {
          if (node.l != null) { l_is_in_set(root, node); }
          if (node.r != null) { r_is_in_set(root, node); }

          zig_zag_right(node, p, g, root, full_value_set, node_set(node), nsr, g.p);
        } else {
          assert p.r == node;
          if (node.l != null) { l_is_in_set(root, node); }
          if (p.l != null) { l_is_in_set(root, p); }

          zig_zig_right(node, p, g, root, full_value_set, node_set(node), nsr, g.p);
        }
      }
    }

    if (node.p != null) {
      child_set_size_le(root, node);
      assert |node_set(root)| - |node_set(node)| >= 0;
    }
    assert 0 <= (if node.p != null then |node_set(root)| - |node_set(node)| else 0);

    assert node.p != null ==>
        (if node.p != null then |node_set(root)| - |node_set(node)| + 1 else 0)
        < old_decreases_value;
  }
}

method 
{:fuel is_structurally_valid,0,0} {:fuel value_set,0,0}
zig_zig_left(x: Node, p: Node, g: Node, ghost root: Node, ghost full_value_set: set<uint64>, ghost ns: set<Node>, ghost nsr: set<Node>, ghost gg: Node?)
modifies x
modifies p
modifies g
modifies x.r
modifies p.r
modifies gg
requires root.p == null
requires is_valid_node(root)
requires x in node_set(root)
requires value_set(root) == full_value_set
requires ns == node_set(x)
requires nsr == node_set(root)
requires x.p == p
requires p.p == g
requires p.l == x
requires g.l == p
requires gg == g.p
ensures x.p == gg
ensures is_valid_node(x)
ensures is_valid_node(root)
ensures gg == null ==> value_set(x) == full_value_set
ensures gg == null ==> node_set(x) == nsr
ensures gg != null ==> value_set(root) == full_value_set
ensures gg != null ==> node_set(root) == nsr
ensures gg != null ==> x in node_set(root)
ensures gg != null ==> root.p == null
ensures x.value == old(x.value)
ensures |node_set(x)| > |ns|
{
  parent_is_in_set(root, x);
  parent_is_valid(root, x);
  parent_is_valid(root, p);

  self_ne_parent(x, root); assert x != p;
  self_ne_grandparent(x, root); assert x != g;
  left_ne_right(p); assert x != p.r;
  if (gg == null) {
    root_is_p(root, p, g); assert g == root;
  }
  self_ne_greatgrandparent(x, root); assert x != gg;

  zig_left(p, g, root, full_value_set, node_set(p), nsr, gg);

  assert x == p.l;
  left_is_in_node_set(p);
  assert x in node_set(p);
  if (gg != null) {
    assert x in node_set(root);
  }

  assert p.r == g;
  assert p.p == gg;

  zig_left(x, p, if gg == null then p else root, full_value_set, ns, nsr, gg);

  assert x.r == p;
  assert p.r == g;
  assert is_valid_node(x);
  assert is_valid_node(p);
  if (gg == null) {
    assert p.r == g
        == root;
    assert is_valid_node(root);
  }
}

method zig_zag_left(x: Node, p: Node, g: Node, ghost root: Node, ghost full_value_set: set<uint64>, ghost ns: set<Node>, ghost nsr: set<Node>, ghost gg: Node?)
modifies x
modifies p
modifies g
modifies x.l
modifies x.r
modifies gg
requires root.p == null
requires is_valid_node(root)
requires x in node_set(root)
requires value_set(root) == full_value_set
requires ns == node_set(x)
requires nsr == node_set(root)
requires x.p == p
requires p.p == g
requires p.r == x
requires g.l == p
requires gg == g.p
ensures x.p == gg
ensures is_valid_node(x)
ensures is_valid_node(root)
ensures gg == null ==> value_set(x) == full_value_set
ensures gg == null ==> node_set(x) == nsr
ensures gg != null ==> value_set(root) == full_value_set
ensures gg != null ==> node_set(root) == nsr
ensures gg != null ==> x in node_set(root)
ensures gg != null ==> root.p == null
ensures x.value == old(x.value)
ensures |node_set(x)| > |ns|
{
  parent_is_in_set(root, x);
  parent_is_valid(root, x);
  parent_is_in_set(root, p);
  parent_is_valid(root, p);

  assert x.value in value_set(x);
  assert x.value in value_set(g.l);
  assert x.value < g.value;

  zig_right(x, p, root, full_value_set, ns, nsr, g);

  assert x.p == g;
  is_one_of_parents_children(root, x);
  assert g.l == x || g.r == x;
  assert x.value < g.value;
  assert g in node_set(root);
  valid_subtree_is_valid(root, g);
  assert is_valid_node(g);
  if (g.r == x) {
    assert x.value in value_set(g.r);
    assert x.value > g.value;
    assert false;
  }
  assert g.l == x;

  zig_left(x, g, root, full_value_set, node_set(x), nsr, gg);
}

method
{:fuel is_structurally_valid,0,0} {:fuel value_set,0,0}
zig_zig_right(x: Node, p: Node, g: Node, ghost root: Node, ghost full_value_set: set<uint64>, ghost ns: set<Node>, ghost nsr: set<Node>, ghost gg: Node?)
modifies x
modifies p
modifies g
modifies x.l
modifies p.l
modifies gg
requires root.p == null
requires is_valid_node(root)
requires x in node_set(root)
requires value_set(root) == full_value_set
requires ns == node_set(x)
requires nsr == node_set(root)
requires x.p == p
requires p.p == g
requires p.r == x
requires g.r == p
requires gg == g.p
ensures x.p == gg
ensures is_valid_node(x)
ensures is_valid_node(root)
ensures gg == null ==> value_set(x) == full_value_set
ensures gg == null ==> node_set(x) == nsr
ensures gg != null ==> value_set(root) == full_value_set
ensures gg != null ==> node_set(root) == nsr
ensures gg != null ==> x in node_set(root)
ensures gg != null ==> root.p == null
ensures x.value == old(x.value)
ensures |node_set(x)| > |ns|
{
  parent_is_in_set(root, x);
  parent_is_valid(root, x);
  parent_is_valid(root, p);

  self_ne_parent(x, root); assert x != p;
  self_ne_grandparent(x, root); assert x != g;
  left_ne_right(p); assert x != p.l;
  if (gg == null) {
    root_is_p(root, p, g); assert g == root;
  }
  self_ne_greatgrandparent(x, root); assert x != gg;

  zig_right(p, g, root, full_value_set, node_set(p), nsr, gg);

  assert x == p.r;
  right_is_in_node_set(p);
  assert x in node_set(p);
  if (gg != null) {
    assert x in node_set(root);
  }

  assert p.l == g;
  assert p.p == gg;

  zig_right(x, p, if gg == null then p else root, full_value_set, ns, nsr, gg);

  assert x.l == p;
  assert p.l == g;
  assert is_valid_node(x);
  assert is_valid_node(p);
  if (gg == null) {
    assert p.l == g
        == root;
    assert is_valid_node(root);
  }
}

method zig_zag_right(x: Node, p: Node, g: Node, ghost root: Node, ghost full_value_set: set<uint64>, ghost ns: set<Node>, ghost nsr: set<Node>, ghost gg: Node?)
modifies x
modifies p
modifies g
modifies x.l
modifies x.r
modifies gg
requires root.p == null
requires is_valid_node(root)
requires x in node_set(root)
requires value_set(root) == full_value_set
requires ns == node_set(x)
requires nsr == node_set(root)
requires x.p == p
requires p.p == g
requires p.l == x
requires g.r == p
requires gg == g.p
ensures x.p == gg
ensures is_valid_node(x)
ensures is_valid_node(root)
ensures gg == null ==> value_set(x) == full_value_set
ensures gg == null ==> node_set(x) == nsr
ensures gg != null ==> value_set(root) == full_value_set
ensures gg != null ==> node_set(root) == nsr
ensures gg != null ==> x in node_set(root)
ensures gg != null ==> root.p == null
ensures x.value == old(x.value)
ensures |node_set(x)| > |ns|
{
  parent_is_in_set(root, x);
  parent_is_valid(root, x);
  parent_is_in_set(root, p);
  parent_is_valid(root, p);

  assert x.value in value_set(x);
  assert x.value in value_set(g.r);
  assert x.value > g.value;

  zig_left(x, p, root, full_value_set, ns, nsr, g);

  assert x.p == g;
  is_one_of_parents_children(root, x);
  assert g.l == x || g.r == x;
  assert x.value > g.value;
  assert g in node_set(root);
  valid_subtree_is_valid(root, g);
  assert is_valid_node(g);
  if (g.l == x) {
    assert x.value in value_set(g.l);
    assert x.value > g.value;
    assert false;
  }
  assert g.r == x;

  zig_right(x, g, root, full_value_set, node_set(x), nsr, gg);

}
