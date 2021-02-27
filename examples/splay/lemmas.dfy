// Copyright 2018-2021 VMware, Inc.
// SPDX-License-Identifier: MIT

lemma node_set_contained(v: Node, w: Node)
requires is_structurally_valid(v)
requires w in node_set(v)
ensures node_set(w) <= node_set(v)
decreases |node_set(v)|
{
  structurally_valid_subtree_is_valid(v, w);
  if (w == v) {
  } else if (w in node_set(v.l)) {
    node_set_contained(v.l, w);
  } else {
    assert w in node_set(v.r);
    node_set_contained(v.r, w);
  }
}

lemma lemma_node_set_of_children_is_smaller(a: Node)
requires is_structurally_valid(a.l)
requires is_structurally_valid(a.r)
requires a.node_set == {a} + node_set(a.l) + node_set(a.r)
ensures |node_set(a.l)| < |a.node_set|
ensures |node_set(a.r)| < |a.node_set|
{
  node_is_not_in_valid_child_subtree(a);

  assert node_set(a.l) <= a.node_set;
  set_ineq(node_set(a.l), a.node_set, a);

  assert node_set(a.r) <= a.node_set;
  set_ineq(node_set(a.r), a.node_set, a);
}

lemma set_ineq<T>(a: set<T>, b: set<T>, x: T)
requires a <= b
requires x in b
requires x !in a
decreases |a|
ensures |a| < |b|
{
  if (|a| == 0) {
    assert |b| >= 1;
  } else {
    var y :| y in a;
    assert y in b;
    assert |a - {y}| == |a| - 1;
    assert |b - {y}| == |b| - 1;
    set_ineq(a - {y}, b - {y}, x);
  }
}

lemma node_is_not_in_valid_child_subtree_left(node: Node)
requires is_structurally_valid(node.l)
ensures node !in node_set(node.l)
{
  if (node in node_set(node.l)) {
    structurally_valid_subtree_is_valid(node.l, node);
    assert is_structurally_valid(node);
    not_in_children(node);
    assert node !in node_set(node.l);
  }
}

lemma node_is_not_in_valid_child_subtree_right(node: Node)
requires is_structurally_valid(node.r)
ensures node !in node_set(node.r)
{
  if (node in node_set(node.r)) {
    structurally_valid_subtree_is_valid(node.r, node);
    assert is_structurally_valid(node);
    not_in_children(node);
    assert node !in node_set(node.r);
  }
}

lemma node_is_not_in_valid_child_subtree_rl(node: Node)
requires node.r != null
requires is_structurally_valid(node.r.l)
ensures node !in node_set(node.r.l)
{
  if (node in node_set(node.r.l)) {
    structurally_valid_subtree_is_valid(node.r.l, node);
    assert is_structurally_valid(node);
    not_in_children(node);
    assert node !in node_set(node.r);
    assert node !in node_set(node.r.l);
  }
}

lemma node_is_not_in_valid_child_subtree_lr(node: Node)
requires node.l != null
requires is_structurally_valid(node.l.r)
ensures node !in node_set(node.l.r)
{
  if (node in node_set(node.l.r)) {
    structurally_valid_subtree_is_valid(node.l.r, node);
    assert is_structurally_valid(node);
    not_in_children(node);
    assert node !in node_set(node.l);
    assert node !in node_set(node.l.r);
  }
}

lemma node_is_not_in_valid_child_subtree_rr(node: Node)
requires node.r != null
requires is_structurally_valid(node.r.r)
ensures node !in node_set(node.r.r)
{
  if (node in node_set(node.r.r)) {
    structurally_valid_subtree_is_valid(node.r.r, node);
    assert is_structurally_valid(node);
    not_in_children(node);
    assert node !in node_set(node.r);
    assert node !in node_set(node.r.r);
  }
}

lemma node_is_not_in_valid_child_subtree_ll(node: Node)
requires node.l != null
requires is_structurally_valid(node.l.l)
ensures node !in node_set(node.l.l)
{
  if (node in node_set(node.l.l)) {
    structurally_valid_subtree_is_valid(node.l.l, node);
    assert is_structurally_valid(node);
    not_in_children(node);
    assert node !in node_set(node.l);
    assert node !in node_set(node.l.l);
  }
}

lemma node_is_not_in_valid_child_subtree(node: Node)
requires is_structurally_valid(node.l)
requires is_structurally_valid(node.r)
ensures node !in node_set(node.l)
ensures node !in node_set(node.r)
{
  node_is_not_in_valid_child_subtree_left(node);
  node_is_not_in_valid_child_subtree_right(node);
}

lemma node_is_not_in_descendant_subtree(root: Node, node: Node)
requires is_valid_node(root)
requires node in node_set(root)
requires root != node
ensures root !in node_set(node)
{
  structurally_valid_subtree_is_valid(root, node);
  node_is_not_in_valid_child_subtree(root);
  if (node in node_set(root.l)) {
    node_set_contained(root.l, node);
  } else {
    node_set_contained(root.r, node);
  }
}

lemma structurally_valid_subtree_is_valid(root: Node, node: Node)
requires is_structurally_valid(root)
requires node in node_set(root)
decreases |node_set(root)|
ensures is_structurally_valid(node)
{
  assert node_set(root) == {root} + node_set(root.l) + node_set(root.r);
  assert node in ({root} + node_set(root.l) + node_set(root.r));
  if (node == root) {
    assert is_structurally_valid(node);
  } else if (node in node_set(root.l)) {
    structurally_valid_subtree_is_valid(root.l, node);
  } else {
    structurally_valid_subtree_is_valid(root.r, node);
  }
}

lemma lemma_left_and_right_are_distinct(l: Node, r: Node, x: uint64)
requires is_structurally_valid(l)
requires is_structurally_valid(r)
requires (forall t: uint64 :: t in value_set(l) ==> t < x)
requires (forall t: uint64 :: t in value_set(r) ==> t > x)
ensures l != r
{
  assert l.value in value_set(l);
  assert r.value in value_set(r);
  if (l == r) {
    assert l.value == r.value;
    assert l.value < x;
    assert r.value > x;
    assert false;
  }
}

lemma root_is_p(root: Node, x: Node, p: Node)
requires is_valid_node(root)
requires x.p == p
requires root.p == null
requires x in node_set(root)
requires p.p == null
ensures p == root
{
  if (p != root) {
    parent_is_in_set(root, x);
    non_root_has_parent(root, p);
  }
}

lemma r_is_in_set(root: Node, x: Node)
requires is_valid_node(root)
requires x in node_set(root)
requires x.r != null
ensures x.r in node_set(root)
{
  valid_subtree_is_valid(root, x);
  node_set_contained(root, x);
  assert is_valid_node(x.r);
  assert x.r in node_set(x.r);
  assert x.r in node_set(x);
}

lemma l_is_in_set(root: Node, x: Node)
requires is_valid_node(root)
requires x in node_set(root)
requires x.l != null
ensures x.l in node_set(root)
{
  valid_subtree_is_valid(root, x);
  node_set_contained(root, x);
  assert x.l in node_set(x);
}

lemma is_one_of_parents_children(root: Node, x: Node)
requires is_valid_node(root)
requires x in node_set(root)
requires x.p != null
requires x != root
decreases |node_set(root)|
ensures x.p.l == x || x.p.r == x
{
}

lemma parent_is_in_set(root: Node, x: Node)
requires is_valid_node(root)
requires x in node_set(root)
requires x.p != null
requires x != root
decreases |node_set(root)|
ensures x.p in node_set(root)
{
  assert x in {root} + node_set(root.l) + node_set(root.r);
  if (root == x) {
  } else if (x in node_set(root.l)) {
    if (x == root.l) {
      assert x.p == root;
      assert x.p in node_set(root);
    } else {
      parent_is_in_set(root.l, x);
    }
  } else {
    assert (x in node_set(root.r));
    if (x == root.r) {
      assert x.p == root;
      assert x.p in node_set(root);
    } else {
      parent_is_in_set(root.r, x);
    }
  }
}

lemma parent_is_valid(root: Node, x: Node)
requires is_valid_node(root)
requires x in node_set(root)
requires x != root
ensures is_valid_node(x.p)
{
  descendant_has_p_not_null(root, x);
  parent_is_in_set(root, x);
  valid_subtree_is_valid(root, x.p);
}

lemma descendant_has_p_not_null(root: Node, x: Node)
requires is_valid_node(root)
requires x in node_set(root)
requires x != root
decreases |node_set(root)|
ensures x.p != null
{
  if (x in node_set(root.l)) {
    if (x == root.l) {
      assert x.p == root;
    } else {
      descendant_has_p_not_null(root.l, x);
    }
  } else {
    if (x == root.r) {
      assert x.p == root;
    } else {
      descendant_has_p_not_null(root.r, x);
    }
  }
}

lemma p_null_implies_root(root: Node, x: Node)
requires is_valid_node(root)
requires x in node_set(root)
requires root.p == null
requires x.p == null
ensures root == x
{
  if (root != x) {
    non_root_has_parent(root, x);
  }
}

lemma non_root_has_parent(root: Node, x: Node)
requires is_valid_node(root)
requires x in node_set(root)
requires x != root
decreases |node_set(root)|
ensures x.p != null
{
  assert x in {root} + node_set(root.l) + node_set(root.r);
  if (root == x) {
  } else if (x in node_set(root.l)) {
    if (root.l == x) {
      assert x.p == root;
    } else {
      non_root_has_parent(root.l, x);
    }
  } else {
    assert (x in node_set(root.r));
    if (root.r == x) {
      assert x.p == root;
    } else {
      non_root_has_parent(root.r, x);
    }
  }
}

lemma parent_of_valid_node_is_valid(root: Node, x: Node, p: Node)
requires is_valid_node(root)
requires x in node_set(root)
requires root.p == null
requires x.p == p
ensures is_valid_node(p)
decreases |node_set(root)|
{
  if (x == root) {
  } else if (x in node_set(root.l)) {
    assert root.l != null;
    assert root.l.p == root
        != x;
    parent_of_valid_node_is_valid1(root, root.l, x, p);
  } else {
    assert x in node_set(root.r);
    parent_of_valid_node_is_valid1(root, root.r, x, p);
  }
}

lemma parent_of_valid_node_is_valid1(root_p: Node, root: Node, x: Node, p: Node)
requires is_valid_node(root_p)
requires is_valid_node(root)
requires root.p == root_p
requires x in node_set(root)
requires root.p != x
requires x.p == p
ensures is_valid_node(p)
decreases |node_set(root)|
{
  if (x == root) {
  } else if (x in node_set(root.l)) {
    parent_of_valid_node_is_valid1(root, root.l, x, p);
  } else {
    parent_of_valid_node_is_valid1(root, root.r, x, p);
  }
}

lemma valid_subtree_is_valid(root: Node, node: Node)
requires is_valid_node(root)
requires node in node_set(root)
decreases |node_set(root)|
ensures is_valid_node(node)
{
  assert node_set(root) == {root} + node_set(root.l) + node_set(root.r);
  assert node in ({root} + node_set(root.l) + node_set(root.r));
  if (node == root) {
    assert is_structurally_valid(node);
  } else if (node in node_set(root.l)) {
    valid_subtree_is_valid(root.l, node);
  } else {
    valid_subtree_is_valid(root.r, node);
  }
}

lemma does_not_contain_grandparent(x: Node?, p: Node, g: Node)
requires is_valid_node(g)
requires g.l == p || g.r == p
requires p.l == x || p.r == x
ensures g !in node_set(x)
{
  does_not_contain_parent(p, g);
  assert node_set(x) <= node_set(p);
}

lemma does_not_contain_parent(x: Node?, p: Node)
requires is_valid_node(p)
requires p.l == x || p.r == x
ensures p !in node_set(x)
{
  not_in_children(p);
}

lemma not_in_children(a: Node)
requires is_structurally_valid(a)
ensures a !in node_set(a.l)
ensures a !in node_set(a.r)
{
  if (a in node_set(a.l)) {
    subtree_set_size_is_less(a.l, a);
  }
  if (a in node_set(a.r)) {
    subtree_set_size_is_less(a.r, a);
  }
}

lemma subtree_set_size_is_less(root: Node, node: Node)
requires is_structurally_valid(root)
requires node in node_set(root.l) || node in node_set(root.r)
decreases |node_set(root)|
ensures |node_set(node)| < |node_set(root)|
{
  if (node in node_set(root.l)) {
    assert root.l != null;
    assert node in ({root.l} + node_set(root.l.l) + node_set(root.l.r));
    if (node == root.l) {
    } else if (node in node_set(root.l.l)) {
      subtree_set_size_is_less(root.l, node);
    } else {
      subtree_set_size_is_less(root.l, node);
    }
  } else {
    assert root.r != null;
    assert node in ({root.r} + node_set(root.r.l) + node_set(root.r.r));
    if (node == root.r) {
    } else if (node in node_set(root.r.l)) {
      subtree_set_size_is_less(root.r, node);
    } else {
      subtree_set_size_is_less(root.r, node);
    }
  }
}

lemma left_not_in_right(p: Node)
requires is_valid_node(p)
ensures p.l !in node_set(p.r)
{
  if (p.l != null) {
    sides_disjoint_not_in_right(p, p.l);
  }
}

lemma right_not_in_left(p: Node)
requires is_valid_node(p)
ensures p.r !in node_set(p.l)
{
  if (p.r != null) {
    sides_disjoint_not_in_left(p, p.r);
  }
}

lemma sides_disjoint_not_in_left(a: Node, b: Node)
requires is_valid_node(a)
requires b in node_set(a.r)
ensures b !in node_set(a.l)
{
  if (b in node_set(a.l)) {
    sides_disjoint(a, b, b);
    assert b != b;
    assert false;
  }
}

lemma sides_disjoint_not_in_right(a: Node, b: Node)
requires is_valid_node(a)
requires b in node_set(a.l)
ensures b !in node_set(a.r)
{
  if (b in node_set(a.r)) {
    sides_disjoint(a, b, b);
    assert b != b;
    assert false;
  }
}

lemma sides_disjoint(a: Node, b: Node, c: Node)
requires is_valid_node(a)
requires b in node_set(a.l)
requires c in node_set(a.r)
ensures b != c
{
  if (b == c) {
    node_set_to_value_set(b, a.l);
    node_set_to_value_set(c, a.r);
    assert b.value in value_set(a.l);
    assert c.value in value_set(a.r);
    assert (forall t: uint64 :: t in value_set(a.l) ==> t < a.value);
    assert b.value < a.value;
    assert (forall t: uint64 :: t in value_set(a.r) ==> t > a.value);
    assert c.value > a.value;
    assert false;
  }
}

lemma node_set_to_value_set(a: Node, b: Node)
requires is_structurally_valid(b)
requires a in node_set(b)
ensures a.value in value_set(b)
{
  lemma_value_set_matches_node_set(b);
}

lemma lemma_value_set_matches_node_set(root: Node?)
requires is_structurally_valid(root)
decreases |node_set(root)|
ensures forall v: Node :: v in node_set(root) ==> v.value in value_set(root)
ensures forall val: uint64 :: val in value_set(root) ==> exists v: Node :: v.value == val
{
  if (root != null) {
    lemma_value_set_matches_node_set(root.l);
    lemma_value_set_matches_node_set(root.r);
  }
}

predicate
{:fuel 0,0}
is_valid_other_than_self(x: Node, value: uint64, l: Node?, r: Node?, ns: set<Node>,
    ns1: set<Node>, vs: set<uint64>)
reads ns1
{
  (l == null || l in ns) &&
  (r == null || r in ns) &&
  (l == null || l in ns1) &&
  (r == null || r in ns1) &&
  |node_set(l)| < |ns| &&
  |node_set(r)| < |ns| &&
  ns == {x} + node_set(l) + node_set(r) &&
  node_set(l) <= ns1 &&
  node_set(r) <= ns1 &&
  is_structurally_valid(l) &&
  is_structurally_valid(r) &&

  (l == null || l.p == x) &&
  (r == null || r.p == x) &&
  (forall t: uint64 :: t in value_set(l) ==> t < value) &&
  (forall t: uint64 :: t in value_set(r) ==> t > value) &&
  is_valid_node(l) &&
  is_valid_node(r) &&
  vs == {value} + value_set(l) + value_set(r)
}

lemma
{:fuel is_valid_other_than_self,1,2}
lemma_modify_p_doesnt_affect_validity1(x: Node, s: set<uint64>)
requires is_valid_node(x)
requires s == value_set(x)
ensures is_valid_other_than_self(x, x.value, x.l, x.r, x.node_set, x.node_set - {x}, s)
{
  node_is_not_in_valid_child_subtree(x);

  assert node_set(x.l) <= x.node_set;
  assert x !in node_set(x.l);
  assert node_set(x.l) <= x.node_set - {x};

  assert node_set(x.r) <= x.node_set;
  assert x !in node_set(x.r);
  assert node_set(x.r) <= x.node_set - {x};
}

lemma
{:fuel is_valid_other_than_self,1,2}
lemma_modify_p_doesnt_affect_validity2(x: Node, s: set<uint64>)
requires is_valid_other_than_self(x, x.value, x.l, x.r, x.node_set, x.node_set - {x}, s)
ensures is_valid_node(x)
ensures s == value_set(x)
{

}

lemma left_ne_right(x: Node)
requires is_valid_node(x)
ensures x.l != x.r || x.l == null || x.r == null
{
  if (x.l != null && x.r != null) {
    assert x.l.value in value_set(x.l);
    assert x.r.value in value_set(x.r);
    assert x.l.value < x.value;
    assert x.r.value > x.value;
    assert x.l.value != x.r.value;
  }
}

lemma self_ne_right(x: Node)
requires is_valid_node(x)
ensures x != x.r
{
}

lemma self_ne_left(x: Node)
requires is_valid_node(x)
ensures x != x.l
{
}

lemma self_ne_parent1(x: Node, root: Node)
requires is_valid_node(root)
requires x in node_set(root)
requires root.p == null
ensures x.p != x
{
  if (x.p == null) {
  } else {
    self_ne_parent(x, root);
  }
}

lemma self_ne_parent(x: Node, root: Node)
requires is_valid_node(root)
requires x in node_set(root)
requires x != root
ensures x.p != x
{
  if (x.p != null) {
    is_one_of_parents_children(root, x);
    parent_is_valid(root, x);
    assert x.p.l == x || x.p.r == x;
    self_ne_right(x.p);
    self_ne_left(x.p);
  }
}

lemma self_ne_greatgrandparent(x: Node, root: Node)
requires is_valid_node(root)
requires x in node_set(root)
requires x.p != null
requires x.p.p != null
requires root.p == null
ensures x.p.p.p != x
{
  if (x.p.p == root) {
  } else if (x.p.p.p != null) {
    is_one_of_parents_children(root, x);
    parent_is_valid(root, x);
    parent_is_in_set(root, x);
    is_one_of_parents_children(root, x.p);
    parent_is_valid(root, x.p);
    parent_is_in_set(root, x.p);
    is_one_of_parents_children(root, x.p.p);
    parent_is_valid(root, x.p.p);
    assert x in node_set(x.p.p.p.l) || x in node_set(x.p.p.p.r);
    not_in_children(x.p.p.p);
    assert !(x.p.p.p in node_set(x.p.p.p.l) || x.p.p.p in node_set(x.p.p.p.r));
    assert x.p.p.p != x;
  }
}

lemma self_ne_grandparent1(x: Node, root: Node)
requires is_valid_node(root)
requires x in node_set(root)
requires x.p != null
requires root.p == null
ensures x.p.p != x
{
  if (x.p == root) {
  } else {
    assert x != root;
    self_ne_grandparent(x, root);
  }
}

lemma self_ne_grandparent(x: Node, root: Node)
requires is_valid_node(root)
requires x in node_set(root)
requires x != root
requires x.p != null
requires x.p != root
ensures x.p.p != x
{
  if (x.p != null && x.p.p != null) {
    is_one_of_parents_children(root, x);
    parent_is_valid(root, x);
    parent_is_in_set(root, x);
    is_one_of_parents_children(root, x.p);
    parent_is_valid(root, x.p);
    assert x in node_set(x.p.p.l) || x in node_set(x.p.p.r);
    not_in_children(x.p.p);
    assert !(x.p.p in node_set(x.p.p.l) || x.p.p in node_set(x.p.p.r));
    assert x.p.p != x;
  }
}

lemma self_ne_lr(x: Node, root: Node)
requires is_valid_node(root)
requires x in node_set(root)
requires x.l != null
ensures x.l.r != x
{
  valid_subtree_is_valid(root, x);
  assert is_valid_node(x.l);
  assert is_valid_node(x.l.r);
  if (x.l.r != null) {
    self_ne_grandparent(x.l.r, x);
  }
}

lemma self_ne_rl(x: Node, root: Node)
requires is_valid_node(root)
requires x in node_set(root)
requires x.r != null
ensures x.r.l != x
{
  valid_subtree_is_valid(root, x);
  assert is_valid_node(x.r);
  assert is_valid_node(x.r.l);
  if (x.r.l != null) {
    self_ne_grandparent(x.r.l, x);
  }
}

lemma grandchild_ne_left(x: Node, ch: Node)
requires is_valid_node(x)
requires x.r != null
requires ch == x.r.l || ch == x.r.r
ensures ch != x.l
{
}

lemma grandchild_ne_right(x: Node, ch: Node)
requires is_valid_node(x)
requires x.l != null
requires ch == x.l.l || ch == x.l.r
ensures ch != x.r
{
}

lemma grandchild_not_in_left(x: Node, ch: Node)
requires is_valid_node(x)
requires x.r != null
requires ch == x.r.l || ch == x.r.r
ensures ch !in node_set(x.l)
{
  assert ch.value in value_set(x.r.l) || ch.value in value_set(x.r.r);
  assert ch.value in value_set(x.r);
  assert ch.value > x.value;
  if (ch in node_set(x.l)) {
    node_set_to_value_set(ch, x.l);
    assert ch.value in value_set(x.l);
    assert ch.value < x.value;
    assert ch.value != ch.value;
    assert false;
  }
}

lemma grandchild_not_in_right(x: Node, ch: Node)
requires is_valid_node(x)
requires x.l != null
requires ch == x.l.l || ch == x.l.r
ensures ch !in node_set(x.r)
{
  assert ch.value in value_set(x.l.l) || ch.value in value_set(x.l.r);
  assert ch.value in value_set(x.l);
  assert ch.value < x.value;
  if (ch in node_set(x.r)) {
    node_set_to_value_set(ch, x.r);
    assert ch.value in value_set(x.r);
    assert ch.value > x.value;
    assert ch.value != ch.value;
    assert false;
  }
}

lemma greatgrandchild_not_in_left(x: Node, ch: Node?)
requires is_valid_node(x)
requires x.r != null
requires (x.r.l != null && (x.r.l.l == ch || x.r.l.r == ch)) ||
         (x.r.r != null && (x.r.r.l == ch || x.r.r.r == ch))
ensures ch !in node_set(x.l)
{
  if (ch != null) {
    assert ch.value in value_set(x.r.l) || ch.value in value_set(x.r.r);
    assert ch.value in value_set(x.r);
    assert ch.value > x.value;
    if (ch in node_set(x.l)) {
      node_set_to_value_set(ch, x.l);
      assert ch.value in value_set(x.l);
      assert ch.value < x.value;
      assert ch.value != ch.value;
      assert false;
    }
  }
}

lemma greatgrandchild_not_in_right(x: Node, ch: Node?)
requires is_valid_node(x)
requires x.l != null
requires (x.l.l != null && (x.l.l.l == ch || x.l.l.r == ch)) ||
         (x.l.r != null && (x.l.r.l == ch || x.l.r.r == ch))
ensures ch !in node_set(x.r)
{
  if (ch != null) {
    assert ch.value in value_set(x.l.l) || ch.value in value_set(x.l.r);
    assert ch.value in value_set(x.l);
    assert ch.value < x.value;
    if (ch in node_set(x.r)) {
      node_set_to_value_set(ch, x.r);
      assert ch.value in value_set(x.r);
      assert ch.value > x.value;
      assert ch.value != ch.value;
      assert false;
    }
  }
}

lemma right_grandchild_set_gt_self(x: Node, ch: Node?)
requires is_valid_node(x)
requires x.r != null
requires ch == x.r.l || ch == x.r.r
ensures is_structurally_valid(ch)
ensures (forall t: uint64 :: t in value_set(ch) ==> t > x.value)
{
  assert value_set(ch) <= value_set(x.r);
  assert (forall t: uint64 :: t in value_set(x.r) ==> t > x.value);
}

lemma left_grandchild_set_lt_self(x: Node, ch: Node?)
requires is_valid_node(x)
requires x.l != null
requires ch == x.l.l || ch == x.l.r
ensures is_structurally_valid(ch)
ensures (forall t: uint64 :: t in value_set(ch) ==> t < x.value)
{
  assert value_set(ch) <= value_set(x.l);
  assert (forall t: uint64 :: t in value_set(x.l) ==> t < x.value);
}

lemma left_child_lt_self(x: Node)
requires is_valid_node(x)
requires x.l != null
ensures x.l.value < x.value
{
  assert x.l.value in value_set(x.l);
}

lemma right_child_gt_self(x: Node)
requires is_valid_node(x)
requires x.r != null
ensures x.r.value > x.value
{
  assert x.r.value in value_set(x.r);
}

lemma coalesce_right_subtree_all_gt(x: Node)
requires x.r != null
requires is_valid_node(x.r)
requires x.r.value > x.value
requires (forall t: uint64 :: t in value_set(x.r.l) ==> t > x.value)
ensures (forall t: uint64 :: t in value_set(x.r) ==> t > x.value)
{
}

lemma coalesce_left_subtree_all_lt(x: Node)
requires x.l != null
requires is_valid_node(x.l)
requires x.l.value < x.value
requires (forall t: uint64 :: t in value_set(x.l.r) ==> t < x.value)
ensures (forall t: uint64 :: t in value_set(x.l) ==> t < x.value)
{
}

lemma get_node_set(x: Node)
requires is_structurally_valid(x)
ensures node_set(x) == {x} + node_set(x.l) + node_set(x.r)
{
}

lemma child_set_size_le(root: Node, node: Node)
requires is_valid_node(root)
requires node in node_set(root)
decreases |node_set(root)|
ensures |node_set(root)| >= |node_set(node)|
{
  if (node == root) {
  } else if (node in node_set(root.l)) {
    child_set_size_le(root.l, node);
  } else {
    child_set_size_le(root.r, node);
  }
}

lemma right_is_in_node_set(x: Node)
requires is_valid_node(x)
requires x.r != null
ensures x.r in node_set(x)
{
}

lemma left_is_in_node_set(x: Node)
requires is_valid_node(x)
requires x.l != null
ensures x.l in node_set(x)
{
}

lemma parent_not_in_r1(x: Node, root: Node)
requires is_valid_node(root)
requires x in node_set(root)
requires root.p == null
ensures x.p !in node_set(x.r)
{
  if (x == root) {
  } else {
    parent_not_in_r(x, root);
  }
}

lemma parent_not_in_l1(x: Node, root: Node)
requires is_valid_node(root)
requires x in node_set(root)
requires root.p == null
ensures x.p !in node_set(x.l)
{
  if (x == root) {
  } else {
    parent_not_in_l(x, root);
  }
}

lemma parent_not_in_r(x: Node, root: Node)
requires is_valid_node(root)
requires x in node_set(root)
requires x != root
ensures x.p !in node_set(x.r)
{
  if (x.p != null) {
    parent_is_valid(root, x);
    is_one_of_parents_children(root, x);
    not_in_children(x.p);
    if (x.p.l == x) {
      assert x.p !in node_set(x.p.l);
      assert x.p !in node_set(x.p.l.r);
    } else {
      assert x.p !in node_set(x.p.r);
      assert x.p !in node_set(x.p.r.r);
    }
  }
}

lemma parent_not_in_l(x: Node, root: Node)
requires is_valid_node(root)
requires x in node_set(root)
requires x != root
ensures x.p !in node_set(x.l)
{
  if (x.p != null) {
    parent_is_valid(root, x);
    is_one_of_parents_children(root, x);
    not_in_children(x.p);
    if (x.p.l == x) {
      assert x.p !in node_set(x.p.l);
      assert x.p !in node_set(x.p.l.l);
    } else {
      assert x.p !in node_set(x.p.r);
      assert x.p !in node_set(x.p.r.l);
    }
  }
}

lemma parent_ne_ll(x: Node, root: Node)
requires is_valid_node(root)
requires x in node_set(root)
requires x != root
requires x.l != null
ensures x.p != x.l.l
{
  valid_subtree_is_valid(root, x);
  descendant_has_p_not_null(root, x);
  assert x.p != null;
  if (x.l.l != null) {
    assert is_valid_node(x.l);
    assert x.l.l in node_set(x.l);
    parent_not_in_l(x, root);
  }
}

lemma parent_ne_rr(x: Node, root: Node)
requires is_valid_node(root)
requires x in node_set(root)
requires x != root
requires x.r != null
ensures x.p != x.r.r
{
  valid_subtree_is_valid(root, x);
  descendant_has_p_not_null(root, x);
  assert x.p != null;
  if (x.r.r != null) {
    assert is_valid_node(x.r);
    assert x.r.r in node_set(x.r);
    parent_not_in_r(x, root);
  }
}

lemma parent_ne_lr(x: Node, root: Node)
requires is_valid_node(root)
requires x in node_set(root)
requires x != root
requires x.l != null
ensures x.p != x.l.r
{
  valid_subtree_is_valid(root, x);
  descendant_has_p_not_null(root, x);
  assert x.p != null;
  if (x.l.r != null) {
    assert is_valid_node(x.l);
    assert x.l.r in node_set(x.l);
    parent_not_in_l(x, root);
  }
}

lemma parent_ne_rl(x: Node, root: Node)
requires is_valid_node(root)
requires x in node_set(root)
requires x != root
requires x.r != null
ensures x.p != x.r.l
{
  valid_subtree_is_valid(root, x);
  descendant_has_p_not_null(root, x);
  assert x.p != null;
  if (x.r.l != null) {
    assert is_valid_node(x.r);
    assert x.r.l in node_set(x.r);
    parent_not_in_r(x, root);
  }
}

lemma parent_not_in_ll(x: Node, root: Node)
requires is_valid_node(root)
requires x in node_set(root)
requires root.p == null
requires x.l != null
ensures x.p !in node_set(x.l.l)
{
  if (x == root) {
  } else {
    valid_subtree_is_valid(root, x);
    descendant_has_p_not_null(root, x);
    assert x.p != null;
    if (x.l.l != null) {
      assert is_valid_node(x.l);
      assert x.l.l in node_set(x.l);
      parent_not_in_l(x, root);
    }
  }
}

lemma parent_not_in_rr(x: Node, root: Node)
requires is_valid_node(root)
requires x in node_set(root)
requires root.p == null
requires x.r != null
ensures x.p !in node_set(x.r.r)
{
  if (x != root) {
    valid_subtree_is_valid(root, x);
    descendant_has_p_not_null(root, x);
    assert x.p != null;
    if (x.r.r != null) {
      assert is_valid_node(x.r);
      assert x.r.r in node_set(x.r);
      parent_not_in_r(x, root);
    }
  }
}

lemma parent_not_in_lr(x: Node, root: Node)
requires is_valid_node(root)
requires x in node_set(root)
requires root.p == null
requires x.l != null
ensures x.p !in node_set(x.l.r)
{
  if (x != root) {
    valid_subtree_is_valid(root, x);
    descendant_has_p_not_null(root, x);
    assert x.p != null;
    if (x.l.r != null) {
      assert is_valid_node(x.l);
      assert x.l.r in node_set(x.l);
      parent_not_in_l(x, root);
    }
  }
}

lemma parent_not_in_rl(x: Node, root: Node)
requires is_valid_node(root)
requires x in node_set(root)
requires root.p == null
requires x.r != null
ensures x.p !in node_set(x.r.l)
{
  if (x != root) {
    valid_subtree_is_valid(root, x);
    descendant_has_p_not_null(root, x);
    assert x.p != null;
    if (x.r.l != null) {
      assert is_valid_node(x.r);
      assert x.r.l in node_set(x.r);
      parent_not_in_r(x, root);
    }
  }
}

lemma parent_ne_right(x: Node, root: Node)
requires is_valid_node(root)
requires x in node_set(root)
requires x != root
ensures x.p != x.r
{
  valid_subtree_is_valid(root, x);
  descendant_has_p_not_null(root, x);
  assert x.p != null;
  if (x.r != null) {
    assert is_valid_node(x.r);
    assert x.r in node_set(x.r);
    parent_not_in_r(x, root);
  }
}

lemma parent_ne_left(x: Node, root: Node)
requires is_valid_node(root)
requires x in node_set(root)
requires x != root
ensures x.p != x.l
{
  valid_subtree_is_valid(root, x);
  descendant_has_p_not_null(root, x);
  assert x.p != null;
  if (x.l != null) {
    assert is_valid_node(x.l);
    assert x.l in node_set(x.l);
    parent_not_in_l(x, root);
  }
}

predicate
{:fuel 0,0}
is_structurally_valid_other_than_subtree(
    a: Node?,
    f: Node,
    fs: set<Node>,
    fsv: set<uint64>,
    fp: Node?,
    other_nodes: set<Node>)
reads other_nodes
decreases |if a == f then fs else node_set(a)|
{
  if (a == null || a == f) then
    true
  else (
    a in other_nodes &&
    (a.l == null || a.l in a.node_set) &&
    (a.r == null || a.r in a.node_set) &&
    (a.l == null || a.l == f || a.l in other_nodes) &&
    (a.r == null || a.r == f || a.r in other_nodes) &&
    |if a.l == f then fs else node_set(a.l)| < |a.node_set| &&
    |if a.r == f then fs else node_set(a.r)| < |a.node_set| &&
    a.node_set == {a} + (if a.l == f then fs else node_set(a.l)) +
                        (if a.r == f then fs else node_set(a.r)) &&
    is_structurally_valid_other_than_subtree(a.l, f, fs, fsv, fp, other_nodes) &&
    is_structurally_valid_other_than_subtree(a.r, f, fs, fsv, fp, other_nodes)
  )
}

function
{:fuel 0,0}
{:fuel is_structurally_valid_other_than_subtree,1,2}
value_set_other_than_subtree(
    a: Node?,
    f: Node,
    fs: set<Node>,
    fsv: set<uint64>,
    fp: Node?,
    other_nodes: set<Node>): set<uint64>
reads other_nodes
requires is_structurally_valid_other_than_subtree(a, f, fs, fsv, fp, other_nodes)
decreases |if a == f then fs else node_set(a)|
{
  if (a == null) then (
    {}
  ) else if (a == f) then (
    fsv
  ) else (
    {a.value} + value_set_other_than_subtree(a.l, f, fs, fsv, fp, other_nodes)
              + value_set_other_than_subtree(a.r, f, fs, fsv, fp, other_nodes)
  )
}

predicate
{:fuel 0,0}
{:fuel is_structurally_valid_other_than_subtree,1,2}
is_valid_node_other_than_subtree(
    a: Node?,
    f: Node,
    fs: set<Node>,
    fsv: set<uint64>,
    fp: Node?,
    other_nodes: set<Node>)
reads other_nodes
decreases |if a == f then fs else node_set(a)|
{
  is_structurally_valid_other_than_subtree(a,f,fs,fsv,fp,other_nodes) && (
    if (a == null || a == f) then
      true
    else (
      (a.l == null || (if a.l == f then fp else a.l.p) == a) &&
      (a.r == null || (if a.r == f then fp else a.r.p) == a) &&
      (forall t: uint64 :: t in value_set_other_than_subtree(a.l,f,fs,fsv,fp,other_nodes) ==>
          t < a.value) &&
      (forall t: uint64 :: t in value_set_other_than_subtree(a.r,f,fs,fsv,fp,other_nodes) ==>
          t > a.value) &&
      is_valid_node_other_than_subtree(a.l,f,fs,fsv,fp,other_nodes) &&
      is_valid_node_other_than_subtree(a.r,f,fs,fsv,fp,other_nodes)
    )
  )
}

predicate
{:fuel 0,0}
{:fuel is_structurally_valid_other_than_subtree,1,2}
is_valid_and_matches(
    a: Node?,
    f: Node,
    fs: set<Node>,
    fsv: set<uint64>,
    fp: Node?,
    other_nodes: set<Node>,
    all_nodes: set<Node>,
    all_values: set<uint64>)
reads other_nodes
{
  is_valid_node_other_than_subtree(a,f,fs,fsv,fp,other_nodes) &&
  value_set_other_than_subtree(a,f,fs,fsv,fp,other_nodes) == all_values &&
  (if a == f then fs else node_set(a)) == all_nodes
}

lemma
{:fuel is_structurally_valid_other_than_subtree,1,2}
{:fuel value_set_other_than_subtree,1,2}
{:fuel is_valid_node_other_than_subtree,1,2}
{:fuel is_valid_and_matches,1,2}
change_subtree_preserves_validity1(
  root: Node,
  f: Node,
  full_node_set: set<Node>,
  full_value_set: set<uint64>,
  fsn: set<Node>,
  fsv: set<uint64>,
  fp: Node?,
  other_nodes: set<Node>)
requires is_valid_node(root)
requires is_valid_node(f)
requires f in node_set(root)
requires node_set(root) == full_node_set
requires value_set(root) == full_value_set
requires node_set(f) == fsn
requires value_set(f) == fsv
requires f.p == fp
requires other_nodes == node_set(root) - node_set(f)
ensures is_valid_and_matches(root, f, fsn, fsv, fp, other_nodes, full_node_set, full_value_set)
{
  if (root != f) {
    node_is_not_in_descendant_subtree(root, f);
    assert root !in node_set(f);
    change_subtree_preserves_validity1_(root,f,full_node_set,full_value_set,
        fsn,fsv,fp,other_nodes);
  }
}

lemma
{:fuel is_structurally_valid_other_than_subtree,1,2}
{:fuel value_set_other_than_subtree,1,2}
{:fuel is_valid_node_other_than_subtree,1,2}
{:fuel is_valid_and_matches,1,2}
change_subtree_preserves_validity2(
  root: Node,
  f: Node,
  full_node_set: set<Node>,
  full_value_set: set<uint64>,
  fsn: set<Node>,
  fsv: set<uint64>,
  fp: Node?,
  other_nodes: set<Node>)
requires is_valid_and_matches(root, f, fsn, fsv, fp, other_nodes, full_node_set, full_value_set)
requires is_valid_node(f)
requires node_set(f) == fsn
requires value_set(f) == fsv
requires f.p == fp
ensures is_valid_node(root)
ensures node_set(root) == full_node_set
ensures value_set(root) == full_value_set
decreases |if root == f then fsn else node_set(root)|
{
  if (root == f) {
  } else {
    assert value_set_other_than_subtree(root, f, fsn, fsv, fp, other_nodes) == 
      {root.value} + value_set_other_than_subtree(root.l, f, fsn, fsv, fp, other_nodes)
                   + value_set_other_than_subtree(root.r, f, fsn, fsv, fp, other_nodes);
    assert node_set(root) ==
      {root} + (if root.l == f then fsn else node_set(root.l)) +
               (if root.r == f then fsn else node_set(root.r));

    if (root.l != null) {
      change_subtree_preserves_validity2(root.l, f, 
          (if root.l == f then fsn else node_set(root.l)),
          value_set_other_than_subtree(root.l, f, fsn, fsv, fp, other_nodes),
          fsn, fsv, fp, other_nodes);
    }
    if (root.r != null) {
      change_subtree_preserves_validity2(root.r, f, 
          (if root.r == f then fsn else node_set(root.r)),
          value_set_other_than_subtree(root.r, f, fsn, fsv, fp, other_nodes),
          fsn, fsv, fp, other_nodes);
    }
  }
}

lemma
{:fuel is_structurally_valid_other_than_subtree,1,2}
{:fuel value_set_other_than_subtree,1,2}
{:fuel is_valid_node_other_than_subtree,1,2}
{:fuel is_valid_and_matches,1,2}
change_subtree_preserves_validity1_(
  root: Node?,
  f: Node,
  full_node_set: set<Node>,
  full_value_set: set<uint64>,
  fsn: set<Node>,
  fsv: set<uint64>,
  fp: Node?,
  other_nodes: set<Node>)
requires is_valid_node(root)
requires is_valid_node(f)
requires root != f ==> root !in node_set(f)
requires node_set(root) == full_node_set
requires value_set(root) == full_value_set
requires node_set(f) == fsn
requires value_set(f) == fsv
requires f.p == fp
requires other_nodes >= node_set(root) - node_set(f)
decreases |node_set(root)|
ensures is_valid_and_matches(root, f, fsn, fsv, fp, other_nodes, full_node_set, full_value_set)
{
  if (root != null) {
    if (root != f) {
      assert root in node_set(root);
      assert root in other_nodes;
      not_in_implies_child_not_in(root, f);
      if (root.l != f) {
        assert root.l !in node_set(f);
      }
      if (root.r != f) {
        assert root.r !in node_set(f);
      }
      change_subtree_preserves_validity1_(root.l, f, node_set(root.l), value_set(root.l),
          fsn, fsv, fp, other_nodes);
      change_subtree_preserves_validity1_(root.r, f, node_set(root.r), value_set(root.r),
        fsn, fsv, fp, other_nodes);
    }
  }
}

lemma not_in_implies_child_not_in(x: Node, f: Node)
requires is_valid_node(x)
requires is_valid_node(f)
requires x !in node_set(f)
ensures x.l != f ==> x.l !in node_set(f)
ensures x.r != f ==> x.r !in node_set(f)
{
  if (x.l != f && x.l in node_set(f)) {
    assert x.l.p == x;
    parent_is_in_set(f, x.l);
    assert x in node_set(f);
    assert false;
  }
  if (x.r != f && x.r in node_set(f)) {
    assert x.r.p == x;
    parent_is_in_set(f, x.r);
    assert x in node_set(f);
    assert false;
  }
}

lemma self_in_set(x: Node)
requires is_valid_node(x)
ensures x in node_set(x)
{
}

lemma child_in_set(x: Node, c: Node)
requires is_valid_node(x)
requires x.l == c || x.r == c
ensures c in node_set(x)
{
}

lemma grandchild_in_set(x: Node, b: Node, c: Node)
requires is_valid_node(x)
requires x.l == b || x.r == b
requires b.l == c || b.r == c
ensures c in node_set(x)
{
}

lemma greatgrandchild_in_set(x: Node, a: Node, b: Node, c: Node)
requires is_valid_node(x)
requires x.l == a || x.r == a
requires a.l == b || a.r == b
requires b.l == c || b.r == c
ensures c in node_set(x)
{
  assert is_valid_node(a);
  assert is_valid_node(b);
  assert is_valid_node(c);
  assert c in node_set(c);
  assert c in node_set(b);
  assert c in node_set(a);
  assert c in node_set(x);
}

lemma l_node_set_le_node_set(node: Node)
requires is_structurally_valid(node)
ensures node_set(node.l) <= node_set(node)
{
}

lemma r_node_set_le_node_set(node: Node)
requires is_structurally_valid(node)
ensures node_set(node.r) <= node_set(node)
{
}

lemma get_value_set(node: Node)
requires is_structurally_valid(node)
ensures value_set(node) == {node.value} + value_set(node.l) + value_set(node.r)
{
}

lemma singleton_value_set(node: Node)
requires is_structurally_valid(node)
requires node.l == null
requires node.r == null
ensures value_set(node) == {node.value}
{
}

lemma null_value_set()
ensures value_set(null) == {}
{
}

lemma sides_disjoint_forall(a: Node)
requires is_valid_node(a)
ensures forall b:Node :: b in node_set(a.l) ==>
        forall c:Node :: c in node_set(a.r) ==>
        b != c
{
  if (!(forall b:Node :: b in node_set(a.l) ==>
         forall c:Node :: c in node_set(a.r) ==> b != c)) {
    assert exists b:Node :: b in node_set(a.l) &&
           exists c:Node :: c in node_set(a.r) && b == c;
    var b:Node :| b in node_set(a.l) &&
           exists c:Node :: c in node_set(a.r) && b == c;
    var c:Node :| c in node_set(a.r) && b == c;

    sides_disjoint(a, b, c);
    assert false;
  }
}

lemma right_is_gt(node: Node)
requires is_valid_node(node)
requires node.r != null
ensures node.r.value > node.value
{
  assert node.r.value in value_set(node.r);
}
