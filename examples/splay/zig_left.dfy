method
{:fuel is_structurally_valid,0,0}
{:fuel value_set,0,0}
zig_left(x: Node, p: Node, ghost root: Node, ghost full_value_set: set<int>, ghost ns: set<Node>, ghost nsr: set<Node>, ghost gg:Node?)
modifies x
modifies p
modifies x.r
modifies gg
requires root.p == null
requires is_valid_node(root)
requires x in node_set(root)
requires value_set(root) == full_value_set
requires ns == node_set(x)
requires nsr == node_set(root)
requires x.p == p
requires p.l == x
requires gg == p.p
ensures x.p == gg
ensures is_valid_node(x)
ensures is_valid_node(root)
ensures gg == null ==> value_set(x) == full_value_set
ensures gg == null ==> node_set(x) == nsr
ensures gg != null ==> value_set(root) == full_value_set
ensures gg != null ==> node_set(root) == nsr
ensures gg != null ==> x in node_set(root)
ensures gg != null ==> root.p == null
ensures x.l == old(x.l)
ensures p.r == old(p.r)
ensures x.value == old(x.value)
ensures p.value == old(p.value)
ensures gg != null ==> gg.value == old(gg.value)
ensures gg != null ==> gg.p == old(gg.p)
ensures x.r == p
ensures x.value == old(x.value)
ensures |node_set(x)| > |ns|
{
  var b := x.r;

  valid_subtree_is_valid(root, x);
  assert is_valid_node(x);
  parent_of_valid_node_is_valid(root, x, p);
  assert is_valid_node(p);

  self_ne_parent(x, root); assert x != p;
  assert x != b;
  parent_is_in_set(root, x);
  self_ne_lr(p, root); assert p != b;
  self_ne_grandparent1(x, root); assert x != gg;
  self_ne_parent1(p, root); assert p != gg;
  if (gg != null) { 
    assert p != root;
    parent_ne_lr(p, root); assert b != gg;
  }

  assert is_valid_node(p.r);

  left_not_in_right(p); assert x !in node_set(p.r);
  does_not_contain_parent(p.r, p); assert p !in node_set(p.r);
  if (b != null) {grandchild_not_in_right(p, b);} assert b !in node_set(p.r);
  parent_not_in_r1(p, root); assert gg !in node_set(p.r);
  does_not_contain_parent(x.l, x); assert x !in node_set(x.l);
  does_not_contain_grandparent(x.l, x, p); assert p !in node_set(x.l);
  right_not_in_left(x); assert b !in node_set(x.l);
  parent_not_in_ll(p, root); assert gg !in node_set(x.l);
  does_not_contain_parent(b, x); assert x !in node_set(b);
  does_not_contain_grandparent(b, x, p); assert p !in node_set(b);
  parent_not_in_lr(p, root); assert gg !in node_set(b);
  left_ne_right(p); assert p.r != x;
  self_ne_right(p); assert p.r != p;
  if (b != null) {grandchild_ne_right(p, b); assert p.r != b;}
  if (gg != null) {parent_ne_right(p, root); assert p.r != gg;}
  if (gg != null) {parent_ne_ll(p, root); assert x.l != gg;}

  assert is_valid_node(b);
  assert x.l == null || x.l.p == x;
  assert is_structurally_valid(p.r);
  get_node_set(x); assert ns == {x} + node_set(x.l) + node_set(b);

  ghost var value_set_b := value_set(b);
  if (gg == null) {
    root_is_p(root, x, p);
    zig_left_value_set_is1(full_value_set, root, p, x, b);
    zig_left_node_set_is1(nsr, root, p, x, b);
  }

  left_grandchild_set_lt_self(p, b);
  left_child_lt_self(p);

  ghost var nsr := node_set(root);
  ghost var vsr := value_set(root);
  ghost var oset := nsr - node_set(gg);
  ghost var ggo;
  if (gg != null) {
    ggo := if gg.l == p then gg.r else gg.l;

    parent_is_in_set(root, p);
    parent_of_valid_node_is_valid(root, p, gg);
    is_one_of_parents_children(root, p);

    self_in_set(gg); assert gg in node_set(gg);
    child_in_set(gg, p); assert p in node_set(gg);
    grandchild_in_set(gg, p, x); assert x in node_set(gg);
    if (b != null) { greatgrandchild_in_set(gg, p, x, b); assert b in node_set(gg); }

    assert is_valid_node(ggo);
    not_in_children(gg);
    if (ggo == gg.r) { grandchild_not_in_right(gg, x); left_not_in_right(gg); greatgrandchild_not_in_right(gg, b); }
    else { grandchild_not_in_left(gg, x); right_not_in_left(gg); greatgrandchild_not_in_left(gg, b); }
    assert x !in node_set(ggo);
    assert p !in node_set(ggo);
    assert b !in node_set(ggo);
    assert gg !in node_set(ggo);
    assert x != ggo;
    left_ne_right(gg); assert p != ggo;
    if (ggo != null) { assert b != ggo; }
    assert gg != ggo;

    assert x !in oset;
    assert p !in oset;
    assert gg !in oset;
    assert b !in oset;

    change_subtree_preserves_validity1(root, gg, nsr, vsr,
        node_set(gg), value_set(gg), gg.p, oset);
  }
  ghost var nsgg := node_set(gg);
  ghost var vsgg := value_set(gg);
  ghost var p_then_x_vset := value_set(p);
  ghost var p_then_x_nset := node_set(p);
  if (gg != null) {
    unpack_gg(gg, p, ggo);
    assert vsgg == {gg.value} + value_set(p) + value_set(ggo);
    assert vsgg == {gg.value} + p_then_x_vset + value_set(ggo);
    zig_left_value_set_is1(p_then_x_vset, p, p, x, b);
    zig_left_node_set_is1(p_then_x_nset, p, p, x, b);
    gg_sets_prop1(gg, gg.r == ggo, p, ggo, p_then_x_vset, value_set(ggo));
    unpack_gg_nodes(gg, p, ggo);
    assert node_set(gg) == {gg} + node_set(p) + node_set(ggo)
        == {gg} + p_then_x_nset + node_set(ggo);
    grandchild_in_set(gg, p, x); assert x in node_set(gg);
  }

  x.r := p;
  p.l := b;
  x.p := p.p;
  p.p := x;

  assert is_valid_node(b);
  if (b != null) {
    lemma_modify_p_doesnt_affect_validity1(b, value_set_b);
    b.p := p;
    lemma_modify_p_doesnt_affect_validity2(b, value_set_b);
  }

  if (x.p != null) {
    assert gg == x.p;
    assert x.p !in node_set(p.r);
    assert x.p !in node_set(x.l);
    assert x.p !in node_set(b);
    assert x.p != b;
    assert x.p != p.r;
    assert x.p != x.l;

    if (x.p.l == p) {
      x.p.l := x;
    } else {
      x.p.r := x;
    }
  }

  assert is_structurally_valid(p.r);
  assert is_valid_node(p.r);
  assert is_valid_node(x.l);

  zig_left_fix_node_sets(x, p, b, ns);
  if (gg == null) {
    zig_left_value_set_is2(full_value_set, root, p, x, b);
    zig_left_node_set_is2(nsr, root, p, x, b);
  }

  assert is_valid_node(p);

  coalesce_right_subtree_all_gt(x);
  assert is_valid_node(x);

  if (gg != null) {
    assert is_valid_node(ggo);
    assert nsgg == node_set(gg);
    zig_left_node_set_is2(p_then_x_nset, p, p, x, b);
    assert node_set(gg) == {gg} + p_then_x_nset + node_set(ggo)
        == {gg} + node_set(x) + node_set(ggo);
    assert x in node_set(gg);
    if (ggo != null) { self_in_set(ggo); }
    assert ggo != null ==> ggo in node_set(gg);
    assert gg.l != null ==> gg.l in node_set(gg);
    assert gg.r != null ==> gg.r in node_set(gg);
    assert gg !in node_set(x);
    assert gg !in node_set(ggo);
    set_ineq(node_set(x), node_set(gg), gg);
    set_ineq(node_set(ggo), node_set(gg), gg);
    assert is_structurally_valid(gg);
    zig_left_value_set_is2(p_then_x_vset, p, p, x, b);
    gg_sets_prop2(gg, gg.r == ggo, x, ggo, p_then_x_vset, value_set(ggo));
    assert is_valid_node(gg);
    unpack_gg(gg, x, ggo);
    assert value_set(gg)
        == {gg.value} + value_set(x) + value_set(ggo)
        == {gg.value} + value_set(x) + value_set(ggo)
        == {gg.value} + p_then_x_vset + value_set(ggo)
        == vsgg;
    change_subtree_preserves_validity2(root, gg, nsr, vsr,
        node_set(gg), value_set(gg), gg.p, oset);
  }
}

ghost method zig_left_fix_node_sets(x: Node, p: Node, b: Node?, ns: set<Node>)
modifies x modifies p
requires ns == {x} + node_set(x.l) + node_set(b)
requires x.l == null || x.l.p == x
requires is_valid_node(x.l)
requires is_valid_node(p.r)
requires is_valid_node(b)
requires p.l == b
requires x.r == p
requires p !in node_set(x.l)
ensures is_structurally_valid(x)
ensures is_structurally_valid(p)
ensures |node_set(x)| > |ns|
{
  assert x != p;

  node_is_not_in_valid_child_subtree_rl(x);
  assert x !in node_set(p.l);
  node_is_not_in_valid_child_subtree_rr(x);
  assert x !in node_set(p.r);
  node_is_not_in_valid_child_subtree_right(p);
  assert p !in node_set(p.r);
  node_is_not_in_valid_child_subtree_left(x);
  assert x !in node_set(x.l);

  node_is_not_in_valid_child_subtree_left(p);
  assert p !in node_set(p.l);

  p.node_set := {p} + node_set(p.l) + node_set(p.r);
  x.node_set := {x} + node_set(x.l) + node_set(x.r);

  assert x !in node_set(x.r);
  set_ineq(node_set(x.r), x.node_set, x);

  assert x !in node_set(x.l);
  set_ineq(node_set(x.l), x.node_set, x);

  assert p !in node_set(p.l);
  set_ineq(node_set(p.l), p.node_set, p);

  assert p !in node_set(p.r);
  set_ineq(node_set(p.r), p.node_set, p);

  assert is_structurally_valid(p);
  assert is_structurally_valid(x);

  assert node_set(x) == {x} + node_set(x.l) + node_set(x.r)
      == {x} + node_set(x.l) + {p} + node_set(p.l) + node_set(p.r)
      >= ns;
  assert p !in ns;
  set_ineq(ns, node_set(x), p);
}

lemma zig_left_value_set_is1(full_value_set: set<int>, root: Node, p: Node, x: Node, b: Node?)
requires is_valid_node(p)
requires is_valid_node(x)
requires root == p;
requires p.l == x
requires x.r == b
requires is_valid_node(root)
requires value_set(root) == full_value_set
ensures full_value_set ==
    {p.value} + ({x.value} + value_set(x.l) + value_set(b)) + value_set(p.r)
{
  assert full_value_set
      == value_set(root)
      == value_set(p)
      == {p.value} + value_set(p.l) + value_set(p.r)
      == {p.value} + value_set(x) + value_set(p.r)
      == {p.value} + ({x.value} + value_set(x.l) + value_set(x.r)) + value_set(p.r)
      == {p.value} + ({x.value} + value_set(x.l) + value_set(b)) + value_set(p.r);
}

lemma zig_left_value_set_is2(full_value_set: set<int>, root: Node, p: Node, x: Node, b: Node?)
requires is_valid_node(b)
requires is_valid_node(p.r)
requires is_valid_node(x.l)
requires is_structurally_valid(x)
requires x.r == p
requires p.l == b
requires {p.value} + ({x.value} + value_set(x.l) + value_set(b)) + value_set(p.r)
    == full_value_set
ensures value_set(x) == full_value_set
{
  assert value_set(x)
      == {x.value} + value_set(x.l) + value_set(x.r)
      == {x.value} + value_set(x.l) + value_set(p)
      == {x.value} + value_set(x.l) + ({p.value} + value_set(p.l) + value_set(p.r))
      == {x.value} + value_set(x.l) + ({p.value} + value_set(b) + value_set(p.r))
      == {p.value} + ({x.value} + value_set(x.l) + value_set(b)) + value_set(p.r)
      == full_value_set;
}

lemma zig_left_node_set_is1(nsr: set<Node>, root: Node, p: Node, x: Node, b: Node?)
requires is_valid_node(p)
requires is_valid_node(x)
requires root == p;
requires p.l == x
requires x.r == b
requires is_valid_node(root)
requires node_set(root) == nsr
ensures nsr ==
    {p} + ({x} + node_set(x.l) + node_set(b)) + node_set(p.r)
{
  assert nsr
      == node_set(root)
      == node_set(p)
      == {p} + node_set(p.l) + node_set(p.r)
      == {p} + node_set(x) + node_set(p.r)
      == {p} + ({x} + node_set(x.l) + node_set(x.r)) + node_set(p.r)
      == {p} + ({x} + node_set(x.l) + node_set(b)) + node_set(p.r);
}

lemma zig_left_node_set_is2(nsr: set<Node>, root: Node, p: Node, x: Node, b: Node?)
requires is_valid_node(b)
requires is_valid_node(p.r)
requires is_structurally_valid(x)
requires x.r == p
requires p.l == b
requires {p} + ({x} + node_set(x.l) + node_set(b)) + node_set(p.r)
    == nsr
ensures node_set(x) == nsr
{
  assert node_set(x)
      == {x} + node_set(x.l) + node_set(x.r)
      == {x} + node_set(x.l) + node_set(p)
      == {x} + node_set(x.l) + ({p} + node_set(p.l) + node_set(p.r))
      == {x} + node_set(x.l) + ({p} + node_set(b) + node_set(p.r))
      == {p} + ({x} + node_set(x.l) + node_set(b)) + node_set(p.r)
      == nsr;
}

lemma unpack_gg_nodes(gg: Node, x: Node, y: Node?)
requires is_structurally_valid(gg)
requires gg.l == x || gg.r == x
requires gg.l == x ==> gg.r == y
requires gg.r == x ==> gg.l == y
ensures node_set(gg) == {gg} + node_set(x) + node_set(y)
{
}

lemma unpack_gg(gg: Node, x: Node, y: Node?)
requires is_structurally_valid(gg)
requires gg.l == x || gg.r == x
requires gg.l == x ==> gg.r == y
requires gg.r == x ==> gg.l == y
ensures value_set(gg) == {gg.value} + value_set(x) + value_set(y)
{
}

predicate
{:fuel 0,0}
gg_children_sets_are_good(gg: Node, which: bool, xset: set<int>, yset: set<int>)
reads gg
{
  if (which) then (
    (forall t: int :: t in xset ==> t < gg.value) &&
    (forall t: int :: t in yset ==> t > gg.value)
  ) else (
    (forall t: int :: t in yset ==> t < gg.value) &&
    (forall t: int :: t in xset ==> t > gg.value)
  )
}

lemma
{:fuel gg_children_sets_are_good,1,2}
gg_sets_prop1(gg: Node, which: bool, x: Node, y: Node?, xset: set<int>, yset: set<int>)
requires is_valid_node(gg)
requires which ==> gg.l == x && gg.r == y
requires !which ==> gg.l == y && gg.r == x
requires value_set(x) == xset
requires value_set(y) == yset
ensures gg_children_sets_are_good(gg, which, xset, yset)
{
}

lemma
{:fuel gg_children_sets_are_good,1,2}
gg_sets_prop2(gg: Node, which: bool, x: Node, y: Node?, xset: set<int>, yset: set<int>)
requires is_structurally_valid(gg)
requires which ==> gg.l == x && gg.r == y
requires !which ==> gg.l == y && gg.r == x
requires is_valid_node(x)
requires is_valid_node(y)
requires x.p == gg
requires y != null ==> y.p == gg
requires gg_children_sets_are_good(gg, which, xset, yset)
requires value_set(x) == xset
requires value_set(y) == yset
ensures is_valid_node(gg)
{
}
