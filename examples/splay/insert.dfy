// Copyright 2018-2021 VMware, Inc.
// SPDX-License-Identifier: MIT

lemma lemma_values_set_corresponds_to_nodes_set(node: Node?)
requires is_structurally_valid(node)
decreases |node_set(node)|
ensures value_set(node) == values_of_nodes(node_set(node))
{
  if (node != null) {
    lemma_values_set_corresponds_to_nodes_set(node.l);
    lemma_values_set_corresponds_to_nodes_set(node.r);
  }
}

lemma lemma_tree_set_inc(
    tree: Tree,
    root: Node,
    all_nodes: set<Node>,
    newnode: Node,
    value: uint64,
    old_set: set<uint64>)
requires is_valid_node(root)
requires tree.root == root
requires root.p == null
requires node_set(tree.root) == all_nodes + {newnode}
requires newnode.value == value
requires old_set == values_of_nodes(all_nodes)
ensures is_valid_tree(tree)
ensures tree_set(tree) == old_set + {value}
{
  lemma_values_set_corresponds_to_nodes_set(tree.root);
  assert tree_set(tree) ==
      value_set(tree.root) ==
      values_of_nodes(node_set(tree.root)) ==
      values_of_nodes(all_nodes + {newnode}) ==
      values_of_nodes(all_nodes) + values_of_nodes({newnode}) ==
      values_of_nodes(all_nodes) + {newnode.value} ==
      values_of_nodes(all_nodes) + {value} ==
      old_set + {value};
}

ghost method insert_init(root: Node, all_nodes: set<Node>, node: Node, value: uint64)
returns (path: seq<Node>, l: uint64, u: uint64)
requires is_valid_node(root)
requires root == node
ensures forall t : uint64 :: t in value_set(root) ==> l <= t <= u
ensures l <= value <= u
ensures is_valid_wrt_path(
        all_nodes,
        root, path, node, value,
        node.value, node.p, node_set(node), value_set(node), l, u)
{
  var s := value_set(root) + {value};
  l := minimum(s);
  u := maximum(s);
  path := [root];

  assert forall t : uint64 :: t in s ==> l <= t <= u;
  assert forall t : uint64 :: t in value_set(root) ==> l <= t <= u;
}

ghost method lemma_is_okay_when_do_nothing(tree: Tree, root: Node, old_ts: set<uint64>,
    value: uint64, node: Node, all_nodes: set<Node>)
requires tree.root == root
requires node.value == value
requires is_valid_node(root)
requires is_valid_node(node)
requires node_set(node) <= node_set(root)
requires root.p == null
requires old_ts == values_of_nodes(all_nodes)
requires all_nodes == node_set(root)
ensures is_valid_tree(tree)
ensures tree_set(tree) == old_ts + {value}
{
  assert is_valid_tree(tree);
  assert node in node_set(node);
  assert node in node_set(root);
  lemma_value_set_matches_node_set(root);
  assert node.value in value_set(root);
  assert value_set(root) == value_set(tree.root) == tree_set(tree);
  assert value in tree_set(tree);
  lemma_values_set_corresponds_to_nodes_set(tree.root);
  assert tree_set(tree) == value_set(tree.root)
      == values_of_nodes(node_set(tree.root))
      == values_of_nodes(node_set(root))
      == values_of_nodes(all_nodes)
      == old_ts;
  assert tree_set(tree) == tree_set(tree) + {value}
      == old_ts + {value};
}

method
{:fuel is_valid_wrt_path, 0, 0}
insert(tree: Tree, value: uint64)
modifies tree, tree.root, if tree.root != null then tree.root.node_set else {}
requires is_valid_tree(tree)
ensures is_valid_tree(tree)
ensures tree_set(tree) == old(tree_set(tree)) + {value}
{

  if (tree.root == null) {
    var node := new Node;
    node.l := null;
    node.r := null;
    node.p := null;
    node.value := value;
    node.node_set := {node};
    assert is_valid_node(node);
    tree.root := node;
  } else {
    var node: Node := tree.root;

    ghost var root := tree.root;
    ghost var all_nodes := node_set(root);
    var path, l, u := insert_init(root, all_nodes, node, value);

    lemma_values_set_corresponds_to_nodes_set(tree.root);
    ghost var original_values_of_nodes := values_of_nodes(all_nodes);
    assert old(tree_set(tree)) == tree_set(tree) == values_of_nodes(all_nodes) ==
        original_values_of_nodes;

    assert is_valid_wrt_path(
        all_nodes,
        root, path, node, value,
        node.value, node.p, node_set(node), value_set(node), l, u);

    ghost var exiting := false;

    var newnode: Node? := null;

    while (true)
    invariant is_valid_tree(tree)
    invariant is_valid_node(root)
    invariant is_valid_node(node)
    invariant node_set(node) <= node_set(root)
    invariant root == tree.root
    invariant all_nodes == node_set(root)
    invariant forall t : uint64 :: t in value_set(root) ==> l <= t <= u;
    invariant is_valid_wrt_path(
        all_nodes,
        root, path, node, value,
        node.value, node.p, node_set(node), value_set(node), l, u)
    invariant forall k : int :: 0 <= k < |path| ==> path[k] in all_nodes
    invariant !exiting ==> values_of_nodes(all_nodes) == original_values_of_nodes;
    invariant exiting ==> newnode != null && newnode in node_set(tree.root);
    decreases |node_set(node)|
    {
      assert node in all_nodes;
      assert !exiting;
      assert values_of_nodes(all_nodes) == original_values_of_nodes;

      if (node.value == value) {
        lemma_is_okay_when_do_nothing(tree, root, old(tree_set(tree)), value, node, all_nodes);
        return;
      }
      if (value < node.value) {
        if (node.l == null) {
          newnode := new Node;
          newnode.l := null;
          newnode.r := null;
          newnode.p := node;
          newnode.value := value;
          newnode.node_set := {newnode};

          ghost var old_value_set := value_set(node);

          node.l := newnode;

          ghost_fix_up_node_sets(all_nodes, tree.root, path, node, value,
              old_value_set, newnode, l, u);
          lemma_tree_set_inc(tree, root, all_nodes, newnode, value, old(tree_set(tree)));

          exiting := true;
          break;
        } else {
          path := append_to_path(root, root, path, node, value, l, u, node.l);

          assert is_valid_wrt_path(
              all_nodes,
              root, path, node.l, value,
              node.l.value, node.l.p, node_set(node.l), value_set(node.l), l, u);

          node := node.l;

          assert is_valid_wrt_path(
              all_nodes,
              root, path, node, value,
              node.value, node.p, node_set(node), value_set(node), l, u);
        }
      } else {
        if (node.r == null) {
          newnode := new Node;
          newnode.l := null;
          newnode.r := null;
          newnode.p := node;
          newnode.value := value;
          newnode.node_set := {newnode};

          ghost var old_value_set := value_set(node);

          node.r := newnode;

          ghost_fix_up_node_sets(all_nodes, tree.root, path, node, value,
              old_value_set, newnode, l, u);
          lemma_tree_set_inc(tree, root, all_nodes, newnode, value, old(tree_set(tree)));

          exiting := true;
          break;
        } else {
          path := append_to_path(root, root, path, node, value, l, u, node.r);

          node := node.r;

          assert is_valid_wrt_path(
              all_nodes,
              root, path, node, value,
              node.value, node.p, node_set(node), value_set(node), l, u);
        }
      }

      assert !exiting;
      assert values_of_nodes(all_nodes) == original_values_of_nodes;
    }

    splay(newnode, /* ghost */ tree.root, value_set(tree.root));
    tree.root := newnode;
  }
}

predicate is_valid_wrt_path(
    all_nodes: set<Node>,
    root: Node, path: seq<Node>, final: Node, value: uint64,
    fv: uint64, fp: Node?, fn: set<Node>, fvs: set<uint64>, l: uint64, r: uint64)
reads all_nodes - {final}
decreases |path|
{
  if (|path| == 0) then
    false
  else (
    root == path[0] &&
    (
      if |path| == 1 then (
        root == final &&
        l <= fv <= r &&
        forall v:uint64 :: v in fvs ==> l <= v <= r
      ) else (
       root != final &&
       root in all_nodes &&
       (root.l != null ==> root.l in all_nodes && root.l in node_set(root)) &&
       (root.r != null ==> root.r in all_nodes && root.r in node_set(root)) &&
       (root.l != null ==> (if root.l == final then fp else root.l.p) == root) &&
       (root.r != null ==> (if root.r == final then fp else root.r.p) == root) &&
       (root.node_set == 
          {root} +
          (if root.l == final then fn else node_set(root.l)) +
          (if root.r == final then fn else node_set(root.r))
       ) &&
       (root.value >= l) &&
       (root.value <= r) &&
       (
          (value < root.value &&
            root.l == path[1] &&
            (root.r != null ==> root.r in (all_nodes - {final})) &&
            node_set(root.r) <= all_nodes - {final} &&
            is_valid_node(root.r) &&
            (forall t : uint64 :: t in value_set(root.r) ==> root.value < t <= r) &&
            is_valid_wrt_path(all_nodes,
              root.l, path[1..], final, value, fv, fp, fn, fvs, l, root.value)
          ) ||
          (value > root.value &&
            root.r == path[1] &&
            (root.l != null ==> root.l in (all_nodes - {final})) &&
            node_set(root.l) <= all_nodes - {final} &&
            is_valid_node(root.l) &&
            (forall t : uint64 :: t in value_set(root.l) ==> l <= t < root.value) &&
            is_valid_wrt_path(all_nodes,
              root.r, path[1..], final, value, fv, fp, fn, fvs, root.value, r)
          )
        )
      )
    )
  )
}

lemma bounds_hold_for_append_left(
    main_root: Node,
    root: Node,
    path: seq<Node>,
    final: Node,
    value: uint64,
    l: uint64,
    r: uint64,
    newnode: Node,
    fv: uint64,
    fvs: set<uint64>)
requires root == final
requires is_valid_node(root)
requires is_valid_node(newnode)
requires fv == newnode.value
requires fvs == value_set(newnode)
requires forall t : uint64 :: t in value_set(root) ==> l < t < r
requires value < root.value
requires root.l == newnode
ensures l < fv < root.value
ensures forall v:uint64 :: v in fvs ==> l < v < root.value
{
  assert newnode.value in value_set(root);
  assert l < newnode.value;
  assert newnode.value < root.value;

  assert value_set(newnode) <= value_set(root);
  assert forall v:uint64 :: v in value_set(newnode) ==> l < v;

  assert forall v:uint64 :: v in value_set(newnode) ==> v < root.value;

  assert forall v:uint64 :: v in value_set(newnode) ==> l < v < root.value;
  assert forall v:uint64 :: v in fvs ==> l < v < root.value;
}

lemma bounds_hold_for_append_right(
    main_root: Node,
    root: Node,
    path: seq<Node>,
    final: Node,
    value: uint64,
    l: uint64,
    r: uint64,
    newnode: Node,
    fv: uint64,
    fvs: set<uint64>)
requires root == final
requires is_valid_node(root)
requires is_valid_node(newnode)
requires fv == newnode.value
requires fvs == value_set(newnode)
requires forall t : uint64 :: t in value_set(root) ==> l < t < r
requires root.value < value
requires root.r == newnode
ensures root.value < fv < r
ensures forall v:uint64 :: v in fvs ==> root.value < v < r
{
  assert newnode.value in value_set(root);
  assert newnode.value < r;
  assert root.value < newnode.value;

  assert value_set(newnode) <= value_set(root);
  assert forall v:uint64 :: v in value_set(newnode) ==> v < r;

  assert forall v:uint64 :: v in value_set(newnode) ==> root.value < v;

  assert forall v:uint64 :: v in value_set(newnode) ==> root.value < v < r;
  assert forall v:uint64 :: v in fvs ==> root.value < v < r;
}


ghost method append_to_path(
    main_root: Node,
    root: Node,
    path: seq<Node>,
    final: Node,
    value: uint64,
    l: uint64,
    r: uint64,
    newnode: Node) returns (path1: seq<Node>)
requires is_valid_node(main_root)
requires is_valid_node(root)
requires is_valid_node(final)
requires is_valid_wrt_path(node_set(main_root), root, path, final, value,
    final.value, final.p, node_set(final), value_set(final),
    l, r)
requires final.l == newnode || final.r == newnode
requires root in node_set(main_root)
requires forall t : uint64 :: t in value_set(root) ==> l < t < r
requires value != final.value;
requires value < final.value ==> newnode == final.l
requires value > final.value ==> newnode == final.r
ensures is_valid_wrt_path(node_set(main_root), root, path1, newnode, value,
    newnode.value, newnode.p, node_set(newnode), value_set(newnode),
    l, r)
ensures path1 == path + [newnode]
{
  var fv := final.value;
  var fp := final.p;
  var fn := node_set(final);
  var fvs := value_set(final);

  var fv1 := newnode.value;
  var fp1 := newnode.p;
  var fn1 := node_set(newnode);
  var fvs1 := value_set(newnode);

  var all_nodes := node_set(main_root);

  path1 := path + [newnode];

  node_set_contained(main_root, root);
  assert node_set(root) <= node_set(main_root);
  assert root.l != null ==> root.l in node_set(root);
  assert root.l != null ==> root.l in node_set(main_root);
  assert root.r != null ==> root.r in node_set(root);
  assert root.r != null ==> root.r in node_set(main_root);

  assert root in node_set(main_root);
  node_set_to_value_set(root, main_root);
  assert root.value in value_set(main_root);
  assert l < root.value < r;

  if (|path| == 1) {
    assert root == final;
    assert value < root.value || value > root.value;

    if (value < root.value) {
      assert root.l == path1[1] == newnode;
      if (root.r != null) {
        sides_disjoint(root, newnode, root.r);
        assert root.r in (all_nodes - {newnode});
        assert node_set(root.r) <= node_set(root);
        assert node_set(root.r) <= all_nodes;
        sides_disjoint_not_in_right(root, newnode);
        assert newnode !in node_set(root.r);
        assert node_set(root.r) <= all_nodes - {newnode};
      } else {
        assert node_set(root.r) <= all_nodes - {newnode};
      }
      assert is_valid_node(root.r);
      assert (forall t : uint64 :: t in value_set(root.r) ==> t > value);

      bounds_hold_for_append_left(main_root, root, path, final, value, l, r, newnode,
          fv1, fvs1);

      assert is_valid_wrt_path(all_nodes,
              root.l, path1[1..], newnode, value, fv1, fp1, fn1, fvs1, l, root.value);
    }
    if (value > root.value) {
      assert root.r == path1[1] == newnode;
      if (root.l != null) {
        sides_disjoint(root, root.l, newnode);
        assert root.l in (all_nodes - {newnode});
        assert node_set(root.l) <= node_set(root);
        assert node_set(root.l) <= all_nodes;
        sides_disjoint_not_in_left(root, newnode);
        assert newnode !in node_set(root.l);
        assert node_set(root.l) <= all_nodes - {newnode};
      } else {
        assert node_set(root.l) <= all_nodes - {newnode};
      }
      assert is_valid_node(root.l);
      assert (forall t : uint64 :: t in value_set(root.l) ==> t < value);

      bounds_hold_for_append_right(main_root, root, path, final, value, l, r, newnode,
          fv1, fvs1);

      assert is_valid_wrt_path(all_nodes,
              root.r, path1[1..], newnode, value, fv1, fp1, fn1, fvs1, root.value, r);
    }
  } else {
    assert value < root.value || value > root.value;
    if (value < root.value) {
      assert path[1] == root.l;
      assert forall t : uint64 :: t in value_set(root.l) ==> t < root.value;
      assert value_set(root.l) <= value_set(root);
      assert forall t : uint64 :: t in value_set(root) ==> l < t;
      assert forall t : uint64 :: t in value_set(root.l) ==> l < t;
      assert forall t : uint64 :: t in value_set(root.l) ==> l < t < root.value;
      assert forall t : uint64 :: t in value_set(path[1]) ==> l < t < root.value;
      var p0 := append_to_path(
        main_root, path[1], path[1..], final, value, l, root.value, newnode);

      assert is_valid_wrt_path(node_set(main_root), path[1], p0, newnode, value,
        newnode.value, newnode.p, node_set(newnode), value_set(newnode),
        l, root.value);

      assert path1 == [root] + p0;
      assert p0 == path1[1..];

      assert root != final;

      lemma_newnode_in_node_set(main_root, path[1], p0, newnode, value, l, root.value);
      assert newnode in node_set(root.l);
      sides_disjoint_not_in_right(root, newnode);
      not_in_children(root);
      assert root != newnode;

      assert root.l == path[1];
      assert (root.r != null ==> root.r in (all_nodes - {newnode}));
      assert node_set(root.r) <= all_nodes - {newnode};
      assert is_valid_node(root.r);
      assert (forall t : uint64 :: t in value_set(root.r) ==> value < t);
      assert is_valid_wrt_path(all_nodes,
        root.l, path1[1..], newnode, value, fv1, fp1, fn1, fvs1, l, root.value);

      assert is_valid_wrt_path(all_nodes,
        root, path1, newnode, value, fv1, fp1, fn1, fvs1, l, r);

    } else {
      assert value > root.value;

      assert path[1] == root.r;
      assert forall t : uint64 :: t in value_set(root.r) ==> root.value < t;
      assert value_set(root.r) <= value_set(root);
      assert forall t : uint64 :: t in value_set(root) ==> t < r;
      assert forall t : uint64 :: t in value_set(root.r) ==> t < r;
      assert forall t : uint64 :: t in value_set(root.r) ==> root.value < t < r;
      assert forall t : uint64 :: t in value_set(path[1]) ==> root.value < t < r;
      var p0 := append_to_path(
        main_root, path[1], path[1..], final, value, root.value, r, newnode);

      assert is_valid_wrt_path(node_set(main_root), path[1], p0, newnode, value,
        newnode.value, newnode.p, node_set(newnode), value_set(newnode),
        root.value, r);

      assert path1 == [root] + p0;
      assert p0 == path1[1..];

      assert root != final;

      lemma_newnode_in_node_set(main_root, path[1], p0, newnode, value, root.value, r);
      assert newnode in node_set(root.r);
      sides_disjoint_not_in_left(root, newnode);
      not_in_children(root);
      assert root != newnode;

      assert root.r == path[1];
      assert (root.l != null ==> root.l in (all_nodes - {newnode}));
      assert node_set(root.l) <= all_nodes - {newnode};
      assert is_valid_node(root.l);
      assert (forall t : uint64 :: t in value_set(root.l) ==> t < value);
      assert is_valid_wrt_path(all_nodes,
        root.r, path1[1..], newnode, value, fv1, fp1, fn1, fvs1, root.value, r);

      assert is_valid_wrt_path(all_nodes,
        root, path1, newnode, value, fv1, fp1, fn1, fvs1, l, r);
    }
  }
}

ghost method minimum(s: set<uint64>) returns (o: uint64)
requires |s| >= 1
ensures forall t : uint64 :: t in s ==> o <= t
{
  var y :| y in s;
  if (|s| > 1) {
    var m := minimum(s - {y});

    assert forall t : uint64 :: t in (s - {y}) ==> m <= t;
    o := (if y < m then y else m);
    assert forall t : uint64 :: t in (s - {y}) ==> o <= t;
    assert o <= y;
  } else {
    assert |s| == 1;
    assert y in s;
    assert |s - {y}| == 0;
    assert s - {y} == {};
    assert s == {y};
    return y;
  }
}

ghost method maximum(s: set<uint64>) returns (o: uint64)
requires |s| >= 1
ensures forall t : uint64 :: t in s ==> o >= t
{
  var y :| y in s;
  if (|s| > 1) {
    var m := maximum(s - {y});

    assert forall t : uint64 :: t in (s - {y}) ==> m >= t;
    o := (if y > m then y else m);
    assert forall t : uint64 :: t in (s - {y}) ==> o >= t;
    assert o >= y;
  } else {
    assert |s| == 1;
    assert y in s;
    assert |s - {y}| == 0;
    assert s - {y} == {};
    assert s == {y};
    return y;
  }
}

ghost method ghost_fix_up_node_sets(all_nodes: set<Node>, root: Node, path: seq<Node>, final: Node, value: uint64,
    old_final_value_set: set<uint64>, newnode: Node, l: uint64, u: uint64)
requires is_valid_wrt_path(
              all_nodes,
              root, path, final, value,
              final.value, final.p, final.node_set, old_final_value_set, l, u)
requires is_valid_node(final.l)
requires is_valid_node(final.r)
requires final.l != null ==> final.l.p == final
requires final.r != null ==> final.r.p == final
requires final.l == newnode || final.r == newnode
requires final.l == newnode ==> final.node_set == {final} + node_set(final.r)
requires final.r == newnode ==> final.node_set == {final} + node_set(final.l)
requires final.l == newnode ==> value_set(final.r) <= old_final_value_set
requires final.r == newnode ==> value_set(final.l) <= old_final_value_set
requires newnode.node_set == {newnode}
requires newnode.value == value
requires l <= value <= u
requires (forall t: uint64 :: t in value_set(final.l) ==> t < final.value);
requires (forall t: uint64 :: t in value_set(final.r) ==> t > final.value);
requires root.p == null
requires all_nodes == node_set(root)
modifies path
ensures is_valid_node(root)
ensures root.p == null
ensures node_set(root) == all_nodes + {newnode};
{
  ghost_fix_up_node_sets_step(all_nodes, root, path, final, value,
      old_final_value_set, newnode, l, u);
}

ghost method ghost_fix_up_node_sets_step(
    all_nodes: set<Node>, root: Node, path: seq<Node>, final: Node, value: uint64,
    old_final_value_set: set<uint64>, newnode: Node, l: uint64, u: uint64)
requires is_valid_wrt_path(
              all_nodes,
              root, path, final, value,
              final.value, final.p, final.node_set, old_final_value_set, l, u)
requires is_valid_node(final.l)
requires is_valid_node(final.r)
requires final.l != null ==> final.l.p == final
requires final.r != null ==> final.r.p == final
requires final.l == newnode || final.r == newnode
requires final.l == newnode ==> final.node_set == {final} + node_set(final.r)
requires final.r == newnode ==> final.node_set == {final} + node_set(final.l)
requires final.l == newnode ==> value_set(final.r) <= old_final_value_set
requires final.r == newnode ==> value_set(final.l) <= old_final_value_set
requires newnode.node_set == {newnode}
requires newnode.value == value
requires l < value < u
requires (forall t: uint64 :: t in value_set(final.l) ==> t < final.value);
requires (forall t: uint64 :: t in value_set(final.r) ==> t > final.value);
decreases |path| decreases 1
modifies path
ensures is_valid_node(root)
ensures root.node_set == old(root.node_set) + {newnode}
ensures forall t : uint64 :: t in value_set(root) ==> l < t < u
ensures node_set(newnode) == {newnode}
{
  var old_node_set_l := if |path| == 1 && root.l == newnode then {} else node_set(root.l);
  var old_node_set_r := if |path| == 1 && root.r == newnode then {} else node_set(root.r);
  var old_node_set := node_set(root);
  old_sets_satisfy_prop(old_node_set_l, old_node_set_r, old_node_set,
      all_nodes, root, path, final, value, old_final_value_set,
      newnode, l, u);
  assert |path| > 1 ==> old_node_set_l == node_set(root.l);
  assert |path| > 1 ==> old_node_set_r == node_set(root.r);

  ghost_maybe_fix_subpath(all_nodes, root, path, final, value, old_final_value_set,
      newnode, l, u);

  node_is_not_in_valid_child_subtree(root);
  assert root !in node_set(root.l);
  assert root !in node_set(root.r);

  lemma_node_set_is_correct(all_nodes, root, path, final, value,
      old_final_value_set, newnode, l, u, old_node_set_l, old_node_set_r,
      old_node_set);

  root.node_set := {root} + node_set(root.l) + node_set(root.r);

  assert is_valid_node(root.l);
  assert is_valid_node(root.r);

  lemma_node_set_of_children_is_smaller(root);

  assert is_valid_node(root);
}

ghost method ghost_maybe_fix_subpath(
    all_nodes: set<Node>, root: Node, path: seq<Node>, final: Node, value: uint64,
    old_final_value_set: set<uint64>, newnode: Node, l: uint64, u: uint64)
requires is_valid_wrt_path(
              all_nodes,
              root, path, final, value,
              final.value, final.p, final.node_set, old_final_value_set, l, u)
requires is_valid_node(final.l)
requires is_valid_node(final.r)
requires final.l != null ==> final.l.p == final
requires final.r != null ==> final.r.p == final
requires final.l == newnode || final.r == newnode
requires final.l == newnode ==> final.node_set == {final} + node_set(final.r)
requires final.r == newnode ==> final.node_set == {final} + node_set(final.l)
requires final.l == newnode ==> value_set(final.r) <= old_final_value_set
requires final.r == newnode ==> value_set(final.l) <= old_final_value_set
requires newnode.node_set == {newnode}
requires newnode.value == value
requires l < value < u
requires (forall t: uint64 :: t in value_set(final.l) ==> t < final.value);
requires (forall t: uint64 :: t in value_set(final.r) ==> t > final.value);
decreases |path| decreases 0
modifies path
ensures root.l != null ==> root.l.p == root
ensures root.r != null ==> root.r.p == root
ensures is_valid_node(root.l)
ensures is_valid_node(root.r)
ensures (forall t: uint64 :: t in value_set(root.l) ==> l < t < root.value)
ensures (forall t: uint64 :: t in value_set(root.r) ==> root.value < t < u)
ensures |path| > 1 ==>
    (node_set(root.l) == old(node_set(root.l)) + {newnode} && node_set(root.r) == old(node_set(root.r))) ||
    (node_set(root.r) == old(node_set(root.r)) + {newnode} && node_set(root.l) == old(node_set(root.l)))
ensures |path| == 1 ==>
    node_set(root.l) == old(node_set(root.l)) &&
    node_set(root.r) == old(node_set(root.r))
ensures |path| == 1 ==> root.l == newnode || root.r == newnode
ensures root.l != null && root.r != null ==> root.l != root.r
ensures node_set(newnode) == {newnode}
{
  if (|path| > 1) {
    if (value < root.value) {
      assert is_valid_wrt_path(all_nodes, root.l, path[1..], final, value,
          final.value, final.p, final.node_set, old_final_value_set, l, root.value);

      assert is_valid_node(root.r);
      lemma_path_disjoint_from_other_side(all_nodes, root, path, final, value,
          old_final_value_set, newnode, l, u);

      ghost_fix_up_node_sets_step(all_nodes, root.l, path[1..],
          final, value, old_final_value_set, newnode, l, root.value);

      assert is_valid_node(root.l);
      assert is_valid_node(root.r);

      assert root.l != null ==> root.l.p == root;
      assert root.r != null ==> root.r.p == root;
      assert (forall t: uint64 :: t in value_set(root.l) ==> l < t < root.value);
      assert (forall t: uint64 :: t in value_set(root.r) ==> root.value < t < u);
    } else {
      assert value > root.value;

      assert is_valid_wrt_path(all_nodes, path[1], path[1..], final, value,
          final.value, final.p, final.node_set, old_final_value_set, root.value, u);

      assert is_valid_node(root.l);
      lemma_path_disjoint_from_other_side(all_nodes, root, path, final, value,
          old_final_value_set, newnode, l, u);

      ghost_fix_up_node_sets_step(all_nodes, path[1], path[1..],
          final, value, old_final_value_set, newnode, root.value, u);

      assert is_valid_node(root.l);
      assert is_valid_node(root.r);

      assert root.l != null ==> root.l.p == root;
      assert root.r != null ==> root.r.p == root;
      assert (forall t: uint64 :: t in value_set(root.l) ==> l < t < root.value);
      assert (forall t: uint64 :: t in value_set(root.r) ==> root.value < t < u);
    }
  } else {
    assert root == final;
    assert is_valid_node(root.l);
    assert is_valid_node(root.r);

    assert root.l != null ==> root.l.p == root;
    assert root.r != null ==> root.r.p == root;
    lemma_bounds_hold_for_final(all_nodes, root, path, final, value,
        old_final_value_set, newnode, l, u);
    assert (forall t: uint64 :: t in value_set(root.l) ==> l < t < root.value);
    assert (forall t: uint64 :: t in value_set(root.r) ==> root.value < t < u);
  }

  if (root.l != null && root.r != null) {
    lemma_left_and_right_are_distinct(root.l, root.r, root.value);
    assert root.l != root.r;
  }
}

lemma old_sets_satisfy_prop(old_node_set_l: set<Node>, old_node_set_r: set<Node>, old_node_set: set<Node>,
    all_nodes: set<Node>, root: Node, path: seq<Node>, final: Node, value: uint64,
    old_final_value_set: set<uint64>, newnode: Node, l: uint64, u: uint64)
requires is_valid_wrt_path(
              all_nodes,
              root, path, final, value,
              final.value, final.p, final.node_set, old_final_value_set, l, u)
requires is_valid_node(final.l)
requires is_valid_node(final.r)
requires (forall t: uint64 :: t in value_set(final.l) ==> t < final.value);
requires (forall t: uint64 :: t in value_set(final.r) ==> t > final.value);
requires old_node_set_l == if |path| == 1 && root.l == newnode then {} else node_set(root.l)
requires old_node_set_r == if |path| == 1 && root.r == newnode then {} else node_set(root.r)
requires old_node_set == node_set(root)
requires final.l == newnode || final.r == newnode
requires final.l == newnode ==> final.node_set == {final} + node_set(final.r)
requires final.r == newnode ==> final.node_set == {final} + node_set(final.l)
ensures old_node_set == {root} + old_node_set_l + old_node_set_r
{
  if (|path| > 1) {
    assert old_node_set == node_set(root) == root.node_set ==
          {root} +
          (if root.l == final then final.node_set else node_set(root.l)) +
          (if root.r == final then final.node_set else node_set(root.r)) ==
          {root} + node_set(root.l) + node_set(root.r) ==
          {root} + old_node_set_l + old_node_set_r;
  } else {
    assert root == final;
    if (final.l != null && final.r != null) {
      lemma_left_and_right_are_distinct(final.l, final.r, final.value);
    }
    assert final.l != final.r;
    if (root.l == newnode) {
      assert root.r != newnode;
      assert old_node_set_l == {};
      assert old_node_set_r == node_set(root.r);
      assert old_node_set == root.node_set
          == {final} + node_set(final.r)
          == {root} + node_set(root.r)
          == {root} + old_node_set_r + old_node_set_l;
    } else {
      assert root.r == newnode;
      assert root.l != newnode;
      assert old_node_set_r == {};
      assert old_node_set_l == node_set(root.l);
      assert old_node_set == root.node_set
          == {final} + node_set(final.l)
          == {root} + node_set(root.l)
          == {root} + old_node_set_l + old_node_set_r;
    }
  }
}

lemma lemma_node_set_is_correct(all_nodes: set<Node>,
    root: Node,
    path: seq<Node>,
    final: Node,
    value: uint64,
    old_final_value_set: set<uint64>,
    newnode: Node,
    l: uint64,
    u: uint64,
    old_node_set_l: set<Node>,
    old_node_set_r: set<Node>,
    old_node_set: set<Node>)
requires |path| >= 1
requires |path| > 1 ==>
    (node_set(root.l) == old_node_set_l + {newnode} && node_set(root.r) == old_node_set_r) ||
    (node_set(root.r) == old_node_set_r + {newnode} && node_set(root.l) == old_node_set_l)
requires old_node_set == {root} + old_node_set_l + old_node_set_r
requires |path| == 1 ==>
  old_node_set_l == (if |path| == 1 && root.l == newnode then {} else node_set(root.l)) &&
  old_node_set_r == (if |path| == 1 && root.r == newnode then {} else node_set(root.r))
requires node_set(newnode) == {newnode}
requires is_valid_node(root.l)
requires is_valid_node(root.r)
requires root.l != null && root.r != null ==> root.l != root.r
requires |path| == 1 ==> root.l == newnode || root.r == newnode
ensures old_node_set + {newnode} == {root} + node_set(root.l) + node_set(root.r)
{
  if (|path| > 1) {
    if (node_set(root.l) == old_node_set_l + {newnode} && node_set(root.r) == old_node_set_r) {
      assert old_node_set + {newnode} ==
          ({root} + old_node_set_l + old_node_set_r) + {newnode} ==
          (old_node_set_l + {newnode}) + old_node_set_r + {root} ==
          node_set(root.l) + node_set(root.r) + {root};
    } else {
      assert (node_set(root.r) == old_node_set_r + {newnode} && node_set(root.l) == old_node_set_l);
      assert old_node_set + {newnode} ==
          ({root} + old_node_set_l + old_node_set_r) + {newnode} ==
          (old_node_set_r + {newnode}) + old_node_set_l + {root} ==
          node_set(root.r) + node_set(root.l) + {root};
    }
  } else {
    assert |path| == 1;
    assert root.l != null || root.r != null;
    assert root.l != root.r;
    if (root.l == newnode) {
      assert root.r != newnode;
      assert old_node_set_l == {};
      assert old_node_set_r == node_set(root.r);
      assert node_set(root.l) ==
              node_set(newnode) == {newnode};
      assert old_node_set + {newnode} ==
          ({root} + old_node_set_l + old_node_set_r) + {newnode} ==
          {root} + {} + node_set(root.r) + node_set(root.l) ==
          {root} + node_set(root.r) + node_set(root.l);
    } else {
    }
  }
}

lemma lemma_path_disjoint_from_other_side(
    all_nodes: set<Node>, root: Node, path: seq<Node>, final: Node, value: uint64,
    old_final_value_set: set<uint64>, newnode: Node, l: uint64, u: uint64)
requires is_valid_wrt_path(
              all_nodes,
              root, path, final, value,
              final.value, final.p, final.node_set, old_final_value_set, l, u)
requires 1 < |path| < 0x1_0000_0000_0000_0000
ensures value < root.value ==> forall k: int :: 0 <= k < |path| ==> path[k] !in node_set(root.r)
ensures value > root.value ==> forall k: int :: 0 <= k < |path| ==> path[k] !in node_set(root.l)
{
  if (value < root.value) {
    lemma_path_is_le(all_nodes, root, path, final, value, old_final_value_set, newnode, l, u);
    assert (forall t : uint64 :: t in value_set(root.r) ==> t > root.value);

    var k1: uint64 := 0;
    while (k1 < |path| as uint64)
    invariant forall k:uint64 :: 0 <= k < k1 ==> k < |path| as uint64 && path[k] !in node_set(root.r)
    {
      assert path[k1].value <= root.value;
      if (path[k1] in node_set(root.r)) {
        node_set_to_value_set(path[k1], root.r);
        assert path[k1].value in value_set(root.r);
        assert path[k1].value > root.value;
        assert false;
      }
      k1 := k1 + 1;
    }
  } else {
    lemma_path_is_ge(all_nodes, root, path, final, value, old_final_value_set, newnode, l, u);
    assert (forall t : uint64 :: t in value_set(root.l) ==> t < root.value);

    var k1: uint64 := 0;
    while (k1 < |path| as uint64)
    invariant forall k:uint64 :: 0 <= k < k1 ==> k < |path| as uint64 && path[k] !in node_set(root.l)
    {
      assert path[k1].value >= root.value;
      if (path[k1] in node_set(root.l)) {
        node_set_to_value_set(path[k1], root.l);
        assert path[k1].value in value_set(root.l);
        assert path[k1].value < root.value;
        assert false;
      }
      k1 := k1 + 1;
    }
  }
}

lemma lemma_path_is_le(
    all_nodes: set<Node>, root: Node, path: seq<Node>, final: Node, value: uint64,
    old_final_value_set: set<uint64>, newnode: Node, l: uint64, u: uint64)
requires is_valid_wrt_path(
              all_nodes,
              root, path, final, value,
              final.value, final.p, final.node_set, old_final_value_set, l, u)
requires value < root.value
ensures forall k: int :: 0 <= k < |path| ==> path[k].value <= root.value
{
  assert path[0] == root;
  assert path[0].value <= root.value;

  if (|path| > 1) {
    lemma_path_is_btw(all_nodes, path[1], path[1..], final, value, old_final_value_set, newnode, l, root.value);
  }
}

lemma lemma_path_is_ge(
    all_nodes: set<Node>, root: Node, path: seq<Node>, final: Node, value: uint64,
    old_final_value_set: set<uint64>, newnode: Node, l: uint64, u: uint64)
requires is_valid_wrt_path(
              all_nodes,
              root, path, final, value,
              final.value, final.p, final.node_set, old_final_value_set, l, u)
requires value > root.value
ensures forall k: int :: 0 <= k < |path| ==> path[k].value >= root.value
{
  assert path[0] == root;
  assert path[0].value <= root.value;

  if (|path| > 1) {
    lemma_path_is_btw(all_nodes, path[1], path[1..], final, value, old_final_value_set, newnode, root.value, u);
  }
}

lemma lemma_path_is_btw(
    all_nodes: set<Node>, root: Node, path: seq<Node>, final: Node, value: uint64,
    old_final_value_set: set<uint64>, newnode: Node, l: uint64, u: uint64)
requires is_valid_wrt_path(
              all_nodes,
              root, path, final, value,
              final.value, final.p, final.node_set, old_final_value_set, l, u)
ensures forall k: int :: 0 <= k < |path| ==> l < path[k].value < u
{
  if (|path| > 1) {
    assert l < path[0].value < u;
    if (value < root.value) {
      lemma_path_is_btw(all_nodes, path[1], path[1..], final, value, old_final_value_set, newnode, l, root.value);
    } else {
      lemma_path_is_btw(all_nodes, path[1], path[1..], final, value, old_final_value_set, newnode, root.value, u);
    }
  } else {
    assert l < final.value < u;
    assert l < path[0].value < u;
  }
}

lemma lemma_bounds_hold_for_final(
    all_nodes: set<Node>, root: Node, path: seq<Node>, final: Node, value: uint64,
    old_final_value_set: set<uint64>, newnode: Node, l: uint64, u: uint64)
requires is_valid_wrt_path(
              all_nodes,
              root, path, final, value,
              final.value, final.p, final.node_set, old_final_value_set, l, u)
requires |path| == 1
requires newnode.value == value
requires newnode.node_set == {newnode}
requires l < value < u
requires is_structurally_valid(final.l)
requires is_structurally_valid(final.r)
requires (forall t: uint64 :: t in value_set(final.l) ==> t < final.value)
requires (forall t: uint64 :: t in value_set(final.r) ==> t > final.value)
requires newnode == final.l || newnode == final.r
requires newnode == final.l ==> value_set(final.r) <= old_final_value_set
requires newnode == final.r ==> value_set(final.l) <= old_final_value_set
ensures (forall t: uint64 :: t in value_set(root.l) ==> l < t < root.value)
ensures (forall t: uint64 :: t in value_set(root.r) ==> root.value < t < u)
{
  assert value_set(newnode) == {value};
  assert forall v:uint64 :: v in value_set(newnode) ==> l < v < u;

  assert root == final;
  assert forall v:uint64 :: v in old_final_value_set ==> l < v < u;
  if (newnode == final.l) {
    assert value_set(final.r) <= old_final_value_set;
    assert value_set(root.r) <= old_final_value_set;
    assert forall v:uint64 :: v in value_set(root.r) ==> l < v < u;

    assert forall v:uint64 :: v in value_set(root.l) ==> l < v < u;
  } else {
    assert newnode == final.r;
  }
}

lemma lemma_newnode_in_node_set(
    main_root: Node, root: Node, path: seq<Node>, final: Node, value: uint64,
    l: uint64, r: uint64)
requires is_structurally_valid(main_root)
requires is_structurally_valid(root)
requires is_structurally_valid(final)
requires is_valid_wrt_path(node_set(main_root), root, path, final, value,
  final.value, final.p, node_set(final), value_set(final),
  l, r);
ensures final in node_set(root)
{
  if (|path| == 1) {
    assert final in node_set(root);
  } else {
    if (value < root.value) {
      lemma_newnode_in_node_set(main_root, path[1], path[1..], final, value, l, root.value);
    } else {
      lemma_newnode_in_node_set(main_root, path[1], path[1..], final, value, root.value, r);
    }
    assert final in node_set(path[1]);
    assert path[1] == root.l || path[1] == root.r;
    assert node_set(path[1]) <= node_set(root);
    assert final in node_set(root);
  }
}
