// Copyright 2018-2021 VMware, Inc.
// SPDX-License-Identifier: MIT

include "splaytree.dfy"

method Main() {
  var tree := new_tree();
  assert is_valid_tree(tree);

  var nInsertions := 1000 * 1000 * 100;

  var i: uint64 := 0;
  while i < nInsertions
    invariant is_valid_tree(tree)
  {
    var v := (i * 1_073_741_827) % nInsertions;
    insert(tree, v);
    assert v in tree_set(tree);
    //var c := contains(tree, v);
    i := i + 1;
  }
  print i;
}

