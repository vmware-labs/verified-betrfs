// Copyright 2018-2021 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, and University of Washington
// SPDX-License-Identifier: BSD-2-Clause
 
include "LinkedBranch.i.dfy"
include "AllocationBranch.i.dfy"

module AllocationBranchRefinement {
    import L = LinkedBranchMod
    import opened AllocationBranchMod
//   import opened Maps
//   import opened Options
//   import opened KeyType
//   import opened ValueMessage
//   import opened Sequences
//   import opened GenericDisk
//   import opened Sets
//   import opened FlattenedBranchMod
//   import KeysImpl = Lexicographic_Byte_Order_Impl
//   import Keys = KeysImpl.Ord

  predicate CanINode(node: Node)
  {
    !node.Summary?
  }

  function INode(node: Node) : L.Node
    requires CanINode(node)
  {
    if node.Index? 
    then L.Index(node.pivots, node.children) 
    else L.Leaf(node.keys, node.msgs)
  }

  function IDiskView(dv: DiskView) : L.DiskView
  {
    L.DiskView(map addr | addr in dv.entries && CanINode(dv.entries[addr]) :: INode(dv.entries[addr]))
  }

  function I(branch: AllocationBranch) : L.LinkedBranch
  {
    L.LinkedBranch(branch.root, IDiskView(branch.diskView))
  }
}


