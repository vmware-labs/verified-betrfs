// Copyright 2018-2021 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, and University of Washington
// SPDX-License-Identifier: BSD-2-Clause

include "../../lib/Buckets/BoundedPivotsLib.i.dfy"

module SplitRequestMod {
  import opened KeyType

  datatype SplitRequest =
      SplitLeaf(childIdx: nat, splitKey: Key) // Target is parent of a leaf node (one with Nil child)
    | SplitIndex(childIdx: nat, childPivotIdx: nat) // Target is parent of an index node (one with non-Nil children)

}
