// Copyright 2018-2021 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, and University of Washington
// SPDX-License-Identifier: BSD-2-Clause
 
include "../../lib/Base/KeyType.s.dfy"
include "../../Spec/Message.s.dfy"
include "../../lib/Base/total_order_impl.i.dfy"
include "../../lib/Base/Sequences.i.dfy"

// iterator for branches 

module FlattenedBranchMod {
  import opened KeyType
  import opened ValueMessage 
  import opened Sequences
  import KeysImpl = Lexicographic_Byte_Order_Impl
  import Keys = KeysImpl.Ord 

  // Flattened branch for iterators (sequential and merge)
  datatype FlattenedBranch = FlattenedBranch(keys: seq<Key>, msgs: seq<Message>)
  {
    predicate WF()
    {
      && |keys| == |msgs|
      && Keys.IsStrictlySorted(keys)
    }

    predicate IsEmpty()
    {
      && keys == []
      && msgs == []
    }

    function Concat(other: FlattenedBranch) : (result: FlattenedBranch)
      requires WF()
      requires other.WF()
      requires |keys| > 0 && |other.keys| > 0 ==> Keys.lt(Last(keys), other.keys[0])
      ensures result.WF()
    {
      Keys.reveal_IsStrictlySorted();
      Keys.lteTransitiveForall();
      
      FlattenedBranch(keys + other.keys, msgs + other.msgs)
    }
  }

}
