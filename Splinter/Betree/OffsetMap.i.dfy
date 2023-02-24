// Copyright 2018-2021 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, and University of Washington
// SPDX-License-Identifier: BSD-2-Clause

include "../../lib/Base/KeyType.s.dfy"
include "Buffer.i.dfy"


module OffsetMapMod {
  import opened KeyType
  import opened BufferMod


  // TotalMapMod provides something like these, but it depends on module
  // refinement that's hairy and has problems in use (rank_is_less_than doesn't
  // make it through the module refinement, so we can't prove decreases).
  predicate AnyKey(key: Key) { true }
  predicate Total(keys: iset<Key>) {
    forall k | AnyKey(k) :: k in keys
  }
  function AllKeys() : (out: iset<Key>)
    ensures Total(out)
  {
    iset k | AnyKey(k)
  }

  datatype OffsetMap = OffsetMap(offsets: imap<Key, nat>)
  {
    predicate WF() {
      Total(offsets.Keys)
    }

    function Get(k: Key) : nat 
      requires WF()
    {
      offsets[k]
    }

    function FilterForBottom() : iset<Key> 
      requires WF()
    {
      iset k | offsets[k] == 0
    }

    function Decrement(i: nat) : OffsetMap 
      requires WF()
    {
      OffsetMap(imap k | AnyKey(k) :: if i <= offsets[k] then offsets[k]-i else 0)
    }
  }
}