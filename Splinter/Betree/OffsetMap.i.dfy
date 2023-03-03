// Copyright 2018-2021 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, and University of Washington
// SPDX-License-Identifier: BSD-2-Clause

include "../../lib/Base/KeyType.s.dfy"
include "Buffer.i.dfy"


module OffsetMapMod {
  import opened KeyType
  import opened BufferMod

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

    // TODO: keeplist
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