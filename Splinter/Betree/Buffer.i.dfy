// Copyright 2018-2021 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, and University of Washington
// SPDX-License-Identifier: BSD-2-Clause

include "../../lib/Base/KeyType.s.dfy"
include "../../Spec/Message.s.dfy"

module BufferMod
{
  import opened KeyType
  import opened ValueMessage
  // import opened MessageMod

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

  datatype Buffer = Buffer(mapp: map<Key, Message>)
  {
    function Query(key: Key) : Message
    {
      if key in mapp then mapp[key] else Update(NopDelta())
    }

    function ApplyFilter(accept: iset<Key>) : Buffer
    {
      Buffer(map k | k in mapp && k in accept :: mapp[k])
    }

    // This would have been cleaner if Buffer were infinite map. Why are they finite?
    function Merge(older: Buffer) : Buffer {
      Buffer(map k | k in (mapp.Keys + older.mapp.Keys) :: 
        if k in mapp.Keys && k in older.mapp.Keys then ValueMessage.Merge(mapp[k], older.mapp[k])
        else if k in mapp.Keys then mapp[k]
        else older.mapp[k])
    }
  }

  function EmptyBuffer() : Buffer {
    Buffer(map[])
  }
}
