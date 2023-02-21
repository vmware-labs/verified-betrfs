// Copyright 2018-2021 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, and University of Washington
// SPDX-License-Identifier: BSD-2-Clause

include "../../lib/Base/KeyType.s.dfy"
include "../../Spec/Message.s.dfy"

module BufferMod
{
  import opened KeyType
  import opened ValueMessage
  // import opened MessageMod

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
