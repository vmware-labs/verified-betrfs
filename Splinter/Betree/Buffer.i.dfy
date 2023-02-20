// Copyright 2018-2021 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, and University of Washington
// SPDX-License-Identifier: BSD-2-Clause

include "../../lib/Base/KeyType.s.dfy"
include "../../Spec/Message.s.dfy"

module BufferMod
{
  import opened KeyType
  import opened ValueMessage

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
  }
}
