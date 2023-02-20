// Copyright 2018-2021 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, and University of Washington
// SPDX-License-Identifier: BSD-2-Clause

include "../../lib/Base/KeyType.s.dfy"
include "../../Spec/Message.s.dfy"
include "Buffer.i.dfy"

module BufferStackMod
{
  import opened KeyType
  import opened ValueMessage
  import opened BufferMod

  // buffers[0] is the newest data, at the top of the stack
  datatype BufferStack = BufferStack(buffers: seq<Buffer>)
  {
    function Length() : nat 
    {
      |buffers|
    }

    function Slice(start: nat, end: nat) : BufferStack
      requires start <= end <= |buffers|
    {
      BufferStack(buffers[start..end])
    }

    function QueryUpTo(key: Key, count: nat) : Message
      requires count <= |buffers|
    {
      if count == 0 then Update(NopDelta())
      else Merge(QueryUpTo(key, count-1), buffers[count-1].Query(key))
    }

    function Query(key: Key) : Message
    {
      QueryUpTo(key, |buffers|)
    }

    function ApplyFilter(accept: iset<Key>) : BufferStack
    {
      BufferStack(seq(|buffers|, i requires 0<=i<|buffers| => buffers[i].ApplyFilter(accept)))
    }

    function PushBufferStack(newBuffers: BufferStack) : BufferStack
    {
      BufferStack(newBuffers.buffers + this.buffers)
    }

    predicate Equivalent(other: BufferStack)
    {
      forall k | AnyKey(k) :: Query(k) == other.Query(k)
    }
  }
}
