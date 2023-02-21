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

    function DropFirst() : BufferStack
      requires 0 < |buffers|
    {
      Slice(1, |buffers|)
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

    function IBottom(offsetMap: OffsetMap) : Buffer 
      requires offsetMap.WF()
      requires 0 < |buffers|
    {
      buffers[0].ApplyFilter(offsetMap.FilterForBottom())
    }

    function I(offsetMap: OffsetMap) : Buffer 
      requires offsetMap.WF()
      decreases |buffers|
    {
      if |buffers| == 0 then EmptyBuffer()
      else DropFirst().I(offsetMap.Decrement(1)).Merge(IBottom(offsetMap))
    }
  }


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
