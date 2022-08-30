// Copyright 2018-2021 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, and University of Washington
// SPDX-License-Identifier: BSD-2-Clause

include "../../lib/Base/KeyType.s.dfy"
include "../../Spec/Message.s.dfy"

module Buffers
{
  import opened KeyType
  import opened ValueMessage

  // I'd prefer to instantiate TotalMapMod here, but rank_is_less_than doesn't
  // make it through the module refinement, so I can't prove decreases when I
  // recursively walk down the BetreeNode. So I do it manually instead.
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

  // buffers[0] is the newest data, at the top of the stack
  datatype BufferStack = BufferStack(buffers: seq<Buffer>)
  {
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

    function SliceRight(start: nat) : BufferStack
      requires start <= |buffers|
    {
      BufferStack(buffers[start..])
    }

    lemma QueryEmptyLeft(key: Key, start: nat, count: nat)
      requires start <= |buffers|
      requires count <= |buffers|
      requires forall i:nat | i < start :: buffers[i].Query(key) == Update(NopDelta())
      ensures count <= start ==> QueryUpTo(key, count) == Update(NopDelta())
      ensures start < count ==> QueryUpTo(key, count) == SliceRight(start).QueryUpTo(key, count-start)
    {
      if count > 0 {
        QueryEmptyLeft(key, start, count-1);
      }
    }    

    lemma QueryUpToEquivalent(key: Key, other: BufferStack, count: nat)
      requires |buffers| == |other.buffers|
      requires count <= |buffers|
      requires forall i:nat | i < |buffers| :: buffers[i].Query(key) == other.buffers[i].Query(key)
      ensures QueryUpTo(key, count) == other.QueryUpTo(key, count)
    {
      if count > 0 {
        QueryUpToEquivalent(key, other, count-1);
      }
    }
  }
}
