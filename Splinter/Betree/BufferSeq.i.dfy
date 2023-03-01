// Copyright 2018-2021 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, and University of Washington
// SPDX-License-Identifier: BSD-2-Clause

include "../../lib/Base/KeyType.s.dfy"
include "../../Spec/Message.s.dfy"
include "Buffer.i.dfy"
include "OffsetMap.i.dfy"

module BufferSeqMod
{
  import opened KeyType
  import opened ValueMessage
  import opened BufferMod
  import opened OffsetMapMod

  // buffers[0] is the oldest data, at the top of the stack
  datatype BufferSeq = BufferSeq(buffers: seq<Buffer>)
  {
    function Length() : nat 
    {
      |buffers|
    }

    function Slice(start: nat, end: nat) : BufferSeq
      requires start <= end <= |buffers|
    {
      BufferSeq(buffers[start..end])
    }

    function DropFirst() : BufferSeq
      requires 0 < |buffers|
    {
      Slice(1, |buffers|)
    }

    function QueryFrom(key: Key, start: nat) : Message
      requires start <= |buffers|
    {
      if start == |buffers| then Update(NopDelta())
      else Merge(QueryFrom(key, start+1), buffers[start].Query(key))
    }

    function Query(key: Key) : Message
    {
      QueryFrom(key, 0)
    }

    function ApplyFilter(accept: iset<Key>) : BufferSeq
    {
      BufferSeq(seq(|buffers|, i requires 0<=i<|buffers| => buffers[i].ApplyFilter(accept)))
    }

    function Extend(newBuffers: BufferSeq) : BufferSeq
    {
      BufferSeq(this.buffers+newBuffers.buffers)
    }

    // When porting, consider eliminating this notion of equivalence up the stack, replace
    // with I()-equivalence
    // predicate Equivalent(other: BufferSeq)
    // {
    //   forall k | AnyKey(k) :: Query(k) == other.Query(k)
    // }

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

  // // TODO:fix
  // lemma CommonBufferSeqs(a: BufferSeq, b: BufferSeq, len: nat, key: Key)
  //   requires len <= |a.buffers|
  //   requires len <= |b.buffers|
  //   requires forall i | 0 <= i< len :: a.buffers[i] == b.buffers[i]
  //   ensures a.QueryFrom(key, len) == b.QueryFrom(key, len)
  // {
  //   var i:nat := 0;
  //   while i < len
  //     invariant i<=len
  //     invariant a.QueryFrom(key, i) == b.QueryFrom(key, i);
  //   {
  //     i := i + 1;
  //   }
  // }

  // lemma ExtendBufferSeqLemma(top: BufferSeq, bottom: BufferSeq, key: Key)
  //   ensures bottom.Extend(top).Query(key) == Merge(top.Query(key), bottom.Query(key))
  //   decreases |bottom.buffers|
  // {
  //   if |bottom.buffers| == 0 {
  //     assert bottom.Extend(top).buffers == top.buffers;  // trigger
  //   } else {
  //     var dropBottom := BufferSeq(DropLast(bottom.buffers));
  //     CommonBufferSeqs(dropBottom.PushBufferSeq(top), bottom.PushBufferSeq(top), |top.buffers|+|bottom.buffers|-1, key);
  //     PushBufferSeqLemma(top, dropBottom, key);
  //     CommonBufferSeqs(dropBottom, bottom, |bottom.buffers|-1, key);
  //   }
  // }
}
