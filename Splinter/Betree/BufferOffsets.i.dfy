// Copyright 2018-2021 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, and University of Washington
// SPDX-License-Identifier: BSD-2-Clause

include "../../lib/Base/Sequences.i.dfy"

module BufferOffsetsMod
{
  import opened Sequences

// data structure tracking offsets of buffers
  datatype BufferOffsets = BufferOffsets(offsets: seq<nat>)
  {
    function Size() : nat
    {
      |offsets|
    }

    function Get(i: nat) : nat
      requires i < |offsets|
    {
      offsets[i]
    }

    function Update(i: nat, v:nat): BufferOffsets 
      requires i < |offsets|
    {
      BufferOffsets(offsets[i := v])
    }

    predicate BoundedBy(length: nat)
      ensures BoundedBy(length) == forall i:nat | i < |offsets| :: Get(i) <= length
    {
      assert forall i:nat | i < |offsets| :: offsets[i] == Get(i);
      forall i:nat | i < |offsets| :: offsets[i] <= length
    }

    function Slice(start: nat, end: nat) : (out: BufferOffsets)
      requires start <= end <= |offsets|
      ensures out.Size() == end-start
      ensures forall i:nat | i < out.Size() :: out.Get(i) == Get(i+start)
    {
      BufferOffsets(offsets[start..end])
    }

    function Split(idx: nat) : (out: BufferOffsets) 
      requires idx < |offsets|
    {
      var original := Get(idx);
      BufferOffsets(replace1with2(offsets, original, original, idx))
    }

    predicate CanCollectGarbage(count: nat)
    {
      forall i:nat | i < Size() :: count <= Get(i)
    }

    // # to shift for every child
    function CollectGarbage(count: nat) : (out: BufferOffsets)
      requires CanCollectGarbage(count)
    {
      BufferOffsets(seq (Size(), i requires 0 <= i < Size() => Get(i)-count))
    }

    function AdvanceIndex(idx: nat, newOffset: nat) : (out: BufferOffsets)
      requires idx < Size()
      ensures out.Size() == Size()
      ensures forall i: nat | i < Size() && i != idx :: Get(i) == out.Get(i)
    {
      BufferOffsets(offsets[idx := newOffset])
    }

    // shift the value of each entry based on compacted buffers
    function CompactRange(compactStart: nat, compactEnd: nat, bufferLen: nat) : (out: BufferOffsets)
      requires compactStart < compactEnd <= bufferLen
      requires BoundedBy(bufferLen)
      ensures forall offset | offset in out.offsets :: offset <= bufferLen
      ensures out.Size() == Size()
      ensures forall offset | offset in out.offsets :: offset  <= bufferLen - (compactEnd-compactStart-1)
    {
      CompactInternal(compactStart, compactEnd, bufferLen, Size())
    }

    function CompactInternal(compactStart: nat, compactEnd: nat, bufferLen: nat, count: nat) : (out: BufferOffsets)
      requires compactStart < compactEnd <= bufferLen
      requires BoundedBy(bufferLen)
      requires count <= Size()
      ensures out.Size() == count
      ensures out.BoundedBy(bufferLen - (compactEnd-compactStart-1))
    {
    
      if count == 0 then BufferOffsets([])
      else (
        var numFlushed := Get(count-1); // this many buffers have been flushed
        var end := bufferLen-numFlushed; // end of valid active buffers 
        var numFlushed' := 
          if compactStart >= end // compacted range is entirely in flushed range
          then numFlushed - (compactEnd-compactStart-1)
          else if compactEnd <= end // compacted range is entirely outside the flushed range
          then numFlushed
          else numFlushed - (compactEnd - end); // compacted range overlaps with flushed range

        BufferOffsets(CompactInternal(compactStart, compactEnd, bufferLen, count-1).offsets + [numFlushed'])
      )
    }
  }
}