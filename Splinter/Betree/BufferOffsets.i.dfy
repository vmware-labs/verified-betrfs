// Copyright 2018-2021 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, and University of Washington
// SPDX-License-Identifier: BSD-2-Clause

include "../../lib/Base/Sequences.i.dfy"

module BufferOffsetsMod
{
  import opened Sequences

  // data structure tracking offsets of buffers
  // TOdo: this is a generic structuer independent of buffer/branch, should rename
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

    function OffSetsAfterCompact(start: nat, end: nat) : BufferOffsets 
    {
      BufferOffsets(
        seq(Size(), i requires 0 <= i < Size() => 
          if Get(i) <= start then Get(i)
          else if Get(i) < end then start
          else Get(i) - (end-start) + 1 // shift by compacted range + the replacement buffer
        )
      )
    }
  }
}