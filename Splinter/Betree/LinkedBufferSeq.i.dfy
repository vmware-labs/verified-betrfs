// Copyright 2018-2021 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, and University of Washington
// SPDX-License-Identifier: BSD-2-Clause

include "../Disk/GenericDisk.i.dfy"
include "BufferSeq.i.dfy"
  
  
module LinkedBufferSeqMod {
  import opened GenericDisk
  import opened Maps
  import opened KeyType
  import opened ValueMessage
  import opened BufferMod
  import opened OffsetMapMod

  datatype BufferDiskView = BufferDiskView(entries: map<Address, Buffer>)
  {
    function Addresses() : set<Address>
    {
      entries.Keys
    }

    function Get(addr: Address) : Buffer
      requires addr in entries
    {
      entries[addr]
    }

    function ModifyDisk(addr: Address, item: Buffer) : BufferDiskView {
      BufferDiskView.BufferDiskView(entries[addr := item])
    }

    predicate IsSubDisk(bigger: BufferDiskView)
    {
      IsSubMap(entries, bigger.entries)
    }

    function {:opaque} MergeDisk(other: BufferDiskView) : (out: BufferDiskView)
      // ensure result is sound -- keys and their values must come from one of these places
      ensures forall addr | addr in out.entries 
        :: || (addr in entries && out.entries[addr] == entries[addr])
           || (addr in other.entries && out.entries[addr] == other.entries[addr])
      // ensure result is complete -- result must contain all the keys
      ensures entries.Keys <= out.entries.Keys
      ensures other.entries.Keys <= out.entries.Keys
    {
      BufferDiskView(MapUnion(entries, other.entries))
    }
  }

  function EmptyBufferDisk() : BufferDiskView {
    BufferDiskView(map[])
  }

  datatype BufferSeq = BufferSeq(buffers: seq<Address>)
  {
    predicate Valid(dv: BufferDiskView)
    {
      forall i:nat | i < |buffers| :: buffers[i] in dv.Addresses()
    }

    function Length() : nat 
    {
      |buffers|
    }

    function Representation() : set<Address> {
      set addr | addr in buffers :: addr
    }

    function Slice(start: nat, end: nat) : BufferSeq
      requires start <= end <= |buffers|
    {
      BufferSeq(buffers[start..end])
    }

    function Extend(newBufferSeq: BufferSeq) : BufferSeq
    {
      BufferSeq(buffers + newBufferSeq.buffers)
    }

    function QueryUpTo(dv: BufferDiskView, key: Key, count: nat) : Message
      requires count <= |buffers|
      requires Valid(dv)
    {
      if count == 0 then Update(NopDelta())
      else
        Merge(QueryUpTo(dv, key, count-1), dv.Get(buffers[count-1]).Query(key))
    }

    function Query(dv: BufferDiskView, key: Key) : Message
      requires Valid(dv)
    {
      QueryUpTo(dv, key, |buffers|)
    }
    
    // TODO: compact equivalence needs this to validate 
    // function ApplyFilter(accept: iset<Key>) : BufferSeq
    // {
    //   BufferSeq(seq(|buffers|, i requires 0<=i<|buffers| => buffers[i].ApplyFilter(accept)))
    // }

    // function PushBufferSeq(newBuffers: BufferSeq) : BufferSeq
    // {
    //   BufferSeq(newBuffers.buffers + this.buffers)
    // }

    // predicate Equivalent(dv: BufferDiskView, other: BufferSeq)
    //   requires Valid(dv)
    //   requires other.Valid(dv)
    // {
    //   forall k | AnyKey(k) :: Query(dv, k) == other.Query(dv, k)
    // }

    function DropFirst() : BufferSeq
      requires 0 < |buffers|
    {
      Slice(1, |buffers|)
    }
    
    function IBottom(dv: BufferDiskView, offsetMap: OffsetMap) : Buffer 
      requires Valid(dv)
      requires offsetMap.WF()
      requires 0 < |buffers|
    {
      dv.Get(buffers[0]).ApplyFilter(offsetMap.FilterForBottom())
    }

    function I(dv: BufferDiskView, offsetMap: OffsetMap) : Buffer 
      requires Valid(dv)
      requires offsetMap.WF()
      decreases |buffers|
    {
      if |buffers| == 0 then EmptyBuffer()
      else DropFirst().I(dv, offsetMap.Decrement(1)).Merge(IBottom(dv, offsetMap))
    }

  }  // end type BufferSeq
}