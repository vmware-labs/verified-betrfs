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
    function Representation() : set<Address>
    {
      entries.Keys
    }

    function Get(addr: Address) : Buffer
      requires addr in entries
    {
      entries[addr]
    }

    function ModifyDisk(addr: Address, item: Buffer) : BufferDiskView {
      BufferDiskView(entries[addr := item])
    }

    predicate IsFresh(addrs: set<Address>) {
      addrs !! entries.Keys
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
      forall i:nat | i < |buffers| :: buffers[i] in dv.Representation()
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

    function QueryFrom(dv: BufferDiskView, key: Key, start: nat) : Message
      requires start <= |buffers|
      requires Valid(dv)
      decreases |buffers| - start
    {
      if start == |buffers| then Update(NopDelta())
      else
        Merge(QueryFrom(dv, key, start+1), dv.Get(buffers[start]).Query(key))
    }

    // no one uses query without queryfrom in linked layer
    // function Query(dv: BufferDiskView, key: Key) : Message
    //   requires Valid(dv)
    // {
    //   QueryFrom(dv, key, 0)
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

    function IFiltered(dv: BufferDiskView, offsetMap: OffsetMap) : Buffer 
      requires Valid(dv)
      requires offsetMap.WF()
      decreases |buffers|
    {
      if |buffers| == 0 then EmptyBuffer()
      else DropFirst().IFiltered(dv, offsetMap.Decrement(1)).Merge(IBottom(dv, offsetMap))
    }

  }  // end type BufferSeq
}