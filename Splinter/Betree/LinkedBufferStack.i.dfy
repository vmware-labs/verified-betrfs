// Copyright 2018-2021 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, and University of Washington
// SPDX-License-Identifier: BSD-2-Clause

include "../Disk/GenericDisk.i.dfy"
include "BufferStack.i.dfy"
  
  
module LinkedBufferStackMod {
  import opened GenericDisk
  import opened Maps
  import opened KeyType
  import opened ValueMessage
  import opened BufferMod
  import BufferStackMod


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


  // Note that this BufferStack is a pointer-y structure. It is different from
  // Buffers.BufferStack
  datatype BufferStack = BufferStack(buffers: seq<Address>)
  {
    predicate Valid(dv: BufferDiskView)
    {
      forall i:nat | i < |buffers| :: buffers[i] in dv.Addresses()
    }

    function Length() : nat 
    {
      |buffers|
    }

    function Slice(start: nat, end: nat) : BufferStack
      requires start <= end <= |buffers|
    {
      BufferStack(buffers[start..end])
    }

    // function GetBuffer(addr: Address) : Buffers.Buffer
    //   requires addr in buffers
    // {
    //   dv.Get(addr)
    // }

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
    // function ApplyFilter(accept: iset<Key>) : BufferStack
    // {
    //   BufferStack(seq(|buffers|, i requires 0<=i<|buffers| => buffers[i].ApplyFilter(accept)))
    // }

    function PushBufferStack(newBuffers: BufferStack) : BufferStack
    {
      BufferStack(newBuffers.buffers + this.buffers)
    }

    predicate Equivalent(dv: BufferDiskView, other: BufferStack)
      requires Valid(dv)
      requires other.Valid(dv)
    {
      forall k | BufferStackMod.AnyKey(k) :: Query(dv, k) == other.Query(dv, k)
    }

    function DropFirst() : BufferStack
      requires 0 < |buffers|
    {
      Slice(1, |buffers|)
    }
    
    function IBottom(dv: BufferDiskView, offsetMap: BufferStackMod.OffsetMap) : Buffer 
      requires Valid(dv)
      requires offsetMap.WF()
      requires 0 < |buffers|
    {
      dv.Get(buffers[0]).ApplyFilter(offsetMap.FilterForBottom())
    }

    function I(dv: BufferDiskView, offsetMap: BufferStackMod.OffsetMap) : Buffer 
      requires Valid(dv)
      requires offsetMap.WF()
      decreases |buffers|
    {
      if |buffers| == 0 then EmptyBuffer()
      else DropFirst().I(dv, offsetMap.Decrement(1)).Merge(IBottom(dv, offsetMap))
    }

  }  // end type BufferStack
}