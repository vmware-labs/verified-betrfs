// Copyright 2018-2021 VMware, Inc.
// SPDX-License-Identifier: BSD-2-Clause

include "../Lang/NativeTypes.s.dfy"
include "../Base/Option.s.dfy"
include "../Base/sequences.i.dfy"
include "LinearMutableMap.i.dfy"
include "LinearDList.i.dfy"

/*
Unique sequence: a sequence of uint64 values, with no duplicates in the sequence.
Exports set-like operations to Add, Remove.
Exports seq-like operation to get First element.
Uses a map to efficiently find values in the sequence and remove them.
*/

module USeq
{
  import opened NativeTypes
  import opened Options
  import opened Sequences
  import LinearMutableMap
  import DList
  export
    provides NativeTypes, Options, Sequences
    provides USeq
    provides USeq.Inv, USeq.I
    provides USeq.Alloc, USeq.Free, USeq.Add, USeq.Remove, USeq.First, USeq.FirstOpt, USeq.Clone

  linear datatype USeq = USeq(
    linear dlist:DList.DList<uint64>,  // list of values
    linear ptr_map:LinearMutableMap.LinearHashMap<uint64> // map of pointers into dlist
    )
  {
    predicate Inv() {
      var q := this.dlist.Seq();
      && LinearMutableMap.Inv(this.ptr_map)
      && this.dlist.Inv()
      && NoDupes(q)
      && this.ptr_map.contents.Keys == Set(q)
      && (forall i {:trigger q[i] in this.ptr_map.contents} :: 0 <= i < |q| ==>
        && q[i] in this.ptr_map.contents
        && this.dlist.Index(this.ptr_map.contents[q[i]]) as int == i)
      && (forall x :: x in this.ptr_map.contents ==>
        && this.dlist.ValidPtr(this.ptr_map.contents[x])
        && this.dlist.Get(this.ptr_map.contents[x]) == x)
    }

    function I():(s:seq<uint64>)
      ensures this.Inv() ==> NoDupes(s)
    {
      this.dlist.Seq()
    }

    static method Alloc() returns(linear useq:USeq)
      ensures useq.Inv()
      ensures useq.I() == []
    {
      var size := 128;
      linear var dlist := DList.DList<uint64>.Alloc(size + 1);
      linear var ptr_map := LinearMutableMap.Constructor(size);
      useq := USeq(dlist, ptr_map);
      reveal_NoDupes();
      assert useq.I() == []; // observe
    }

    linear method Free()
    {
      linear var USeq(dlist, ptr_map) := this;
      dlist.Free();
      LinearMutableMap.Destructor(ptr_map);
    }

    linear inout method Add(x:uint64)
      requires old_self.Inv()
      requires |old_self.I()| < 0x1_0000_0000_0000_0000 / 8
      ensures self.Inv()
      ensures self.I() == (if x in old_self.I() then old_self.I() else old_self.I() + [x])
    {
      reveal_NoDupes();
      NoDupesSetCardinality(self.I());

      var found := LinearMutableMap.Get(self.ptr_map, x);
      if !found.Some? {
        var p := inout self.dlist.InsertBefore(0, x);
        LinearMutableMap.Insert(inout self.ptr_map, x, p);
      }
    }

    linear inout method Remove(x:uint64)
      requires old_self.Inv()
      ensures self.Inv()
      ensures self.I() == RemoveOneValue(old_self.I(), x)
    {
      ghost var q := self.dlist.Seq();

      var removed := LinearMutableMap.RemoveAndGet(inout self.ptr_map, x);
      if (removed.Some?) {
        var Some(p) := removed;
        inout self.dlist.Remove(p);
      }
      reveal_NoDupes();
      reveal_RemoveOneValue();
    }

    shared function method First() : (x:uint64)
      requires this.Inv()
      requires |this.I()| > 0
      ensures x == this.I()[0]
    {
      this.dlist.Get(this.dlist.Next(0))
    }

    shared function method FirstOpt() : (x:Option<uint64>)
      requires this.Inv()
      ensures |this.I()| == 0 ==> x == None
      ensures |this.I()| > 0 ==> x == Some(this.I()[0])
    {
      var p := this.dlist.Next(0);
      if (p == 0) then None
      else Some(this.dlist.Get(p))
    }

    shared method Clone() returns(linear useq':USeq)
      ensures useq' == this
    {
      shared var USeq(dlist, ptr_map) := this;
      linear var dlist' := dlist.Clone();
      linear var ptr_map' := LinearMutableMap.Clone(ptr_map);
      useq' := USeq(dlist', ptr_map');
    }
  }
}
