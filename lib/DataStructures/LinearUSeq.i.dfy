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
    provides Inv, I
    provides Alloc, Free, Add, Remove, First, FirstOpt, Clone

  linear datatype USeq = USeq(
    linear dlist:DList.DList<uint64>,  // list of values
    linear ptr_map:LinearMutableMap.LinearHashMap<uint64> // map of pointers into dlist
    )

  predicate Inv(useq:USeq) {
    var q := DList.Seq(useq.dlist);
    && LinearMutableMap.Inv(useq.ptr_map)
    && DList.Inv(useq.dlist)
    && NoDupes(q)
    && useq.ptr_map.contents.Keys == Set(q)
    && (forall i {:trigger q[i] in useq.ptr_map.contents} :: 0 <= i < |q| ==>
      && q[i] in useq.ptr_map.contents
      && DList.Index(useq.dlist, useq.ptr_map.contents[q[i]]) as int == i)
    && (forall x :: x in useq.ptr_map.contents ==>
      && DList.ValidPtr(useq.dlist, useq.ptr_map.contents[x])
      && DList.Get(useq.dlist, useq.ptr_map.contents[x]) == x)
  }

  function I(useq:USeq):(s:seq<uint64>)
    ensures Inv(useq) ==> NoDupes(s)
  {
    DList.Seq(useq.dlist)
  }

  method Alloc() returns(linear useq:USeq)
    ensures Inv(useq)
    ensures I(useq) == []
  {
    var size := 128;
    linear var dlist := DList.Alloc<uint64>(size + 1);
    linear var ptr_map := LinearMutableMap.Constructor(size);
    useq := USeq(dlist, ptr_map);
    reveal_NoDupes();
  }

  method Free(linear useq:USeq)
  {
    linear var USeq(dlist, ptr_map) := useq;
    DList.Free(dlist);
    LinearMutableMap.Destructor(ptr_map);
  }

  method Add(linear useq:USeq, x:uint64) returns(linear useq':USeq)
    requires Inv(useq)
    requires |I(useq)| < 0x1_0000_0000_0000_0000 / 8
    ensures Inv(useq')
    ensures I(useq') == (if x in I(useq) then I(useq) else I(useq) + [x])
  {
    reveal_NoDupes();
    NoDupesSetCardinality(I(useq));

    linear var USeq(dlist, ptr_map) := useq;
    if (LinearMutableMap.Get(ptr_map, x).Some?) {
      useq' := USeq(dlist, ptr_map);
    } else {
      var p;
      dlist, p := DList.InsertBefore(dlist, 0, x);
      ptr_map := LinearMutableMap.Insert(ptr_map, x, p);
      useq' := USeq(dlist, ptr_map);
    }
  }

  method Remove(linear useq:USeq, x:uint64) returns(linear useq':USeq)
    requires Inv(useq)
    ensures Inv(useq')
    ensures I(useq') == RemoveOneValue(I(useq), x)
  {
    linear var USeq(dlist, ptr_map) := useq;
    ghost var q := DList.Seq(dlist);

    linear var RemoveResult(ptr_map', removed) := LinearMutableMap.RemoveAndGet(ptr_map, x);
    if (removed.Some?) {
      var Some(p) := removed;
      dlist := DList.Remove(dlist, p);
    }
    useq' := USeq(dlist, ptr_map');
    reveal_NoDupes();
    reveal_RemoveOneValue();
  }

  function method First(shared useq:USeq) : (x:uint64)
    requires Inv(useq)
    requires |I(useq)| > 0
    ensures x == I(useq)[0]
  {
    DList.Get(useq.dlist, DList.Next(useq.dlist, 0))
  }

  function method FirstOpt(shared useq:USeq) : (x:Option<uint64>)
    requires Inv(useq)
    ensures |I(useq)| == 0 ==> x == None
    ensures |I(useq)| > 0 ==> x == Some(I(useq)[0])
  {
    var p := DList.Next(useq.dlist, 0);
    if (p == 0) then None
    else Some(DList.Get(useq.dlist, p))
  }

  method Clone(shared useq:USeq) returns(linear useq':USeq)
    ensures useq' == useq
  {
    shared var USeq(dlist, ptr_map) := useq;
    linear var dlist' := DList.Clone(dlist);
    linear var ptr_map' := LinearMutableMap.Clone(ptr_map);
    useq' := USeq(dlist', ptr_map');
  }
}
