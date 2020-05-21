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

module LinearUSeq
{
  import opened NativeTypes
  import opened Options
  import opened Sequences
  import LinearMutableMap
  import DList
  export
    provides NativeTypes, Options, Sequences
    provides LinearUSeq
    provides Inv, I, Unique
    provides Alloc, Free, Add, Remove, First, FirstOpt

  linear datatype LinearUSeq = LinearUSeq(
    linear dlist:DList.DList<uint64>,  // list of values
    linear ptr_map:LinearMutableMap.LinearHashMap<uint64> // map of pointers into dlist
    )

  predicate Inv(useq:LinearUSeq) {
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

  function I(useq:LinearUSeq):seq<uint64>
  {
    DList.Seq(useq.dlist)
  }

  lemma Unique(useq:LinearUSeq)
    requires Inv(useq)
    ensures NoDupes(I(useq))
  {
  }

  method Alloc() returns(linear useq:LinearUSeq)
    ensures Inv(useq)
  {
    var size := 128;
    linear var dlist := DList.Alloc<uint64>(size + 1);
    linear var ptr_map := LinearMutableMap.Constructor(size);
    useq := LinearUSeq(dlist, ptr_map);
    reveal_NoDupes();
  }

  method Free(linear useq:LinearUSeq)
  {
    linear var LinearUSeq(dlist, ptr_map) := useq;
    DList.Free(dlist);
    LinearMutableMap.Destructor(ptr_map);
  }

  method Add(linear useq:LinearUSeq, x:uint64) returns(linear useq':LinearUSeq)
    requires Inv(useq)
    requires |I(useq)| < 0x1_0000_0000_0000_0000 / 8
    ensures Inv(useq')
    ensures Set(I(useq')) == Set(I(useq)) + {x}
  {
    reveal_NoDupes();
    useq' := Remove(useq, x);
    NoDupesSetCardinality(I(useq));
    NoDupesSetCardinality(I(useq'));

    linear var LinearUSeq(dlist, ptr_map) := useq';
    var p;
    dlist, p := DList.InsertBefore(dlist, 0, x);
    ptr_map := LinearMutableMap.Insert(ptr_map, x, p);
    useq' := LinearUSeq(dlist, ptr_map);
  }

  method Remove(linear useq:LinearUSeq, x:uint64) returns(linear useq':LinearUSeq)
    requires Inv(useq)
    ensures Inv(useq')
    ensures Set(I(useq')) == Set(I(useq)) - {x}
  {
    linear var LinearUSeq(dlist, ptr_map) := useq;
    ghost var q := DList.Seq(dlist);

    linear var RemoveResult(ptr_map', removed) := LinearMutableMap.RemoveAndGet(ptr_map, x);
    if (removed.Some?) {
      var Some(p) := removed;
      dlist := DList.Remove(dlist, p);
    }
    useq' := LinearUSeq(dlist, ptr_map');
    reveal_NoDupes();
  }

  method First(shared useq:LinearUSeq) returns(x:uint64)
    requires Inv(useq)
    requires |I(useq)| > 0
    ensures x == I(useq)[0]
  {
    var p := DList.Next(useq.dlist, 0);
    x := DList.Get(useq.dlist, p);
  }

  method FirstOpt(shared useq:LinearUSeq) returns(x:Option<uint64>)
    requires Inv(useq)
    ensures |I(useq)| == 0 ==> x == None
    ensures |I(useq)| > 0 ==> x == Some(I(useq)[0])
  {
    var p := DList.Next(useq.dlist, 0);
    if (p == 0) {
      x := None;
    } else {
      x := Some(DList.Get(useq.dlist, p));
    }
  }
}
