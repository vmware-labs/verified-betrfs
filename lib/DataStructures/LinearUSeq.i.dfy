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
    var q := useq.dlist.Seq();
    && LinearMutableMap.Inv(useq.ptr_map)
    && useq.dlist.Inv()
    && NoDupes(q)
    && useq.ptr_map.contents.Keys == Set(q)
    && (forall i {:trigger q[i] in useq.ptr_map.contents} :: 0 <= i < |q| ==>
      && q[i] in useq.ptr_map.contents
      && useq.dlist.Index(useq.ptr_map.contents[q[i]]) as int == i)
    && (forall x :: x in useq.ptr_map.contents ==>
      && useq.dlist.ValidPtr(useq.ptr_map.contents[x])
      && useq.dlist.Get(useq.ptr_map.contents[x]) == x)
  }

  function I(useq:USeq):(s:seq<uint64>)
    ensures Inv(useq) ==> NoDupes(s)
  {
    useq.dlist.Seq()
  }

  method Alloc() returns(linear useq:USeq)
    ensures Inv(useq)
    ensures I(useq) == []
  {
    var size := 128;
    linear var dlist := DList.DList<uint64>.Alloc(size + 1);
    linear var ptr_map := LinearMutableMap.Constructor(size);
    useq := USeq(dlist, ptr_map);
    reveal_NoDupes();
  }

  method Free(linear useq:USeq)
  {
    linear var USeq(dlist, ptr_map) := useq;
    dlist.Free();
    LinearMutableMap.Destructor(ptr_map);
  }

  method Add(linear inout useq:USeq, x:uint64)
    requires Inv(old_useq)
    requires |I(old_useq)| < 0x1_0000_0000_0000_0000 / 8
    ensures Inv(useq)
    ensures I(useq) == (if x in I(old_useq) then I(old_useq) else I(old_useq) + [x])
  {
    reveal_NoDupes();
    NoDupesSetCardinality(I(useq));

    var found := LinearMutableMap.Get(useq.ptr_map, x);
    if !found.Some? {
      var p := inout useq.dlist.InsertBefore(0, x);
      LinearMutableMap.Insert(inout useq.ptr_map, x, p);
    }
  }

  method Remove(linear inout useq:USeq, x:uint64)
    requires Inv(old_useq)
    ensures Inv(useq)
    ensures I(useq) == RemoveOneValue(I(old_useq), x)
  {
    //linear var USeq(dlist, ptr_map) := useq;
    ghost var q := useq.dlist.Seq();

    var removed := LinearMutableMap.RemoveAndGet(inout useq.ptr_map, x);
    if (removed.Some?) {
      var Some(p) := removed;
      inout useq.dlist.Remove(p);
    }
    reveal_NoDupes();
    reveal_RemoveOneValue();
  }

  function method First(shared useq:USeq) : (x:uint64)
    requires Inv(useq)
    requires |I(useq)| > 0
    ensures x == I(useq)[0]
  {
    useq.dlist.Get(useq.dlist.Next(0))
  }

  function method FirstOpt(shared useq:USeq) : (x:Option<uint64>)
    requires Inv(useq)
    ensures |I(useq)| == 0 ==> x == None
    ensures |I(useq)| > 0 ==> x == Some(I(useq)[0])
  {
    var p := useq.dlist.Next(0);
    if (p == 0) then None
    else Some(useq.dlist.Get(p))
  }

  method Clone(shared useq:USeq) returns(linear useq':USeq)
    ensures useq' == useq
  {
    shared var USeq(dlist, ptr_map) := useq;
    linear var dlist' := dlist.Clone();
    linear var ptr_map' := LinearMutableMap.Clone(ptr_map);
    useq' := USeq(dlist', ptr_map');
  }
}
