include "../Lang/NativeTypes.s.dfy"
include "../Base/Option.s.dfy"
include "../Base/DebugAccumulator.i.dfy"
include "LruModel.i.dfy"
include "LinearMutableMap.i.dfy"
include "LinearDList.i.dfy"

module LinearLru
{
  import opened NativeTypes
  import opened Options
  import LruModel`Internal
  import LinearMutableMap
  import DList
  export
    provides NativeTypes, Options, LruModel
    provides LinearLru
    provides Inv, Queue
    provides Alloc, Free, Remove, Use, Next, NextOpt

  linear datatype LinearLru = LinearLru(
    linear dlist:DList.DList<uint64>,  // list of values
    linear ptr_map:LinearMutableMap.LinearHashMap<uint64> // map of pointers into dlist
    )

  predicate Inv(lru:LinearLru) {
    var q := DList.Seq(lru.dlist);
    && LinearMutableMap.Inv(lru.ptr_map)
    && DList.Inv(lru.dlist)
    && LruModel.WF(q)
    && LruModel.I(q) == lru.ptr_map.contents.Keys
    && (forall i {:trigger q[i] in lru.ptr_map.contents} :: 0 <= i < |q| ==>
      && q[i] in lru.ptr_map.contents
      && DList.Index(lru.dlist, lru.ptr_map.contents[q[i]]) as int == i)
    && (forall x :: x in lru.ptr_map.contents ==>
      && DList.ValidPtr(lru.dlist, lru.ptr_map.contents[x])
      && DList.Get(lru.dlist, lru.ptr_map.contents[x]) == x)
  }

  function Queue(lru:LinearLru):(q:LruModel.LruQueue)
    ensures Inv(lru) ==> LruModel.WF(q)
  {
    DList.Seq(lru.dlist)
  }

  method Alloc() returns(linear lru:LinearLru)
    ensures Inv(lru)
  {
    var size := 128;
    linear var dlist := DList.Alloc<uint64>(size + 1);
    linear var ptr_map := LinearMutableMap.Constructor(size);
    lru := LinearLru(dlist, ptr_map);
  }

  method Free(linear lru:LinearLru)
  {
    linear var LinearLru(dlist, ptr_map) := lru;
    DList.Free(dlist);
    LinearMutableMap.Destructor(ptr_map);
  }

  method Remove(linear inout lru:LinearLru, x:uint64)
    requires Inv(old_lru)
    ensures Inv(lru)
    ensures Queue(lru) == LruModel.Remove(Queue(old_lru), x)
  {
    ghost var q := DList.Seq(lru.dlist);
    LruModel.LruRemove'(q, x);

    var removed := LinearMutableMap.RemoveAndGet(inout lru.ptr_map, x);
    if (removed.Some?) {
      var Some(p) := removed;
      DList.Remove(inout lru.dlist, p);
    }
  }

  method Use(linear inout lru:LinearLru, x:uint64)
    requires Inv(old_lru)
    requires |LruModel.I(Queue(old_lru))| < 0x1_0000_0000_0000_0000 / 8
    ensures Inv(lru)
    ensures Queue(lru) == LruModel.Use(Queue(old_lru), x)
  {
    LruModel.QueueCount(Queue(lru));
    LruModel.LruRemove'(Queue(lru), x);
    Remove(inout lru, x);
    LruModel.QueueCount(Queue(lru));

    var p := DList.InsertBefore(inout lru.dlist, 0, x);
    LinearMutableMap.Insert(inout lru.ptr_map, x, p);
  }

  method Next(shared lru:LinearLru) returns(x:uint64)
    requires Inv(lru)
    requires |LruModel.I(Queue(lru))| > 0
    ensures x == LruModel.Next(Queue(lru))
  {
    LruModel.QueueCount(DList.Seq(lru.dlist));
    var p := DList.Next(lru.dlist, 0);
    x := DList.Get(lru.dlist, p);
  }

  method NextOpt(shared lru:LinearLru) returns(x:Option<uint64>)
    requires Inv(lru)
    ensures x == LruModel.NextOpt(Queue(lru))
  {
    LruModel.QueueCount(DList.Seq(lru.dlist));
    var p := DList.Next(lru.dlist, 0);
    if (p == 0) {
      x := None;
    } else {
      LruModel.reveal_NextOpt();
      x := Some(DList.Get(lru.dlist, p));
    }
  }
}
