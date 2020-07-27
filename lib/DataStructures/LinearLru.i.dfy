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
    provides LinearLru.Inv, LinearLru.Queue
    provides LinearLru.Alloc, LinearLru.Free, LinearLru.Remove, LinearLru.Use, LinearLru.Next, LinearLru.NextOpt

  linear datatype LinearLru = LinearLru(
    linear dlist:DList.DList<uint64>,  // list of values
    linear ptr_map:LinearMutableMap.LinearHashMap<uint64> // map of pointers into dlist
    )
  {

    predicate Inv() {
      var q := this.dlist.Seq();
      && LinearMutableMap.Inv(this.ptr_map)
      && this.dlist.Inv()
      && LruModel.WF(q)
      && LruModel.I(q) == this.ptr_map.contents.Keys
      && (forall i {:trigger q[i] in this.ptr_map.contents} :: 0 <= i < |q| ==>
        && q[i] in this.ptr_map.contents
        && this.dlist.Index(this.ptr_map.contents[q[i]]) as int == i)
      && (forall x :: x in this.ptr_map.contents ==>
        && this.dlist.ValidPtr(this.ptr_map.contents[x])
        && this.dlist.Get(this.ptr_map.contents[x]) == x)
    }

    function Queue():(q:LruModel.LruQueue)
      ensures this.Inv() ==> LruModel.WF(q)
    {
      this.dlist.Seq()
    }

    method Alloc() returns (linear lru:LinearLru)
      ensures lru.Inv()
    {
      var size := 128;
      linear var dlist := DList.DList<uint64>.Alloc(size + 1);
      linear var ptr_map := LinearMutableMap.Constructor(size);
      lru := LinearLru(dlist, ptr_map);
    }

    method Free(linear lru:LinearLru)
    {
      linear var LinearLru(dlist, ptr_map) := lru;
      dlist.Free();
      LinearMutableMap.Destructor(ptr_map);
    }

    linear inout method Remove(x:uint64)
      requires old_self.Inv()
      ensures self.Inv()
      ensures self.Queue() == LruModel.Remove(old_self.Queue(), x)
    {
      ghost var q := self.dlist.Seq();
      LruModel.LruRemove'(q, x);

      var removed := LinearMutableMap.RemoveAndGet(inout self.ptr_map, x);
      if (removed.Some?) {
        var Some(p) := removed;
        inout self.dlist.Remove(p);
      }
    }

    linear inout method Use(x:uint64)
      requires old_self.Inv()
      requires |LruModel.I(old_self.Queue())| < 0x1_0000_0000_0000_0000 / 8
      ensures self.Inv()
      ensures self.Queue() == LruModel.Use(old_self.Queue(), x)
    {
      LruModel.QueueCount(self.Queue());
      LruModel.LruRemove'(self.Queue(), x);
      Remove(inout self, x);
      LruModel.QueueCount(self.Queue());

      var p := inout self.dlist.InsertBefore(0, x);
      LinearMutableMap.Insert(inout self.ptr_map, x, p);
    }

    shared method Next() returns(x:uint64)
      requires this.Inv()
      requires |LruModel.I(this.Queue())| > 0
      ensures x == LruModel.Next(this.Queue())
    {
      LruModel.QueueCount(this.dlist.Seq());
      var p := this.dlist.Next(0);
      x := this.dlist.Get(p);
    }

    shared method NextOpt() returns(x:Option<uint64>)
      requires this.Inv()
      ensures x == LruModel.NextOpt(this.Queue())
    {
      LruModel.QueueCount(this.dlist.Seq());
      var p := this.dlist.Next(0);
      if (p == 0) {
        x := None;
      } else {
        LruModel.reveal_NextOpt();
        x := Some(this.dlist.Get(p));
      }
    }
  }
}
