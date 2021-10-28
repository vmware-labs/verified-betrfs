include "AbstractCacheSM.i.dfy"
include "SimpleCacheSM.i.dfy"
include "SimpleCache_Inv.i.dfy"

module SimpleCache_Refines_AbstractCache refines
    Refinement(CrashAsyncIfc(CacheIfc),
        SimpleCacheStateMachine,
        AbstractCacheStateMachine) {

  import opened SimpleCacheStateMachine
  import opened RequestIds
  import SimpleCache_Inv
  import DiskIfc

  predicate Inv(s: A.Variables) {
    SimpleCache_Inv.Inv(s)
  }

  lemma InitImpliesInv(s: A.Variables)
  //requires A.Init(s)
  ensures Inv(s)
  {
    SimpleCache_Inv.Init_Implies_Inv(s);
  }

  lemma NextPreservesInv(s: A.Variables, s': A.Variables, op: ifc.Op)
  //requires Inv(s)
  //requires A.Next(s, s', op)
  ensures Inv(s')
  {
    SimpleCache_Inv.Next_PreservesInv(s, s', op);
  }

  predicate IsInMem(s: Variables, c: nat, d: nat) {
    c in s.entries && (s.entries[c].Writeback? || s.entries[c].Clean?
        || s.entries[c].Dirty?)
      && s.entries[c].disk_idx == d
  }


  predicate InCache(s: Variables, disk_idx: nat) {
    exists cache_idx :: IsInMem(s, cache_idx, disk_idx)
  }

  function GetCacheIdx(s: Variables, disk_idx: nat) : nat
  requires InCache(s, disk_idx)
  {
    var cache_idx :| IsInMem(s, cache_idx, disk_idx);
    cache_idx
  }

  function GetElem(s: A.Variables, i: nat) : B.Elem
  requires i in s.disk
  {
    B.Elem(s.disk[i],
      if InCache(s, i) then s.entries[GetCacheIdx(s, i)].data
          else s.disk[i])
  }

  function InterpStore(s: A.Variables) : imap<nat, B.Elem>
  {
    imap i | i in s.disk :: GetElem(s, i)
  }

  function I(s: A.Variables) : B.Variables
  //requires Inv(s)
  {
    B.Variables(
      InterpStore(s),
      s.tickets,
      s.stubs,
      s.sync_reqs,
      s.havocs
    )
  }

  lemma InitRefinesInit(s: A.Variables)
  //requires A.Init(s)
  //requires Inv(s)
  ensures B.Init(I(s))
  {
  }

  lemma StartRead_Refines(s: Variables, s': Variables, op: ifc.Op, cache_idx: nat, disk_idx: nat)
  requires Inv(s)
  requires Inv(s')
  requires StartRead(s, s', op, cache_idx, disk_idx)
  ensures B.Next(I(s), I(s'), op)
  {
    assert forall d, c :: IsInMem(s, c, d) <==> IsInMem(s', c, d);

    /*
    var x := InterpStore(s);
    var y := InterpStore(s');
    forall k | k in x
    ensures k in y && y[k] == x[k]
    {
      if InCache(s, k) {
        assert InCache(s', k);
        assert GetCacheIdx(s, k) == GetCacheIdx(s', k);
      }
      if InCache(s', k) {
        assert InCache(s, k);
      }
      if k == disk_idx {
        assert k in y && y[k] == x[k];
      } else {
        assert k in y && y[k] == x[k];
      }
    }
    assert x == y;
    */

    assert B.NextStep(I(s), I(s'), op, B.Stutter_Step);
  }

  lemma FinishRead_Refines(s: Variables, s': Variables, op: ifc.Op, cache_idx: nat, disk_idx: nat) 
  requires Inv(s)
  requires FinishRead(s, s', op, cache_idx, disk_idx)
  requires Inv(s')
  ensures B.Next(I(s), I(s'), op)
  {
    assert forall d, c :: IsInMem(s, c, d) ==> IsInMem(s', c, d);
    assert forall d, c :: d != disk_idx ==> IsInMem(s', c, d) ==> IsInMem(s, c, d);
    assert IsInMem(s', cache_idx, disk_idx);

    /*
    var x := InterpStore(s);
    var y := InterpStore(s');
    forall k | k in x
    ensures k in y && y[k] == x[k]
    {
      if k == disk_idx {
        assert k in y && y[k] == x[k];
      } else {
        assert k in y && y[k] == x[k];
      }
    }
    assert x == y;
    assert I(s) == I(s');
    */
    assert B.NextStep(I(s), I(s'), op, B.Stutter_Step);
  }

  lemma MarkDirty_Refines(s: Variables, s': Variables, op: ifc.Op, cache_idx: nat) 
  requires Inv(s)
  requires MarkDirty(s, s', op, cache_idx)
  requires Inv(s')
  ensures B.Next(I(s), I(s'), op)
  {
    assert forall d, c :: IsInMem(s, c, d) <==> IsInMem(s', c, d);
    assert B.NextStep(I(s), I(s'), op, B.Stutter_Step);
  }

  lemma StartWriteback_Refines(s: Variables, s': Variables, op: ifc.Op, cache_idx: nat, disk_idx: nat) 
  requires Inv(s)
  requires StartWriteback(s, s', op, cache_idx, disk_idx)
  requires Inv(s')
  ensures B.Next(I(s), I(s'), op)
  {
    assert forall d, c :: IsInMem(s, c, d) <==> IsInMem(s', c, d);
    assert B.NextStep(I(s), I(s'), op, B.Stutter_Step);
  }

  lemma FinishWriteback_Refines(s: Variables, s': Variables, op: ifc.Op, cache_idx: nat, disk_idx: nat) 
  requires Inv(s)
  requires FinishWriteback(s, s', op, cache_idx, disk_idx)
  requires Inv(s')
  ensures B.Next(I(s), I(s'), op)
  {
    assert forall d, c :: IsInMem(s, c, d) <==> IsInMem(s', c, d);
    assert B.NextStep(I(s), I(s'), op, B.Stutter_Step);
  }

  lemma Evict_Refines(s: Variables, s': Variables, op: ifc.Op, cache_idx: nat) 
  requires Inv(s)
  requires Evict(s, s', op, cache_idx)
  requires Inv(s')
  ensures B.Next(I(s), I(s'), op)
  {
    assert forall d, c :: IsInMem(s', c, d) ==> IsInMem(s, c, d);
    assert forall d, c :: c != cache_idx ==> IsInMem(s, c, d) ==> IsInMem(s', c, d);
    assert IsInMem(s, cache_idx, s.entries[cache_idx].disk_idx);

    assert B.NextStep(I(s), I(s'), op, B.Stutter_Step);
  }

  lemma ProcessRead_Refines(s: Variables, s': Variables, op: ifc.Op, disk_idx: nat) 
  requires Inv(s)
  requires ProcessRead(s, s', op, disk_idx)
  requires Inv(s')
  ensures B.Next(I(s), I(s'), op)
  {
    assert forall d, c :: IsInMem(s, c, d) <==> IsInMem(s', c, d);
    assert B.NextStep(I(s), I(s'), op, B.Stutter_Step);
  }

  lemma ProcessWrite_Refines(s: Variables, s': Variables, op: ifc.Op, disk_idx: nat) 
  requires Inv(s)
  requires ProcessWrite(s, s', op, disk_idx)
  requires Inv(s')
  ensures B.Next(I(s), I(s'), op)
  {
    assert forall d, c :: IsInMem(s, c, d) <==> IsInMem(s', c, d);
    assert forall c :: SimpleCache_Inv.IsWriter(s, c, disk_idx) ==> IsInMem(s, c, disk_idx);
    assert disk_idx in InterpStore(s);
    assert disk_idx in InterpStore(s');
    assert InterpStore(s')[disk_idx] == B.PersistElem(InterpStore(s)[disk_idx]);
    assert B.Persist(I(s), I(s'), op, disk_idx);
    assert B.NextStep(I(s), I(s'), op, B.Persist_Step(disk_idx));
  }

  lemma Crash_Refines(s: Variables, s': Variables, op: ifc.Op)
  requires Inv(s)
  requires Crash(s, s', op)
  requires Inv(s')
  ensures B.Next(I(s), I(s'), op)
  {
    assert B.NextStep(I(s), I(s'), op, B.Crash_Step);
  }

  lemma NewTicket_Refines(s: Variables, s': Variables, op: ifc.Op)
  requires Inv(s)
  requires NewTicket(s, s', op)
  requires Inv(s')
  ensures B.Next(I(s), I(s'), op)
  {
    assert forall d, c :: IsInMem(s, c, d) <==> IsInMem(s', c, d);
    assert B.NewTicket(I(s), I(s'), op);
    assert B.NextStep(I(s), I(s'), op, B.NewTicket_Step);
  }

  lemma ConsumeStub_Refines(s: Variables, s': Variables, op: ifc.Op)
  requires Inv(s)
  requires ConsumeStub(s, s', op)
  requires Inv(s')
  ensures B.Next(I(s), I(s'), op)
  {
    assert forall d, c :: IsInMem(s, c, d) <==> IsInMem(s', c, d);
    assert B.NextStep(I(s), I(s'), op, B.ConsumeStub_Step);
  }

  lemma NewSyncTicket_Refines(s: Variables, s': Variables, op: ifc.Op)
  requires Inv(s)
  requires NewSyncTicket(s, s', op)
  requires Inv(s')
  ensures B.Next(I(s), I(s'), op)
  {
    assert forall d, c :: IsInMem(s, c, d) <==> IsInMem(s', c, d);
    assert B.NextStep(I(s), I(s'), op, B.NewSyncTicket_Step);
  }

  lemma ConsumeSyncStub_Refines(s: Variables, s': Variables, op: ifc.Op)
  requires Inv(s)
  requires ConsumeSyncStub(s, s', op)
  requires Inv(s')
  ensures B.Next(I(s), I(s'), op)
  {
    assert forall d, c :: IsInMem(s, c, d) <==> IsInMem(s', c, d);
    assert B.NextStep(I(s), I(s'), op, B.ConsumeSyncStub_Step);
  }

  lemma NewHavocTicket_Refines(s: Variables, s': Variables, op: ifc.Op)
  requires Inv(s)
  requires NewHavocTicket(s, s', op)
  requires Inv(s')
  ensures B.Next(I(s), I(s'), op)
  {
    assert forall d, c :: IsInMem(s, c, d) <==> IsInMem(s', c, d);
    assert B.NextStep(I(s), I(s'), op, B.NewHavocTicket_Step);
  }

  lemma ConsumeHavocStub_Refines(s: Variables, s': Variables, op: ifc.Op)
  requires Inv(s)
  requires ConsumeHavocStub(s, s', op)
  requires Inv(s')
  ensures B.Next(I(s), I(s'), op)
  {
    assert forall d, c :: IsInMem(s, c, d) <==> IsInMem(s', c, d);
    assert B.NextStep(I(s), I(s'), op, B.ConsumeHavocStub_Step);
  }

  lemma HavocNew_Refines(s: Variables, s': Variables, op: ifc.Op, cache_idx: nat, rid: RequestId, block: DiskIfc.Block)
  requires Inv(s)
  requires HavocNew(s, s', op, cache_idx, rid, block)
  requires Inv(s')
  ensures B.Next(I(s), I(s'), op)
  {
    assert forall d, c :: IsInMem(s, c, d) ==> IsInMem(s', c, d);
    assert forall d, c :: c != cache_idx ==> IsInMem(s', c, d) ==> IsInMem(s, c, d);
    assert B.NextStep(I(s), I(s'), op, B.DoHavoc_Step(rid));
  }

  lemma HavocEvict_Refines(s: Variables, s': Variables, op: ifc.Op, cache_idx: nat, rid: RequestId)
  requires Inv(s)
  requires HavocEvict(s, s', op, cache_idx, rid)
  requires Inv(s')
  ensures B.Next(I(s), I(s'), op)
  {
    assert forall d, c :: c != cache_idx ==> IsInMem(s, c, d) ==> IsInMem(s', c, d);
    assert forall d, c :: IsInMem(s', c, d) ==> IsInMem(s, c, d);
    assert B.NextStep(I(s), I(s'), op, B.DoHavoc_Step(rid));
  }

  lemma ObserveCleanForSync_Refines(s: Variables, s': Variables, op: ifc.Op, rid: RequestId, cache_idx: nat)
  requires Inv(s)
  requires ObserveCleanForSync(s, s', op, rid, cache_idx)
  requires Inv(s')
  ensures B.Next(I(s), I(s'), op)
  {
    assert forall d, c :: IsInMem(s, c, d) <==> IsInMem(s', c, d);
    assert B.NextStep(I(s), I(s'), op,
        B.ObserveCleanForSync_Step(rid, s.entries[cache_idx].disk_idx));
  }

  lemma ApplyRead_Refines(s: Variables, s': Variables, op: ifc.Op, rid: RequestId, cache_idx: nat) 
  requires Inv(s)
  requires ApplyRead(s, s', op, rid, cache_idx)
  requires Inv(s')
  ensures B.Next(I(s), I(s'), op)
  {
    assert forall d, c :: IsInMem(s, c, d) <==> IsInMem(s', c, d);
    assert IsInMem(s, cache_idx, s.entries[cache_idx].disk_idx);
    assert InterpStore(s') == InterpStore(s);
    assert B.ApplyRead(I(s), I(s'), op, rid);
    assert B.NextStep(I(s), I(s'), op, B.ApplyRead_Step(rid));
  }

  lemma ApplyWrite_Refines(s: Variables, s': Variables, op: ifc.Op, rid: RequestId, cache_idx: nat) 
  requires Inv(s)
  requires ApplyWrite(s, s', op, rid, cache_idx)
  requires Inv(s')
  ensures B.Next(I(s), I(s'), op)
  {
    assert forall d, c :: IsInMem(s, c, d) <==> IsInMem(s', c, d);
    assert IsInMem(s, cache_idx, s.entries[cache_idx].disk_idx);
    assert B.NextStep(I(s), I(s'), op, B.ApplyWrite_Step(rid));
  }

  lemma NextStep_Refines(s: Variables, s': Variables, op: ifc.Op, step: Step)
  requires Inv(s)
  requires NextStep(s, s', op, step)
  requires Inv(s')
  {
    match step {
      case StartRead_Step(cache_idx, disk_idx) => { StartRead_Refines(s, s', op, cache_idx, disk_idx); }
      case FinishRead_Step(cache_idx, disk_idx) => { FinishRead_Refines(s, s', op, cache_idx, disk_idx); }
      case MarkDirty_Step(cache_idx) => { MarkDirty_Refines(s, s', op, cache_idx); }
      case StartWriteback_Step(cache_idx, disk_idx) => { StartWriteback_Refines(s, s', op, cache_idx, disk_idx); }
      case FinishWriteback_Step(cache_idx, disk_idx) => { FinishWriteback_Refines(s, s', op, cache_idx, disk_idx) ; }
      case Evict_Step(cache_idx) => { Evict_Refines(s, s', op, cache_idx); }
      case ProcessRead_Step(disk_idx) => { ProcessRead_Refines(s, s', op, disk_idx); }
      case ProcessWrite_Step(disk_idx) => { ProcessWrite_Refines(s, s', op, disk_idx); }
      case Crash_Step => { Crash_Refines(s, s', op); }
      case NewTicket_Step => { NewTicket_Refines(s, s', op); }
      case ConsumeStub_Step => { ConsumeStub_Refines(s, s', op); }
      case NewSyncTicket_Step => { NewSyncTicket_Refines(s, s', op); }
      case ConsumeSyncStub_Step => { ConsumeSyncStub_Refines(s, s', op); }
      case NewHavocTicket_Step => { NewHavocTicket_Refines(s, s', op); }
      case ConsumeHavocStub_Step => { ConsumeHavocStub_Refines(s, s', op); }
      case ObserveCleanForSync_Step(rid, cache_idx) => { ObserveCleanForSync_Refines(s, s', op, rid, cache_idx); }
      case ApplyRead_Step(rid, cache_idx) => { ApplyRead_Refines(s, s', op, rid, cache_idx); }
      case ApplyWrite_Step(rid, cache_idx) => { ApplyWrite_Refines(s, s', op, rid, cache_idx); }
      case HavocNew_Step(cache_idx, rid, block) => { HavocNew_Refines(s, s', op, cache_idx, rid, block); }
      case HavocEvict_Step(cache_idx, rid) => { HavocEvict_Refines(s, s', op, cache_idx, rid); }
      case Stutter_Step => {
        assert B.NextStep(I(s), I(s'), op, B.Stutter_Step);
      }
    }
  }

  lemma NextRefinesNext(s: A.Variables, s': A.Variables, op: ifc.Op)
  //requires Inv(s)
  //requires Inv(s')
  //requires A.Next(s, s', op)
  ensures B.Next(I(s), I(s'), op)
}
