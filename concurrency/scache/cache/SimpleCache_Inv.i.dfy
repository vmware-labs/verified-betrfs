include "SimpleCacheSM.i.dfy"

module SimpleCache_Inv {
  import opened SimpleCacheStateMachine
  import ifc = CrashAsyncIfc(CacheIfc)
  import opened NativeTypes
  import opened RequestIds
  import CacheIfc

  predicate IsReader(s: Variables, c: nat, d: nat) {
    c in s.entries && s.entries[c].Reading? && s.entries[c].disk_idx == d
  }

  predicate IsWriter(s: Variables, c: nat, d: nat) {
    c in s.entries && s.entries[c].Writeback? && s.entries[c].disk_idx == d
  }

  predicate Inv(s: Variables) {
    && (forall c1, c2 |
      && c1 in s.entries && !s.entries[c1].Empty?
      && c2 in s.entries && !s.entries[c2].Empty?
      && c1 != c2
      :: s.entries[c1].disk_idx != s.entries[c2].disk_idx)
    && (forall d :: !(d in s.write_reqs && d in s.write_resps))
    /*&& (forall d :: !(d in s.write_reqs && d in s.read_reqs))
    && (forall d :: !(d in s.write_reqs && d in s.read_resps))
    && (forall d :: !(d in s.write_resps && d in s.read_reqs))
    && (forall d :: !(d in s.write_resps && d in s.read_resps))*/
    && (forall d :: !(d in s.read_reqs && d in s.read_resps))
    && (forall d | d in s.read_resps :: d in s.disk && s.disk[d] == s.read_resps[d])
    && (forall d | d in s.read_reqs || d in s.read_resps :: exists c :: IsReader(s, c, d))
    && (forall d | d in s.write_reqs || d in s.write_resps :: exists c :: IsWriter(s, c, d))
    /*&& (forall c | c in s.entries && s.entries[c].Reading?
        :: s.entries[c].disk_idx in s.read_reqs
        || s.entries[c].disk_idx in s.read_resps)*/
    && (forall c | c in s.entries && s.entries[c].Clean?
        :: s.entries[c].disk_idx in s.disk && s.disk[s.entries[c].disk_idx] == s.entries[c].data)
    && (forall c | c in s.entries && s.entries[c].Writeback? && s.entries[c].disk_idx in s.write_reqs
        :: s.write_reqs[s.entries[c].disk_idx] == s.entries[c].data)
    && (forall c | c in s.entries && s.entries[c].Writeback? && s.entries[c].disk_idx in s.write_resps
        :: s.entries[c].disk_idx in s.disk && s.disk[s.entries[c].disk_idx] == s.entries[c].data)
    && (forall c | c in s.entries && (s.entries[c].Writeback? || s.entries[c].Clean? || s.entries[c].Dirty?) :: s.entries[c].disk_idx in s.disk)
    && (forall k | True(k) :: k in s.disk)
  }

  lemma StartRead_PreservesInv(s: Variables, s': Variables, op: ifc.Op, cache_idx: nat, disk_idx: nat)
  requires Inv(s)
  requires StartRead(s, s', op, cache_idx, disk_idx)
  ensures Inv(s')
  {
    assert forall d, c :: IsReader(s, c, d) ==> IsReader(s', c, d);
    assert forall d, c :: IsWriter(s, c, d) ==> IsWriter(s', c, d);

    if disk_idx in s.read_resps {
      assert exists c :: IsReader(s, c, disk_idx);
      assert !s.entries[disk_idx].Empty?;
      assert false;
    }

    assert IsReader(s', cache_idx, disk_idx);
  }

  lemma FinishRead_PreservesInv(s: Variables, s': Variables, op: ifc.Op, cache_idx: nat, disk_idx: nat) 
  requires Inv(s)
  requires FinishRead(s, s', op, cache_idx, disk_idx)
  ensures Inv(s')
  {
    assert forall d, c :: d != disk_idx ==> IsReader(s, c, d) ==> IsReader(s', c, d);
    assert forall d, c :: IsWriter(s, c, d) ==> IsWriter(s', c, d);
  }

  lemma MarkDirty_PreservesInv(s: Variables, s': Variables, op: ifc.Op, cache_idx: nat) 
  requires Inv(s)
  requires MarkDirty(s, s', op, cache_idx)
  ensures Inv(s')
  {
    assert forall d, c :: IsReader(s, c, d) ==> IsReader(s', c, d);
    assert forall d, c :: IsWriter(s, c, d) ==> IsWriter(s', c, d);
  }

  lemma HavocNew_PreservesInv(s: Variables, s': Variables, op: ifc.Op, cache_idx: nat, rid: RequestId, block: DiskIfc.Block) 
  requires Inv(s)
  requires HavocNew(s, s', op, cache_idx, rid, block)
  ensures Inv(s')
  {
    assert forall d, c :: IsReader(s, c, d) ==> IsReader(s', c, d);
    assert forall d, c :: IsWriter(s, c, d) ==> IsWriter(s', c, d);
  }

  lemma HavocEvict_PreservesInv(s: Variables, s': Variables, op: ifc.Op, cache_idx: nat, rid: RequestId)
  requires Inv(s)
  requires HavocEvict(s, s', op, cache_idx, rid)
  ensures Inv(s')
  {
    assert forall d, c :: IsReader(s, c, d) ==> IsReader(s', c, d);
    assert forall d, c :: IsWriter(s, c, d) ==> IsWriter(s', c, d);
  }


  lemma StartWriteback_PreservesInv(s: Variables, s': Variables, op: ifc.Op, cache_idx: nat, disk_idx: nat) 
  requires Inv(s)
  requires StartWriteback(s, s', op, cache_idx, disk_idx)
  ensures Inv(s')
  {
    assert forall d, c :: IsReader(s, c, d) ==> IsReader(s', c, d);
    assert forall d, c :: IsWriter(s, c, d) ==> IsWriter(s', c, d);

    assert IsWriter(s', cache_idx, disk_idx);
  }

  lemma FinishWriteback_PreservesInv(s: Variables, s': Variables, op: ifc.Op, cache_idx: nat, disk_idx: nat) 
  requires Inv(s)
  requires FinishWriteback(s, s', op, cache_idx, disk_idx)
  ensures Inv(s')
  {
    assert forall d, c :: IsReader(s, c, d) ==> IsReader(s', c, d);
    assert forall d, c :: d != disk_idx ==> IsWriter(s, c, d) ==> IsWriter(s', c, d);

    assert IsWriter(s, cache_idx, disk_idx);

    assert s.entries[cache_idx].disk_idx in s.disk;
    assert s.disk[s.entries[cache_idx].disk_idx] == s.entries[cache_idx].data;
  }

  lemma Evict_PreservesInv(s: Variables, s': Variables, op: ifc.Op, cache_idx: nat) 
  requires Inv(s)
  requires Evict(s, s', op, cache_idx)
  ensures Inv(s')
  {
    assert forall d, c :: IsReader(s, c, d) ==> IsReader(s', c, d);
    assert forall d, c :: IsWriter(s, c, d) ==> IsWriter(s', c, d);
  }

  lemma ProcessRead_PreservesInv(s: Variables, s': Variables, op: ifc.Op, disk_idx: nat) 
  requires Inv(s)
  requires ProcessRead(s, s', op, disk_idx)
  ensures Inv(s')
  {
    assert forall d, c :: IsReader(s, c, d) ==> IsReader(s', c, d);
    assert forall d, c :: IsWriter(s, c, d) ==> IsWriter(s', c, d);
  }

  lemma ProcessWrite_PreservesInv(s: Variables, s': Variables, op: ifc.Op, disk_idx: nat) 
  requires Inv(s)
  requires ProcessWrite(s, s', op, disk_idx)
  ensures Inv(s')
  {
    assert forall d, c :: IsReader(s, c, d) ==> IsReader(s', c, d);
    assert forall d, c :: IsWriter(s, c, d) ==> IsWriter(s', c, d);
  }

  lemma Crash_PreservesInv(s: Variables, s': Variables, op: ifc.Op)
  requires Inv(s)
  requires Crash(s, s', op)
  ensures Inv(s')
  {
  }

  lemma NewTicket_PreservesInv(s: Variables, s': Variables, op: ifc.Op)
  requires Inv(s)
  requires NewTicket(s, s', op)
  ensures Inv(s')
  {
    assert forall d, c :: IsReader(s, c, d) ==> IsReader(s', c, d);
    assert forall d, c :: IsWriter(s, c, d) ==> IsWriter(s', c, d);
  }

  lemma ConsumeStub_PreservesInv(s: Variables, s': Variables, op: ifc.Op)
  requires Inv(s)
  requires ConsumeStub(s, s', op)
  ensures Inv(s')
  {
    assert forall d, c :: IsReader(s, c, d) ==> IsReader(s', c, d);
    assert forall d, c :: IsWriter(s, c, d) ==> IsWriter(s', c, d);
  }

  lemma NewSyncTicket_PreservesInv(s: Variables, s': Variables, op: ifc.Op)
  requires Inv(s)
  requires NewSyncTicket(s, s', op)
  ensures Inv(s')
  {
    assert forall d, c :: IsReader(s, c, d) ==> IsReader(s', c, d);
    assert forall d, c :: IsWriter(s, c, d) ==> IsWriter(s', c, d);
  }

  lemma ConsumeSyncStub_PreservesInv(s: Variables, s': Variables, op: ifc.Op)
  requires Inv(s)
  requires ConsumeSyncStub(s, s', op)
  ensures Inv(s')
  {
    assert forall d, c :: IsReader(s, c, d) ==> IsReader(s', c, d);
    assert forall d, c :: IsWriter(s, c, d) ==> IsWriter(s', c, d);
  }

  lemma NewHavocTicket_PreservesInv(s: Variables, s': Variables, op: ifc.Op)
  requires Inv(s)
  requires NewHavocTicket(s, s', op)
  ensures Inv(s')
  {
    assert forall d, c :: IsReader(s, c, d) ==> IsReader(s', c, d);
    assert forall d, c :: IsWriter(s, c, d) ==> IsWriter(s', c, d);
  }

  lemma ConsumeHavocStub_PreservesInv(s: Variables, s': Variables, op: ifc.Op)
  requires Inv(s)
  requires ConsumeHavocStub(s, s', op)
  ensures Inv(s')
  {
    assert forall d, c :: IsReader(s, c, d) ==> IsReader(s', c, d);
    assert forall d, c :: IsWriter(s, c, d) ==> IsWriter(s', c, d);
  }

  lemma ObserveCleanForSync_PreservesInv(s: Variables, s': Variables, op: ifc.Op, rid: RequestId, cache_idx: nat)
  requires Inv(s)
  requires ObserveCleanForSync(s, s', op, rid, cache_idx)
  ensures Inv(s')
  {
    assert forall d, c :: IsReader(s, c, d) ==> IsReader(s', c, d);
    assert forall d, c :: IsWriter(s, c, d) ==> IsWriter(s', c, d);
  }

  lemma ApplyRead_PreservesInv(s: Variables, s': Variables, op: ifc.Op, rid: RequestId, cache_idx: nat) 
  requires Inv(s)
  requires ApplyRead(s, s', op, rid, cache_idx)
  ensures Inv(s')
  {
    assert forall d, c :: IsReader(s, c, d) ==> IsReader(s', c, d);
    assert forall d, c :: IsWriter(s, c, d) ==> IsWriter(s', c, d);
  }

  lemma ApplyWrite_PreservesInv(s: Variables, s': Variables, op: ifc.Op, rid: RequestId, cache_idx: nat) 
  requires Inv(s)
  requires ApplyWrite(s, s', op, rid, cache_idx)
  ensures Inv(s')
  {
    assert forall d, c :: IsReader(s, c, d) ==> IsReader(s', c, d);
    assert forall d, c :: IsWriter(s, c, d) ==> IsWriter(s', c, d);
  }

  lemma Init_Implies_Inv(s: Variables)
  requires Init(s)
  ensures Inv(s)
  {
  }

  lemma NextStep_PreservesInv(s: Variables, s': Variables, op: ifc.Op, step: Step)
  requires Inv(s)
  requires NextStep(s, s', op, step)
  ensures Inv(s')
  {
    match step {
      case StartRead_Step(cache_idx, disk_idx) => { StartRead_PreservesInv(s, s', op, cache_idx, disk_idx); }
      case FinishRead_Step(cache_idx, disk_idx) => { FinishRead_PreservesInv(s, s', op, cache_idx, disk_idx); }
      case MarkDirty_Step(cache_idx) => { MarkDirty_PreservesInv(s, s', op, cache_idx); }
      case StartWriteback_Step(cache_idx, disk_idx) => { StartWriteback_PreservesInv(s, s', op, cache_idx, disk_idx); }
      case FinishWriteback_Step(cache_idx, disk_idx) => { FinishWriteback_PreservesInv(s, s', op, cache_idx, disk_idx) ; }
      case Evict_Step(cache_idx) => { Evict_PreservesInv(s, s', op, cache_idx); }
      case ProcessRead_Step(disk_idx) => { ProcessRead_PreservesInv(s, s', op, disk_idx); }
      case ProcessWrite_Step(disk_idx) => { ProcessWrite_PreservesInv(s, s', op, disk_idx); }
      case Crash_Step => { Crash_PreservesInv(s, s', op); }
      case NewTicket_Step => { NewTicket_PreservesInv(s, s', op); }
      case ConsumeStub_Step => { ConsumeStub_PreservesInv(s, s', op); }
      case NewSyncTicket_Step => { NewSyncTicket_PreservesInv(s, s', op); }
      case ConsumeSyncStub_Step => { ConsumeSyncStub_PreservesInv(s, s', op); }
      case NewHavocTicket_Step => { NewHavocTicket_PreservesInv(s, s', op); }
      case ConsumeHavocStub_Step => { ConsumeHavocStub_PreservesInv(s, s', op); }
      case ObserveCleanForSync_Step(rid, cache_idx) => { ObserveCleanForSync_PreservesInv(s, s', op, rid, cache_idx); }
      case ApplyRead_Step(rid, cache_idx) => { ApplyRead_PreservesInv(s, s', op, rid, cache_idx); }
      case ApplyWrite_Step(rid, cache_idx) => { ApplyWrite_PreservesInv(s, s', op, rid, cache_idx); }
      case HavocNew_Step(cache_idx, rid, block) => { HavocNew_PreservesInv(s, s', op, cache_idx, rid, block); }
      case HavocEvict_Step(cache_idx, rid) => { HavocEvict_PreservesInv(s, s', op, cache_idx, rid); }
      case Stutter_Step => { }
    }
  }

  lemma Next_PreservesInv(s: Variables, s': Variables, op: ifc.Op)
  requires Inv(s)
  requires Next(s, s', op)
  ensures Inv(s')
  {
    var step :| NextStep(s, s', op, step);
    NextStep_PreservesInv(s, s', op, step);
  }
}
