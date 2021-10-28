include "../../framework/DiskSSM.s.dfy"
include "CacheSpec.s.dfy"

module AbstractCacheStateMachine refines StateMachine(CrashAsyncIfc(CacheIfc)) {
  import opened NativeTypes
  import opened RequestIds
  import CacheIfc

  type Value = seq<byte>

  datatype Elem = Elem(
    persistent: Value,
    ephemeral: Value
  )

  datatype Variables = Variables(
    store: imap<nat, Elem>,
    tickets: map<RequestId, CacheIfc.Input>,
    stubs: map<RequestId, CacheIfc.Output>,
    sync_reqs: map<RequestId, set<nat>>,
    havoc_reqs: map<RequestId, nat>
  )

  predicate Init(s: Variables) {
    && s.tickets == map[]
    && s.stubs == map[]
  }

  predicate Stutter(s: Variables, s': Variables, op: ifc.Op) {
    && op.InternalOp?
    && s' == s
  }

  function PersistElem(elem: Elem) : Elem {
    Elem(elem.ephemeral, elem.ephemeral)
  }

  /*function Persist_UpdateSyncReqs(sync_reqs: map<RequestId, set<nat>>, key: nat)
      : map<RequestId, set<nat>>
  {
    map rid | rid in sync_reqs :: sync_reqs[rid] - {key}
  }*/

  predicate Persist(s: Variables, s': Variables, op: ifc.Op, key: nat) {
    && op.InternalOp?
    && key in s.store
    && s' == s
      .(store := s.store[key := PersistElem(s.store[key])])
      //.(sync_reqs := Persist_UpdateSyncReqs(s.sync_reqs, key))
  }

  function CrashElem(elem: Elem) : Elem {
    Elem(elem.persistent, elem.persistent)
  }

  function CrashStore(store: imap<nat, Elem>) : imap<nat, Elem> {
    imap k | k in store :: CrashElem(store[k])
  }

  predicate Crash(s: Variables, s': Variables, op: ifc.Op) {
    && op.CrashOp?
    && s'.tickets == map[]
    && s'.stubs == map[]
    && s'.store == CrashStore(s.store)
  }

  predicate NewTicket(s: Variables, s': Variables, op: ifc.Op) {
    && op.Start?
    && (op.input.WriteInput? || op.input.ReadInput?)
    && op.rid !in s.tickets
    && s' == s.(tickets := s.tickets[op.rid := op.input])
  }

  predicate ConsumeStub(s: Variables, s': Variables, op: ifc.Op) {
    && op.End?
    && op.rid in s.stubs && s.stubs[op.rid] == op.output
    && s' == s.(stubs := s.stubs - {op.rid})
  }

  predicate NewSyncTicket(s: Variables, s': Variables, op: ifc.Op) {
    && op.Start?
    && op.input.SyncInput?
    && op.rid !in s.sync_reqs
    && s' == s.(sync_reqs := s.sync_reqs[op.rid := op.input.keys])
  }

  predicate ConsumeSyncStub(s: Variables, s': Variables, op: ifc.Op) {
    && op.End?
    && op.output.SyncOutput?
    && op.rid in s.sync_reqs
    && s.sync_reqs[op.rid] == {}
    && s' == s.(stubs := s.stubs - {op.rid})
  }

  predicate ObserveCleanForSync(s: Variables, s': Variables, op: ifc.Op, rid: RequestId, key: nat) {
    && op.InternalOp?
    && rid in s.sync_reqs
    && key in s.store
    && s.store[key].persistent == s.store[key].ephemeral
    && s' == s.(sync_reqs := s.sync_reqs[rid := s.sync_reqs[rid] - {key}])
  }

  predicate ApplyRead(s: Variables, s': Variables, op: ifc.Op, rid: RequestId) {
    && op.InternalOp?
    && rid in s.tickets
    && s.tickets[rid].ReadInput?
    && s.tickets[rid].key in s.store
    && s' == s
      .(tickets := s.tickets - {rid})
      .(stubs := s.stubs[rid := CacheIfc.ReadOutput(s.store[s.tickets[rid].key].ephemeral)])
  }

  function WriteElem(elem: Elem, data: Value) : Elem {
    Elem(elem.persistent, data)
  }

  predicate ApplyWrite(s: Variables, s': Variables, op: ifc.Op, rid: RequestId) {
    && op.InternalOp?
    && rid in s.tickets
    && s.tickets[rid].WriteInput?
    && s.tickets[rid].key in s.store
    && s' == s
      .(tickets := s.tickets - {rid})
      .(stubs := s.stubs[rid := CacheIfc.WriteOutput])
      .(store := s.store[s.tickets[rid].key :=
          WriteElem(s.store[s.tickets[rid].key], s.tickets[rid].data)])
  }

  datatype Step = 
     | Stutter_Step
     | Persist_Step(key: nat) 
     | Crash_Step
     | NewTicket_Step
     | ConsumeStub_Step
     | NewSyncTicket_Step
     | ConsumeSyncStub_Step
     | ObserveCleanForSync_Step(rid: RequestId, key: nat)
     | ApplyRead_Step(rid: RequestId)
     | ApplyWrite_Step(rid: RequestId) 

  predicate NextStep(s: Variables, s': Variables, op: ifc.Op, step: Step) {
    match step {
      case Stutter_Step => Stutter(s, s', op)
      case Persist_Step(key) => Persist(s, s', op, key)
      case Crash_Step => Crash(s, s', op)
      case NewTicket_Step => NewTicket(s, s', op)
      case ConsumeStub_Step => ConsumeStub(s, s', op)
      case NewSyncTicket_Step => NewSyncTicket(s, s', op)
      case ConsumeSyncStub_Step => ConsumeSyncStub(s, s', op)
      case ObserveCleanForSync_Step(rid, key) => ObserveCleanForSync(s, s', op, rid, key)
      case ApplyRead_Step(rid) => ApplyRead(s, s', op, rid)
      case ApplyWrite_Step(rid) => ApplyWrite(s, s', op, rid)
    }
  }

  predicate Next(s: Variables, s': Variables, op: ifc.Op) {
    exists step :: NextStep(s, s', op, step)
  }
}
