include "../framework/StateMachines.s.dfy"
include "../../lib/Lang/NativeTypes.s.dfy"
include "../framework/DiskSSM.s.dfy"

module CacheIfc refines InputOutputIfc {
  import opened NativeTypes

  datatype Input =
    | WriteInput(key: int, data: seq<byte>)
    | ReadInput(key: int)
    | SyncInput

  datatype Output =
    | WriteOutput
    | ReadOutput(data: seq<byte>)
    | SyncOutput
}

module CacheSpec refines StateMachine(CrashAsyncIfc(CacheIfc)) {
  import opened NativeTypes
  import opened RequestIds
  import CacheIfc

  type Value = seq<byte>

  datatype VersionedObject = VersionedObject(
      versions: seq<Value>,
      persistent: nat
      )

  datatype Variables = Variables(
    store: map<int, VersionedObject>,

    reqs: map<RequestId, CacheIfc.Input>,
    resps: map<RequestId, CacheIfc.Output>,

    // RequestId -> key -> version
    // means that for the RequestId to complete, the 'persistence'
    // at key 'key' must be >= version
    syncs: map<RequestId, map<int, int>>
  )

  // Put a new request (either a 'read' or a 'write') into the requests
  predicate PushInput(s: Variables, s': Variables, op: ifc.Op,
        rid: RequestId, input: CacheIfc.Input)
  {
    && op == ifc.Start(rid, input)
    && (input.WriteInput? || input.ReadInput?)
    && rid !in s.reqs
    && s' == s.(reqs := s.reqs[rid := input])
  }

  // Process a read or a write.
  // Put the result in the 'resps' map.
  predicate Process(s: Variables, s': Variables, op: ifc.Op,
        rid: RequestId)
  {
    && op == ifc.InternalOp
    && rid in s.reqs
    && (s.reqs[rid].WriteInput? ==>
      // For a write: append this value to the versions list
      && s.reqs[rid].key in s.store
      && s' ==
        s.(store := s.store[s.reqs[rid].key :=
            VersionedObject(
              s.store[s.reqs[rid].key].versions + [s.reqs[rid].data],
              s.store[s.reqs[rid].key].persistent)])
         .(reqs := s.reqs - {rid})
         .(resps := s.resps[rid := CacheIfc.WriteOutput])
    )
    && (s.reqs[rid].ReadInput? ==>
      // For a read: determine the latest version.
      && s.reqs[rid].key in s.store
      && |s.store[s.reqs[rid].key].versions| > 0
      && s' ==
        s.(reqs := s.reqs - {rid})
         .(resps := s.resps[rid := CacheIfc.ReadOutput(
            s.store[s.reqs[rid].key].versions[
                |s.store[s.reqs[rid].key].versions| - 1])])
    )
  }

  // Pull a return value out of the 'resps' map
  predicate PopOutput(s: Variables, s': Variables, op: ifc.Op, rid: RequestId)
  {
    && rid in s.resps
    && op == ifc.End(rid, s.resps[rid])
    && s' == s.(resps := s.resps - {rid})
  }

  // Add a 'sync' request.
  // Save a copy of the latest version numbers for each cache entry; in order to finish
  // this sync request, we need to ensure that all those versions get written.
  predicate PushSync(s: Variables, s': Variables, op: ifc.Op, rid: RequestId)
  {
    && op == ifc.Start(rid, CacheIfc.SyncInput)
    && rid !in s.syncs
    && s' == s.(syncs := s.syncs[rid :=
        (map key | key in s.store :: |s.store[key].versions| - 1)])
  }

  // Finish a 'sync' request. To do this, requires checking that each entry is persisted
  // up to the point where the 'sync' request began.

  predicate PopSync(s: Variables, s': Variables, op: ifc.Op, rid: RequestId) {
    && op == ifc.End(rid, CacheIfc.SyncOutput)
    && rid in s.syncs
    && s' == s.(resps := s.resps - {rid})
    && (forall key | key in s.syncs[rid]
            :: key in s.store && s.store[key].persistent >= s.syncs[rid][key])
  }

  // 'Persist' can happen at any time, up to the implementation. (Only requirement
  // is that stuff has to be persisted before a sync completes.)
  // A 'persist' is represented by monotonically increasing the persist counters.

  predicate VersionedObjectPersist(v: VersionedObject, v': VersionedObject) {
    && v'.versions == v.versions
    && v.persistent <= v'.persistent < |v.versions|
  }

  predicate Persist(s: Variables, s': Variables, op: ifc.Op) {
    && op == ifc.InternalOp
    && s'.reqs == s.reqs
    && s'.resps == s.resps
    && s'.syncs == s.syncs
    && (forall key :: key in s.store <==> key in s'.store)
    && (forall key :: key in s.store ==> key in s'.store
        && VersionedObjectPersist(s.store[key], s'.store[key]))
  }

  // Crash: can lose some versions, can't go back behind the latest 'persist'.

  predicate VersionedObjectCrash(v: VersionedObject, v': VersionedObject) {
    && |v'.versions| <= |v.versions|
    && v'.versions == v.versions[0 .. |v'.versions|]
    && |v'.versions| >= v.persistent
    && v'.persistent == v.persistent
  }

  predicate Crash(s: Variables, s': Variables, op: ifc.Op) {
    && op == ifc.CrashOp
    && s'.reqs == map[]
    && s'.resps == map[]
    && s'.syncs == map[]
    && (forall key :: key in s.store <==> key in s'.store)
    && (forall key | key in s.store ::
          && key in s'.store
          && VersionedObjectCrash(s.store[key], s'.store[key])
       )
  }

  datatype Step =
    | PushInputStep(rid: RequestId, input: CacheIfc.Input)
    | ProcessStep(rid: RequestId)
    | PopOutputStep(rid: RequestId)
    | PushSyncStep(rid: RequestId)
    | PopSyncStep(rid: RequestId)
    | PersistStep
    | CrashStep

  predicate NextStep(s: Variables, s': Variables, op: ifc.Op, step: Step) {
    match step {
      case PushInputStep(rid, input) => PushInput(s, s', op, rid, input)
      case ProcessStep(rid) => Process(s, s', op, rid)
      case PopOutputStep(rid) => PopOutput(s, s', op, rid)
      case PushSyncStep(rid) => PushSync(s, s', op, rid)
      case PopSyncStep(rid) => PopSync(s, s', op, rid)
      case PersistStep => Persist(s, s', op)
      case CrashStep => Persist(s, s', op)
    }
  }

  predicate Next(s: Variables, s': Variables, op: ifc.Op) {
    exists step :: NextStep(s, s', op, step)
  }
}
