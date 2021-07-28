include "../framework/StateMachines.s.dfy"
include "../../lib/Lang/NativeTypes.s.dfy"

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

  type Value = seq<byte>

  datatype VersionedObject = VersionedObject(
      versions: seq<Value>,
      persistent: nat
      )

  datatype Variables = Variables(
    store: map<int, VersionedObject>,

    reqs: map<RequestId, IOIfc.Input>,
    resps: map<RequestId, IOIfc.Output>,

    // RequestId -> key -> version
    // means that for the RequestId to complete, the 'persistence'
    // at key 'key' must be >= version
    syncReqs: map<RequestId, map<int, int>>
  )

  predicate PushInput(s: Variables, s': Variable, op: ifc.Op,
        rid: RequestId, input: CacheIfc.Input)
  {
    && op == Start(rid, input)
    && (input.WriteInput? || input.ReadInput?)
    && rid !in s.reqs
    && s' == s.(reqs := s.reqs[rid := input])
  }

  predicate Process(s: Variables, s': Variable, op: ifc.Op,
        rid: RequestId)
  {
    && op == InternalOp
    && rid in s.reqs
    && (s.reqs[rid].WriteInput? ==>
      s.(store := s.store[s.reqs[rid].key := s.reqs[rid].data])
      s.(reqs := s.reqs - {rid})
      s.(resps := s.resps[rid := WriteOutput])
    )
  }

  predicate PopOutput(s: Variables, s': Variable, op: ifc.Op,
      rid: RequestId, output: CacheIfc.Output)
  {
    && op == End(rid, output)
    && rid in s.resps
    && s' == s.(resps := s.resps - {rid})
    && output == s.resps[rid]
  }

  predicate PushSync(s: Variables, s': Variables, op: ifc.Op, rid: RequestId)
  {
    && op == Start(rid, SyncInput)
    && rid !in s.syncReqs
    && s' == s.(syncReqs := s.syncReqs[rid :=
        (map key | key in s.store :: |s.store[key].versions| - 1))
  }

  predicate PopSync(s: Variables, s': Variables, op: ifc.Op, rid: RequestId) {
    && op == End(rid, SyncOutput)
    && rid in s.syncResps
    && s' == s.(resps := s.resps - {rid})
    && (forall key | key in s.syncReqs[rid]
            :: key in s.store && s.store[key].persistent >= s.syncReqs[rid][key])
  }

  predicate VersionedObjectPersist(v: VersionedObject, v': VersionedObject) {
    && v'.versions == v.versions
    && v.persistent <= v'.persistent < |v.versions|)
  }

  predicate Persist(s: Variables, s': Variables, op: ifc.Op) {
    && op == InternalOp
    && s'.reqs == s.reqs
    && s'.resps == s.resps
    && s'.syncReqs == s.syncReqs
    && (forall key :: key in s.store <==> key in s'.store)
    && (forall key :: key in s.store ==> key in s'.store
        && VersionedObjectPersist(s.store[key], s'.store[key])
  }

  predicate VersionedObjectCrash(v: VersionedObject, v': VersionedObject, op: ifc.Op) {
    && |v'.versions| <= |v.versions|
    && v'.versions == v.versions[0 .. |v'.versions|]
    && |v'.versions| >= v.persistent
    && v'.persistent == v.persistent
  }

  predicate Crash(s: Variables, s': Variables, op: ifc.Op) {
    && op == CrashOp
    && s'.reqs == map[]
    && s'.resps == map[]
    && s'.syncReqs == map[]
    && (forall key | key in s.store ::
          && key in s'.store
          && VersionedObjectCrash(s.store[key], s'.store[key])
       )
  }
}
