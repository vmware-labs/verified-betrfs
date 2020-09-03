include "../MapSpec/MapSpec.s.dfy"
include "../MapSpec/ThreeStateVersionedMap.s.dfy"
include "../ByteBlockCacheSystem/AsyncDiskModel.s.dfy"
include "../lib/Base/NativeTypes.s.dfy"
include "MainDiskIOHandler.s.dfy"

// Contains the abstract 'Main' module, which an implementation
// must refine, that is, it must define the global state type,
// implement the handle methods, and meet all of the contracts
// demanded by this file. (See MainHandlers.i.dfy)

module DiskTypes {
  import opened NativeTypes
  type LBA = uint64
  type ByteSector = seq<byte>
}

abstract module Main {
  import ADM : AsyncDiskModel

  import ThreeStateVersionedMap
  import opened NativeTypes
  import opened Options
  import DiskTypes
  import UI
  import opened MainDiskIOHandler
  import opened KeyType
  import opened ValueType

  type UIOp = ADM.M.UIOp

  // impl defined stuff

  type Constants // impl defined
  type Variables // impl defined

  class HeapState {
    var s: Variables;
    ghost var Repr: set<object>;
    constructor(s_: Variables, ghost repr: set<object>)
    ensures fresh(this)
    ensures Repr == repr
    ensures this.s == s_;
    {
      s := s_;
      Repr := repr;
    }
  }

  function HeapSet(hs: HeapState) : set<object>
    reads hs

  predicate Inv(k: Constants, hs: HeapState)
    reads hs, HeapSet(hs)
  function Ik(k: Constants): ADM.M.Constants
  function I(k: Constants, hs: HeapState): ADM.M.Variables
    requires Inv(k, hs)
    reads hs, HeapSet(hs)

  method InitState() returns (k: Constants, hs: HeapState)
    ensures Inv(k, hs)
    ensures ADM.M.Init(Ik(k), I(k, hs))

  // Implementation of the state transitions

  method handlePushSync(k: Constants, hs: HeapState, io: DiskIOHandler)
  returns (id: uint64)
  requires io.initialized()
  requires Inv(k, hs)
  requires io !in HeapSet(hs)
  modifies hs, HeapSet(hs)
  modifies io
  ensures forall o | o in HeapSet(hs) :: o in old(HeapSet(hs)) || fresh(o)
  ensures Inv(k, hs)
  ensures ADM.M.Next(Ik(k), old(I(k, hs)), I(k, hs),
      if id == 0 then UI.NoOp else UI.PushSyncOp(id as int),
      io.diskOp())

  method handlePopSync(k: Constants, hs: HeapState, io: DiskIOHandler, id: uint64, graphSync: bool)
  returns (wait: bool, success: bool)
  requires io.initialized()
  requires Inv(k, hs)
  requires io !in HeapSet(hs)
  modifies hs, HeapSet(hs)
  modifies io
  ensures forall o | o in HeapSet(hs) :: o in old(HeapSet(hs)) || fresh(o)
  ensures Inv(k, hs)
  ensures ADM.M.Next(Ik(k), old(I(k, hs)), I(k, hs),
      if success then UI.PopSyncOp(id as int) else UI.NoOp,
      io.diskOp())

  method handleReadResponse(k: Constants, hs: HeapState, io: DiskIOHandler)
  requires io.diskOp().RespReadOp?
  requires Inv(k, hs)
  requires io !in HeapSet(hs)
  modifies hs, HeapSet(hs)
  ensures forall o | o in HeapSet(hs) :: o in old(HeapSet(hs)) || fresh(o)
  ensures Inv(k, hs)
  ensures ADM.M.Next(Ik(k), old(I(k, hs)), I(k, hs), UI.NoOp, io.diskOp())

  method handleWriteResponse(k: Constants, hs: HeapState, io: DiskIOHandler)
  requires io.diskOp().RespWriteOp?
  requires Inv(k, hs)
  requires io !in HeapSet(hs)
  modifies hs, HeapSet(hs)
  ensures forall o | o in HeapSet(hs) :: o in old(HeapSet(hs)) || fresh(o)
  ensures Inv(k, hs)
  ensures ADM.M.Next(Ik(k), old(I(k, hs)), I(k, hs), UI.NoOp, io.diskOp())

  method handleQuery(k: Constants, hs: HeapState, io: DiskIOHandler, key: Key)
  returns (v: Option<Value>)
  requires io.initialized()
  requires Inv(k, hs)
  requires io !in HeapSet(hs)
  modifies hs, HeapSet(hs)
  modifies io
  ensures forall o | o in HeapSet(hs) :: o in old(HeapSet(hs)) || fresh(o)
  ensures Inv(k, hs)
  ensures ADM.M.Next(Ik(k), old(I(k, hs)), I(k, hs),
    if v.Some? then UI.GetOp(key, v.value) else UI.NoOp,
    io.diskOp())

  method handleInsert(k: Constants, hs: HeapState, io: DiskIOHandler, key: Key, value: Value)
  returns (success: bool)
  requires io.initialized()
  requires Inv(k, hs)
  requires io !in HeapSet(hs)
  modifies hs, HeapSet(hs)
  modifies io
  ensures forall o | o in HeapSet(hs) :: o in old(HeapSet(hs)) || fresh(o)
  ensures Inv(k, hs)
  ensures ADM.M.Next(Ik(k), old(I(k, hs)), I(k, hs),
    if success then UI.PutOp(key, value) else UI.NoOp,
    io.diskOp())

  method handleSucc(k: Constants, hs: HeapState, io: DiskIOHandler, start: UI.RangeStart, maxToFind: uint64)
  returns (res: Option<UI.SuccResultList>)
  requires io.initialized()
  requires Inv(k, hs)
  requires maxToFind >= 1
  requires io !in HeapSet(hs)
  modifies hs, HeapSet(hs)
  modifies io
  ensures forall o | o in HeapSet(hs) :: o in old(HeapSet(hs)) || fresh(o)
  ensures Inv(k, hs)
  ensures ADM.M.Next(Ik(k), old(I(k, hs)), I(k, hs),
    if res.Some? then UI.SuccOp(start, res.value.results, res.value.end) else UI.NoOp,
    io.diskOp())

  // Mkfs
  // You have to prove that, if the blocks returned by Mkfs are
  // written to disk, then the initial conditions of the
  // disk system are satisfied.
  
  predicate InitDiskContents(diskContents: map<uint64, seq<byte>>)

  method Mkfs()
  returns (diskContents: map<uint64, seq<byte>>)
  ensures InitDiskContents(diskContents)
  ensures ADM.BlocksDontIntersect(diskContents)

  lemma InitialStateSatisfiesSystemInit(
      k: ADM.Constants, 
      s: ADM.Variables,
      diskContents: map<uint64, seq<byte>>)
  requires ADM.M.Init(k.machine, s.machine)
  requires ADM.D.Init(k.disk, s.disk)
  requires InitDiskContents(diskContents)
  requires ADM.BlocksWrittenInByteSeq(diskContents, s.disk.contents)
  ensures ADM.Init(k, s)

  // These are proof obligations for the refining module to fill in.
  // The refining module must
  //
  //  * Supply an abstraction function from the abstract disk
  //    state machine to the high-level MapSpec (by implementing
  //    the SystemI function)
  //
  //  * Prove the lemmas that show that this abstraction function
  //    yields a valid state machine refinement.

  function SystemIk(k: ADM.Constants) : ThreeStateVersionedMap.Constants
  function SystemI(k: ADM.Constants, s: ADM.Variables) : ThreeStateVersionedMap.Variables
  requires ADM.Inv(k, s)

  lemma SystemRefinesCrashSafeMapInit(
    k: ADM.Constants, s: ADM.Variables)
  requires ADM.Init(k, s)
  ensures ADM.Inv(k, s)
  ensures ThreeStateVersionedMap.Init(SystemIk(k), SystemI(k, s))

  lemma SystemRefinesCrashSafeMapNext(
    k: ADM.Constants, s: ADM.Variables, s': ADM.Variables, uiop: ADM.UIOp)
  requires ADM.Inv(k, s)
  requires ADM.Next(k, s, s', uiop)
  ensures ADM.Inv(k, s')
  ensures ThreeStateVersionedMap.Next(SystemIk(k), SystemI(k, s), SystemI(k, s'), uiop)
}
