include "../MapSpec/MapSpec.s.dfy"
include "../MapSpec/ThreeStateVersionedMap.s.dfy"
include "../ByteBlockCacheSystem/AsyncDiskModel.s.dfy"
include "../lib/Lang/NativeTypes.s.dfy"
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

  predicate Inv(hs: HeapState)
    reads hs, HeapSet(hs)
  function I(hs: HeapState): ADM.M.Variables
    requires Inv(hs)
    reads hs, HeapSet(hs)

  method InitState() returns (hs: HeapState)
    ensures Inv(hs)
    ensures ADM.M.Init(I(hs))

  // Implementation of the state transitions

  method handlePushSync(hs: HeapState, io: DiskIOHandler)
  returns (id: uint64)
  requires io.initialized()
  requires Inv(hs)
  requires io !in HeapSet(hs)
  modifies hs, HeapSet(hs)
  modifies io
  ensures forall o | o in HeapSet(hs) :: o in old(HeapSet(hs)) || fresh(o)
  ensures Inv(hs)
  ensures ADM.M.Next(old(I(hs)), I(hs),
      if id == 0 then UI.NoOp else UI.PushSyncOp(id as int),
      io.diskOp())

  method handlePopSync(hs: HeapState, io: DiskIOHandler, id: uint64, graphSync: bool)
  returns (wait: bool, success: bool)
  requires io.initialized()
  requires Inv(hs)
  requires io !in HeapSet(hs)
  modifies hs, HeapSet(hs)
  modifies io
  ensures forall o | o in HeapSet(hs) :: o in old(HeapSet(hs)) || fresh(o)
  ensures Inv(hs)
  ensures ADM.M.Next(old(I(hs)), I(hs),
      if success then UI.PopSyncOp(id as int) else UI.NoOp,
      io.diskOp())

  method handleReadResponse(hs: HeapState, io: DiskIOHandler)
  requires io.diskOp().RespReadOp?
  requires Inv(hs)
  requires io !in HeapSet(hs)
  modifies hs, HeapSet(hs)
  ensures forall o | o in HeapSet(hs) :: o in old(HeapSet(hs)) || fresh(o)
  ensures Inv(hs)
  ensures ADM.M.Next(old(I(hs)), I(hs), UI.NoOp, io.diskOp())

  method handleWriteResponse(hs: HeapState, io: DiskIOHandler)
  requires io.diskOp().RespWriteOp?
  requires Inv(hs)
  requires io !in HeapSet(hs)
  modifies hs, HeapSet(hs)
  ensures forall o | o in HeapSet(hs) :: o in old(HeapSet(hs)) || fresh(o)
  ensures Inv(hs)
  ensures ADM.M.Next(old(I(hs)), I(hs), UI.NoOp, io.diskOp())

  method handleQuery(hs: HeapState, io: DiskIOHandler, key: Key)
  returns (v: Option<Value>)
  requires io.initialized()
  requires Inv(hs)
  requires io !in HeapSet(hs)
  modifies hs, HeapSet(hs)
  modifies io
  ensures forall o | o in HeapSet(hs) :: o in old(HeapSet(hs)) || fresh(o)
  ensures Inv(hs)
  ensures ADM.M.Next(old(I(hs)), I(hs),
    if v.Some? then UI.GetOp(key, v.value) else UI.NoOp,
    io.diskOp())

  method handleInsert(hs: HeapState, io: DiskIOHandler, key: Key, value: Value)
  returns (success: bool)
  requires io.initialized()
  requires Inv(hs)
  requires io !in HeapSet(hs)
  modifies hs, HeapSet(hs)
  modifies io
  ensures forall o | o in HeapSet(hs) :: o in old(HeapSet(hs)) || fresh(o)
  ensures Inv(hs)
  ensures ADM.M.Next(old(I(hs)), I(hs),
    if success then UI.PutOp(key, value) else UI.NoOp,
    io.diskOp())

  method handleSucc(hs: HeapState, io: DiskIOHandler, start: UI.RangeStart, maxToFind: uint64)
  returns (res: Option<UI.SuccResultList>)
  requires io.initialized()
  requires Inv(hs)
  requires maxToFind >= 1
  requires io !in HeapSet(hs)
  modifies hs, HeapSet(hs)
  modifies io
  ensures forall o | o in HeapSet(hs) :: o in old(HeapSet(hs)) || fresh(o)
  ensures Inv(hs)
  ensures ADM.M.Next(old(I(hs)), I(hs),
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
      s: ADM.Variables,
      diskContents: map<uint64, seq<byte>>)
  requires ADM.M.Init(s.machine)
  requires ADM.D.Init(s.disk)
  requires InitDiskContents(diskContents)
  requires ADM.BlocksWrittenInByteSeq(diskContents, s.disk.contents)
  ensures ADM.Init(s)

  // These are proof obligations for the refining module to fill in.
  // The refining module must
  //
  //  * Supply an abstraction function from the abstract disk
  //    state machine to the high-level MapSpec (by implementing
  //    the SystemI function)
  //
  //  * Prove the lemmas that show that this abstraction function
  //    yields a valid state machine refinement.

  inductive predicate SystemReachable(s: ADM.Variables)
  {
    ADM.Init(s) || (exists s0, u :: SystemReachable(s0) && ADM.Next(s0, s, u))
  }

  function SystemI(s: ADM.Variables) : ThreeStateVersionedMap.Variables
  requires SystemReachable(s)

  lemma SystemRefinesCrashSafeMapInit(
    s: ADM.Variables)
  requires ADM.Init(s)
  ensures SystemReachable(s)
  ensures ThreeStateVersionedMap.Init(SystemI(s))

  lemma SystemRefinesCrashSafeMapNext(
    s: ADM.Variables, s': ADM.Variables, uiop: ADM.UIOp)
  requires SystemReachable(s)
  requires ADM.Next(s, s', uiop)
  ensures SystemReachable(s')
  ensures ThreeStateVersionedMap.Next(SystemI(s), SystemI(s'), uiop)
}
