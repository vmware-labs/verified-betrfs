include "MapSpec.dfy"
include "CrashSafe.dfy"
include "Disk.dfy"
include "DiskAccessModel.dfy"
include "../lib/NativeTypes.dfy"

module DiskTypes {
  import opened NativeTypes
  type LBA = uint64
  type ByteSector = seq<byte>
}

// Implementation has to instantiate this
// and refine it to the BetreeBlockCache
// either than or BetreeBlockCache itself will be the instantiation of this module?

// TODO how to create all the contracts without a dependency on the .i file that instantiates
// the machine? Sounds like it would require parameterized modules?
// IDEALLY we would be able to say: define a machine type M and also give me a proof
// that MachineSystem<M> refines CrashSafeMap

/*
abstract module Machine refines DiskAccessMachine {
  import UI = UI
  import DiskTypes

  type Constants
  type Variables

  type UIOp = UI.Op

  // TODO create a proof obligation for the refinement
  //lemma Refines(k: Constants, s: Variables, s': Variables, uiop, dop)
  //requires Next(k, s, s', uiop, dop)
  //ensures Next(Ik(k), I(k, s), I(k, s'), uiop, dop)
}
*/

abstract module Main {
  import DAM : DiskAccessModel
  import D = Disk

  import MS = MapSpec
  import CrashSafeMap
  import opened NativeTypes
  import opened Options
  import DiskTypes
  import UI

  type UIOp = DAM.M.UIOp

  // impl defined stuff

  type Constants // impl defined
  type HeapState // impl defined (heap state)
  function HeapSet(hs: HeapState) : set<object>

  predicate Inv(k: Constants, hs: HeapState)
    reads HeapSet(hs)
  function Ik(k: Constants): DAM.M.Constants
  function I(k: Constants, hs: HeapState): DAM.M.Variables
    requires Inv(k, hs)
    reads HeapSet(hs)
  function ILBA(lba: LBA) : DAM.M.LBA

  predicate ValidSector(sector: Sector)

  function ISector(sector: Sector) : DAM.M.Sector
    requires ValidSector(sector)

  method InitState() returns (k: Constants, hs: HeapState)
    ensures Inv(k, hs)

  // DiskInterface

  function method BlockSize() : uint64 { 8*1024*1024 }

  type LBA = DiskTypes.LBA
  type Sector = DiskTypes.ByteSector
  type DiskOp = D.DiskOp<LBA, Sector>

  predicate ValidDiskOp(dop: DiskOp)
  {
    match dop {
      case ReadOp(lba, sector) => ValidSector(sector)
      case WriteOp(lba, sector) => ValidSector(sector)
      case NoDiskOp => true
    }
  }

  class DiskIOHandler {
    method {:axiom} write(lba: LBA, sector: array<byte>)
    modifies this;
    requires diskOp() == D.NoDiskOp;
    requires sector.Length == BlockSize() as int
    requires ValidSector(sector[..])
    ensures diskOp() == D.WriteOp(lba, sector[..]);

    method {:axiom} read(lba: LBA) returns (sector: array<byte>)
    modifies this
    requires diskOp() == D.NoDiskOp
    ensures diskOp() == D.ReadOp(lba, sector[..])
    ensures sector.Length == BlockSize() as int
    ensures ValidSector(sector[..])

    function {:axiom} diskOp() : DiskOp
    reads this
    ensures ValidDiskOp(diskOp())

    predicate initialized()
    reads this
    {
      diskOp() == D.NoDiskOp
    }
  }

  function IDiskOp(diskOp: DiskOp) : DAM.M.DiskOp
  requires ValidDiskOp(diskOp)
  {
    match diskOp {
      case WriteOp(lba, sector) => D.WriteOp(ILBA(lba), ISector(sector))
      case ReadOp(lba, sector) => D.ReadOp(ILBA(lba), ISector(sector))
      case NoDiskOp => D.NoDiskOp
    }
  }

  // Implementation of the state transitions

  method handleSync(k: Constants, hs: HeapState, io: DiskIOHandler)
  returns (success: bool)
  requires io.initialized()
  requires Inv(k, hs)
  modifies HeapSet(hs)
  modifies io
  ensures Inv(k, hs)
  ensures ValidDiskOp(io.diskOp())
  ensures DAM.M.Next(Ik(k), old(I(k, hs)), I(k, hs),
    if success then UI.SyncOp else UI.NoOp,
    IDiskOp(io.diskOp()))
  // impl defined

  method handleQuery(k: Constants, hs: HeapState, io: DiskIOHandler, key: MS.Key)
  returns (v: Option<MS.Value>)
  requires io.initialized()
  requires Inv(k, hs)
  modifies HeapSet(hs)
  modifies io
  ensures Inv(k, hs)
  ensures ValidDiskOp(io.diskOp())
  ensures DAM.M.Next(Ik(k), old(I(k, hs)), I(k, hs),
    if v.Some? then UI.GetOp(key, v.value) else UI.NoOp,
    IDiskOp(io.diskOp()))
  // impl defined

  method handleInsert(k: Constants, hs: HeapState, io: DiskIOHandler, key: MS.Key, value: MS.Value)
  returns (success: bool)
  requires io.initialized()
  requires Inv(k, hs)
  modifies HeapSet(hs)
  modifies io
  ensures Inv(k, hs)
  ensures ValidDiskOp(io.diskOp())
  ensures DAM.M.Next(Ik(k), old(I(k, hs)), I(k, hs),
    if success then UI.PutOp(key, value) else UI.NoOp,
    IDiskOp(io.diskOp()))
  // impl defined


  // TODO add proof obligation that the InitState together with the initial disk state
  // from mkfs together refine to the initial state of the BlockCacheSystem.

  function SystemIk(k: DAM.Constants) : CrashSafeMap.Constants
  function SystemI(k: DAM.Constants, s: DAM.Variables) : CrashSafeMap.Variables
  requires DAM.Inv(k, s)

  lemma SystemRefinesCrashSafeMapInit(
    k: DAM.Constants, s: DAM.Variables)
  requires DAM.Init(k, s)
  ensures DAM.Inv(k, s)
  ensures CrashSafeMap.Init(SystemIk(k), SystemI(k, s))

  lemma SystemRefinesCrashSafeMapNext(
    k: DAM.Constants, s: DAM.Variables, s': DAM.Variables, uiop: DAM.CrashableUIOp)
  requires DAM.Inv(k, s)
  requires DAM.Next(k, s, s', uiop)
  ensures DAM.Inv(k, s')
  ensures CrashSafeMap.Next(SystemIk(k), SystemI(k, s), SystemI(k, s'), uiop)
}
