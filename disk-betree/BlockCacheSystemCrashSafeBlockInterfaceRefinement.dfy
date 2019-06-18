include "BlockCacheSystem.dfy"
include "CrashSafe.dfy"
include "../lib/Maps.dfy"

module BlockCacheSystemCrashSafeBlockInterfaceRefinement {
  import BCS = BlockCacheSystem
  import CSBI = CrashSafeBlockInterface

  import opened Maps

  import BC = BlockCache
  import BI = BlockInterface
  import D = Disk
  import DiskBetree
  type Node<Value> = DiskBetree.Node<Value>
  type Reference = BI.Reference
  type DiskOp<T> = BC.DiskOp<T>

  function Ik(k: BCS.Constants) : CSBI.Constants
  {
    k.machine.constants
  }

  function RefGraph(m: map<Reference, Node>) : imap<Reference, iset<Reference>>
  {
    imap ref | ref in m :: BC.Successors(m[ref])
  }

  function I<Value>(k: BCS.Constants, s: BCS.Variables) : CSBI.Variables<Node<Value>>
  requires BCS.Inv(k, s)
  {
    var persistentGraph := BCS.PersistentGraph(k, s);
    var ephemeralGraph := if s.machine.Ready? then BCS.EphemeralGraph(k, s) else persistentGraph;
    CSBI.Variables(
      BI.Variables(
        MapToImap(persistentGraph),
        RefGraph(persistentGraph)
      ),
      BI.Variables(
        MapToImap(ephemeralGraph),
        RefGraph(ephemeralGraph)
      )
    )
  }

  lemma RefinesInit(k: BCS.Constants, s: BCS.Variables)
  requires BCS.Init(k, s)
  ensures BCS.Inv(k, s)
  ensures CSBI.Init(Ik(k), I(k, s))

  lemma RefinesWriteBack(k: BCS.Constants, s: BCS.Variables, s': BCS.Variables, dop: DiskOp, ref: Reference)
  requires BCS.Inv(k, s)
  requires BCS.Inv(k, s')
  requires BC.WriteBack(k.machine, s.machine, s'.machine, dop, ref)
  requires D.Write(k.disk, s.disk, s'.disk, dop)
  ensures CSBI.Next(Ik(k), I(k, s), I(k, s'))
  {
    assert I(k, s).persistent == I(k, s').persistent;
    //assert BI.NextStep(I(k, s).ephemeral, I(k, s').ephemeral, BI.Stutter);
    //assert CSBI.NextStep(Ik(k), I(k, s), I(k, s'), CSBI.EphemeralMoveStep);
  }

  lemma RefinesWriteBackSuperblock(k: BCS.Constants, s: BCS.Variables, s': BCS.Variables, dop: DiskOp)
  requires BCS.Inv(k, s)
  requires BCS.Inv(k, s')
  requires BC.WriteBackSuperblock(k.machine, s.machine, s'.machine, dop)
  requires D.Write(k.disk, s.disk, s'.disk, dop)
  ensures CSBI.Next(Ik(k), I(k, s), I(k, s'))

  lemma RefinesDirty(k: BCS.Constants, s: BCS.Variables, s': BCS.Variables, dop: DiskOp, ref: Reference, block: Node)
  requires BCS.Inv(k, s)
  requires BCS.Inv(k, s')
  requires BC.Dirty(k.machine, s.machine, s'.machine, dop, ref, block)
  requires D.Stutter(k.disk, s.disk, s'.disk, dop)
  ensures CSBI.Next(Ik(k), I(k, s), I(k, s'))

  lemma RefinesAlloc(k: BCS.Constants, s: BCS.Variables, s': BCS.Variables, dop: DiskOp, ref: Reference, block: Node)
  requires BCS.Inv(k, s)
  requires BCS.Inv(k, s')
  requires BC.Alloc(k.machine, s.machine, s'.machine, dop, ref, block)
  requires D.Stutter(k.disk, s.disk, s'.disk, dop)
  ensures CSBI.Next(Ik(k), I(k, s), I(k, s'))

  lemma RefinesUnalloc(k: BCS.Constants, s: BCS.Variables, s': BCS.Variables, dop: DiskOp, ref: Reference)
  requires BCS.Inv(k, s)
  requires BCS.Inv(k, s')
  requires BC.Unalloc(k.machine, s.machine, s'.machine, dop, ref)
  requires D.Stutter(k.disk, s.disk, s'.disk, dop)
  ensures CSBI.Next(Ik(k), I(k, s), I(k, s'))

  lemma RefinesPageIn(k: BCS.Constants, s: BCS.Variables, s': BCS.Variables, dop: DiskOp, ref: Reference)
  requires BCS.Inv(k, s)
  requires BCS.Inv(k, s')
  requires BC.PageIn(k.machine, s.machine, s'.machine, dop, ref)
  requires D.Read(k.disk, s.disk, s'.disk, dop)
  ensures CSBI.Next(Ik(k), I(k, s), I(k, s'))

  lemma RefinesPageInSuperblock(k: BCS.Constants, s: BCS.Variables, s': BCS.Variables, dop: DiskOp)
  requires BCS.Inv(k, s)
  requires BCS.Inv(k, s')
  requires BC.PageInSuperblock(k.machine, s.machine, s'.machine, dop)
  requires D.Read(k.disk, s.disk, s'.disk, dop)
  ensures CSBI.Next(Ik(k), I(k, s), I(k, s'))

  lemma RefinesEvict(k: BCS.Constants, s: BCS.Variables, s': BCS.Variables, dop: DiskOp, ref: Reference)
  requires BCS.Inv(k, s)
  requires BCS.Inv(k, s')
  requires BC.Evict(k.machine, s.machine, s'.machine, dop, ref)
  requires D.Stutter(k.disk, s.disk, s'.disk, dop)
  ensures CSBI.Next(Ik(k), I(k, s), I(k, s'))

  lemma RefinesCrashStep(k: BCS.Constants, s: BCS.Variables, s': BCS.Variables)
  requires BCS.Inv(k, s)
  requires BCS.Inv(k, s')
  requires BC.Init(k.machine, s'.machine)
  requires s.disk == s'.disk
  ensures CSBI.Next(Ik(k), I(k, s), I(k, s'))

  lemma RefinesNextStep(k: BCS.Constants, s: BCS.Variables, s': BCS.Variables, step: BCS.Step)
  requires BCS.Inv(k, s)
  requires BCS.NextStep(k, s, s', step)
  ensures BCS.Inv(k, s')
  ensures CSBI.Next(Ik(k), I(k, s), I(k, s'))
  {
    BCS.NextPreservesInv(k, s, s');
    match step {
      case MachineStep(dop: DiskOp) => {
        var mstep :| BC.NextStep(k.machine, s.machine, s'.machine, dop, mstep);
        match mstep {
          case WriteBackStep(ref) => RefinesWriteBack(k, s, s', dop, ref);
          case WriteBackSuperblockStep => RefinesWriteBackSuperblock(k, s, s', dop);
          case DirtyStep(ref, block) => RefinesDirty(k, s, s', dop, ref, block);
          case AllocStep(ref, block) => RefinesAlloc(k, s, s', dop, ref, block);
          case UnallocStep(ref) => RefinesUnalloc(k, s, s', dop, ref);
          case PageInStep(ref) => RefinesPageIn(k, s, s', dop, ref);
          case PageInSuperblockStep => RefinesPageInSuperblock(k, s, s', dop);
          case EvictStep(ref) => RefinesEvict(k, s, s', dop, ref);
        }
      }
      case CrashStep => {
        RefinesCrashStep(k, s, s');
      }
    }
  }
}
