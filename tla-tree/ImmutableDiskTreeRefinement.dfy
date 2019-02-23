include "CrashableMap.dfy"
include "ImmutableDiskTreeInterpretation.dfy"

module ImmutableDiskTreeRefinement {
import opened KVTypes
import opened TreeTypes
import ImmutableDiskTreeImpl
import opened ImmutableDiskTree
import opened ImmutableDiskTreeInv
import opened ImmutableDiskTreeHeight
import opened ImmutableDiskTreeInterpretation
import opened MissingLibrary
import CrashableMap

type View = ImmutableDiskTreeImpl.View
function DiskSize(k:Constants) : int { ImmutableDiskTreeImpl.DiskSize(k.impl) }
function ROOT_ADDR() : TableAddress { ImmutableDiskTreeImpl.ROOT_ADDR() }

predicate WFDiskState(k:Constants, s:Variables)
{
    && TreeDisk.WF(k.disk, s.disk)
    && k.disk.size == DiskSize(k)
}

function {:opaque} DiskView(k:Constants, s:Variables) : (diskView:View)
    requires WFDiskState(k, s)
    ensures FullView(k.impl, diskView)
    ensures forall lba :: 0 <= lba < DiskSize(k) ==> diskView[lba] == s.disk.sectors[lba]
{
    map lba | 0 <= lba < DiskSize(k) :: s.disk.sectors[lba]
}

// I rewritten from ImmutableDiskTree namespace.
function Jk(k:Constants) : CrashableMap.Constants
{
    Ik(k.impl)
}

function J(k:Constants, s:Variables) : CrashableMap.Variables
    requires WFDiskState(k, s)
    requires TreeInv(k.impl, s.impl, DiskView(k, s))
{
    I(k.impl, s.impl, DiskView(k, s))
}

lemma InvImpliesRefinementInit(k:Constants, s:Variables)
    requires Init(k, s)
    requires TreeInv(k.impl, s.impl, DiskView(k, s))
    ensures CrashableMap.Init(Jk(k), J(k, s))
{
    reveal_ISubtreePrefixView();
    reveal_ISlotView();
    var tv := PersistentTreeView(k.impl, DiskView(k, s));
    assert ISubtreeView(tv, ROOT_ADDR()) == ISubtreePrefixView(tv, ROOT_ADDR(), /*slotCount*/ 1); // OBSERVE
    assert IPersistentView(k.impl, DiskView(k, s)) == CrashableMap.EmptyMap(); // OBSERVE
}

function FetchStep(k:Constants, s:Variables, s':Variables) : (step:Step)
    requires Next(k, s, s')
    ensures NextStep(k, s, s', step)
{
    reveal_Next();
    var step :| NextStep(k, s, s', step);
    step
}

lemma InvImpliesRefinementNext(k:Constants, s:Variables, s':Variables)
    requires Next(k, s, s')
    requires TreeInv(k.impl, s.impl, DiskView(k, s))
    requires TreeInv(k.impl, s'.impl, DiskView(k, s'))
    ensures CrashableMap.WF(J(k, s))
    ensures CrashableMap.WF(J(k, s))
    ensures CrashableMap.Next(Jk(k), J(k, s), J(k, s'))
{
    var Ik := Jk(k);
    var Is := J(k, s);
    var Is' := J(k, s');
    var step := FetchStep(k, s, s');

    match step.impl {
        case QueryActionStep(lookup, datum) => {
            assert CrashableMap.Query(Ik, Is, Is', datum);
        }
        case InsertActionStep(edit, datum) => {
            assert CrashableMap.Write(Ik, Is, Is', datum);
        }
        case DeleteActionStep(edit, datum) => {
            assert CrashableMap.Write(Ik, Is, Is', Datum(datum.key, EmptyValue()));
        }
        case ExpandActionStep(j) => {
            assert CrashableMap.Stutter(Ik, Is, Is');
        }
        case ContractActionStep(j) => {
            assert CrashableMap.Stutter(Ik, Is, Is');
        }
        case WriteBackActionStep(lba) => {
            assert CrashableMap.Stutter(Ik, Is, Is');
        }
        case EmitTableActionStep(persistentTi, super, tblSectorIdx) => {
            assert CrashableMap.Stutter(Ik, Is, Is');
        }
        case CommitActionStep(persistentTi, super) => {
            assert CrashableMap.PersistWrites(Ik, Is, Is', 1);
        }
        case CrashActionStep => {
            assert CrashableMap.SpontaneousCrash(Ik, Is, Is');
        }
        case RecoverActionStep(super, persistentTl) => {
            assert CrashableMap.Stutter(Ik, Is, Is');
        }
        case CacheFaultActionStep(lba, sector) => {
            assert CrashableMap.Stutter(Ik, Is, Is');
        }
        case CacheEvictActionStep(lba) => {
            assert CrashableMap.Stutter(Ik, Is, Is');
        }
    }
}

} // module ImmutableDiskTreeRefinement
