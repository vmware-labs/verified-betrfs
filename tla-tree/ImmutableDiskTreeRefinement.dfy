include "CrashableMap.dfy"
include "ImmutableDiskTreeInterpretation.dfy"

module ImmutableDiskTreeRefinement {
import opened KVTypes
import opened TreeTypes
import opened ImmutableDiskTree
import opened ImmutableDiskTreeInv
import opened ImmutableDiskTreeHeight
import opened ImmutableDiskTreeInterpretation
import opened MissingLibrary
import CrashableMap

lemma InvImpliesRefinementInit(k:Constants, s:Variables)
    requires Init(k, s)
    requires TreeInv(k, s)
    ensures CrashableMap.Init(Ik(k), I(k, s))
{
    reveal_ISubtreePrefixView();
    reveal_ISlotView();
    var tv := PersistentTreeView(k, s);
    assert ISubtreeView(tv, ROOT_ADDR()) == ISubtreePrefixView(tv, ROOT_ADDR(), /*slotCount*/ 1); // OBSERVE
    assert IPersistentView(k, s) == CrashableMap.EmptyMap(); // OBSERVE
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
    requires TreeInv(k, s)
    requires TreeInv(k, s')
    ensures CrashableMap.WF(I(k, s))
    ensures CrashableMap.WF(I(k, s'))
    ensures CrashableMap.Next(Ik(k), I(k, s), I(k, s'))
{
    var Ik := Ik(k);
    var Is := I(k, s);
    var Is' := I(k, s');
    var step := FetchStep(k, s, s');

    match step {
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
