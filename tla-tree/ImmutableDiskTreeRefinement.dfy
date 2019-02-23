include "CrashableMap.dfy"
include "ImmutableDiskTreeInterpretation.dfy"

module ImmutableDiskTreeRefinement {
import opened KVTypes
import opened TreeTypes
import ImmutableDiskTreeImpl
import opened ImmutableDiskTree
import opened ImmutableDiskTreeInv
import opened ImmutableDiskTreeHeight
import opened ImmutableDiskTreeContent
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

function DiskView(k:Constants, s:Variables) : (diskView:View)
    requires WFDiskState(k, s)
    ensures ImmutableDiskTreeImpl.FullView(k.impl, diskView)
{
    ImmutableDiskTreeImpl.ViewOfDisk(s.disk.sectors)
}

predicate SysInv(k:Constants, s:Variables)
{
    && WFDiskState(k, s)
    && TreeInv(k.impl, s.impl, DiskView(k, s))  // TODO remove this dependency until GC time
    && CacheLbasFitOnDisk(k.impl, s.impl)
    && OneDatumPerKeyInv(LookupView(k.impl, s.impl.ephemeralTable, ViewThroughCache(k.impl, s.impl, DiskView(k, s))))
}

// I rewritten from ImmutableDiskTree namespace.
function Jk(k:Constants) : CrashableMap.Constants
{
    Ik(k.impl)
}

function J(k:Constants, s:Variables) : CrashableMap.Variables
    requires SysInv(k, s)
{
    I(k.impl, s.impl, DiskView(k, s))
}

lemma InvImpliesRefinementInit(k:Constants, s:Variables)
    requires Init(k, s)
    requires SysInv(k, s)
    ensures CrashableMap.Init(Jk(k), J(k, s))
{
    reveal_AllValueLookups();
    reveal_AllKeys();
    reveal_ReachableValues();
    assert ILookupView(PersistentLookupView(k.impl, DiskView(k, s))) == CrashableMap.EmptyMap();    // OBSERVE
}

function FetchStep(k:Constants, s:Variables, s':Variables) : (step:Step)
    requires Next(k, s, s')
    ensures NextStep(k, s, s', step)
{
    reveal_Next();
    var step :| NextStep(k, s, s', step);
    step
}

//lemma ViewOfCacheImpliesInCache()
    //requires 

lemma ViewOfCacheNestsInViewThroughCache(k:Constants, s:Variables)
    requires WFDiskState(k, s)
    requires CacheLbasFitOnDisk(k.impl, s.impl)
    ensures ViewsNest(k.impl,
        ImmutableDiskTreeImpl.ViewOfCache(s.impl.cache),
        ViewThroughCache(k.impl, s.impl, DiskView(k, s)))
{
    ImmutableDiskTreeImpl.reveal_ViewOfCache();
    reveal_ViewThroughCache();
    var cacheView := ImmutableDiskTreeImpl.ViewOfCache(s.impl.cache);   // OBSERVE trigger
}

lemma LemmaQueryNext(k:Constants, s:Variables, s':Variables, step:Step)
    requires Next(k, s, s')
    requires SysInv(k, s)
    requires SysInv(k, s')
    requires NextStep(k, s, s', step)
    requires step.impl.QueryActionStep?
    requires step.impl.datum.value != EmptyValue();
    ensures CrashableMap.NextStep(Jk(k), J(k, s), J(k, s'), CrashableMap.QueryStep(step.impl.datum))
{
    reveal_AllValueLookups();
    ViewOfCacheNestsInViewThroughCache(k, s);
    reveal_AllKeys();
    reveal_ReachableValues();
}

lemma InvImpliesRefinementNext(k:Constants, s:Variables, s':Variables)
    requires Next(k, s, s')
    requires SysInv(k, s)
    requires SysInv(k, s')
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
            if (datum.value != EmptyValue()) {
                LemmaQueryNext(k, s, s', step);
            } else {
                assume false;
            }
        }
        case InsertActionStep(edit, datum) => {
            assume false;
            assert CrashableMap.Write(Ik, Is, Is', datum);
            assert CrashableMap.NextStep(Ik, Is, Is', CrashableMap.WriteStep(datum));
        }
        case DeleteActionStep(edit, datum) => {
            assume false;
            var emptyWrite := Datum(datum.key, EmptyValue());
            assert CrashableMap.Write(Ik, Is, Is', emptyWrite);
            assert CrashableMap.NextStep(Ik, Is, Is', CrashableMap.WriteStep(emptyWrite));
        }
        case ExpandActionStep(j) => {
            assume false;
            assert CrashableMap.Stutter(Ik, Is, Is');
        }
        case ContractActionStep(j) => {
            assume false;
            assert CrashableMap.Stutter(Ik, Is, Is');
        }
        case WriteBackActionStep(lba) => {
            assume false;
            assert CrashableMap.Stutter(Ik, Is, Is');
            assert CrashableMap.NextStep(Ik, Is, Is', CrashableMap.StutterStep);
        }
        case EmitTableActionStep(persistentTi, super, tblSectorIdx) => {
            assume false;
            assert CrashableMap.Stutter(Ik, Is, Is');
            assert CrashableMap.NextStep(Ik, Is, Is', CrashableMap.StutterStep);
        }
        case CommitActionStep(persistentTi, super) => {
            assume false;
            assert CrashableMap.PersistWrites(Ik, Is, Is', 1);
        }
        case CrashActionStep => {
            assume false;
            assert CrashableMap.SpontaneousCrash(Ik, Is, Is');
        }
        case RecoverActionStep(super, persistentTl) => {
            assume false;
            assert CrashableMap.Stutter(Ik, Is, Is');
        }
        case CacheFaultActionStep(lba, sector) => {
            assume false;
            assert CrashableMap.Stutter(Ik, Is, Is');
        }
        case CacheEvictActionStep(lba) => {
            assume false;
            assert CrashableMap.Stutter(Ik, Is, Is');
        }
    }
}

} // module ImmutableDiskTreeRefinement
