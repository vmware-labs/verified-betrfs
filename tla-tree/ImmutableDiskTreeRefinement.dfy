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
    requires step.impl.value.Some?
    ensures CrashableMap.NextStep(Jk(k), J(k, s), J(k, s'), CrashableMap.QueryStep(step.impl.key, step.impl.value))
{
    reveal_AllValueLookups();
    ViewOfCacheNestsInViewThroughCache(k, s);
    reveal_AllKeys();
    reveal_ReachableValues();
}

lemma WFDiskStateInduction(k:Constants, s:Variables, s':Variables, step:Step)
    requires NextStep(k, s, s', step)
    requires SysInv(k, s)
    ensures WFDiskState(k, s');
{
    match step.disk {
        case ReadStep(lba, sector) => {
            assert WFDiskState(k, s');
        }
        case WriteStep(lba, sector) => {
            assert WFDiskState(k, s');
        }
        case IdleStep => {
            assert WFDiskState(k, s');
        }
    }
}

lemma TreeInvInduction(k:Constants, s:Variables, s':Variables, step:Step)
    requires NextStep(k, s, s', step)
    requires SysInv(k, s)
    ensures WFDiskState(k, s');
    ensures TreeInv(k.impl, s'.impl, DiskView(k, s'))
{
    assume false;    // TODO I think we're going to end up deleting TreeInv anyway.
}

function LookupForDatum(lv:LookupView, datum:Datum) : (lookup:ImmutableDiskTreeImpl.Lookup)
    requires datum in AllValueLookups(lv)
    ensures ValidValueLookup(lv, lookup)
    ensures ImmutableDiskTreeImpl.TerminalSlot(lookup).datum == datum
{
    reveal_AllValueLookups();
    var lookup :| ValidValueLookup(lv, lookup) && ImmutableDiskTreeImpl.TerminalSlot(lookup).datum == datum;
    lookup
}

lemma DifferentDatums(k:Constants, s:Variables, s':Variables, step:Step, lv:LookupView, datum1:Datum, datum2:Datum,
    lookup1:ImmutableDiskTreeImpl.Lookup, lookup2:ImmutableDiskTreeImpl.Lookup, commonPrefixLength:int)
    requires NextStep(k, s, s', step)
    requires SysInv(k, s)
    requires lv == EphemeralLookupView(k.impl, s'.impl, DiskView(k, s'))
    requires (datum1 in AllValueLookups(lv) && datum2 in AllValueLookups(lv) && datum1.key == datum2.key)
    requires lookup1 == LookupForDatum(lv, datum1)
    requires lookup2 == LookupForDatum(lv, datum2)
    requires IsGreatestCommonPrefix(lookup1, lookup2, commonPrefixLength)
    requires commonPrefixLength == |lookup1.layers|
    ensures DatumsUniqueInView(lv, datum1, datum2)
{
}

lemma DivergentLayerAgreesOnAddrAndNodes(lv:LookupView, lookup1:ImmutableDiskTreeImpl.Lookup, lookup2:ImmutableDiskTreeImpl.Lookup, i:int)
    requires ImmutableDiskTreeImpl.ValidLookupInView(lv.k, lv.table, lv.view, lookup1)
    requires ImmutableDiskTreeImpl.ValidLookupInView(lv.k, lv.table, lv.view, lookup2)
    requires 0 <= i < |lookup1.layers|
    requires 0 <= i < |lookup2.layers|
    requires i==0 || lookup1.layers[i-1] == lookup2.layers[i-1]
    ensures lookup1.layers[i].addr == lookup2.layers[i].addr
    ensures lookup1.layers[i].node == lookup2.layers[i].node
{
    assert ImmutableDiskTreeImpl.LookupHonorsPointerLinksAtLayer(lookup1, i);   // OBSERVE trigger
    assert ImmutableDiskTreeImpl.LookupHonorsPointerLinksAtLayer(lookup2, i);   // OBSERVE trigger
}

lemma OneDatumPerKeyInvInduction(k:Constants, s:Variables, s':Variables, step:Step)
    requires NextStep(k, s, s', step)
    requires SysInv(k, s)
    ensures WFDiskState(k, s');
    ensures OneDatumPerKeyInv(LookupView(k.impl, s'.impl.ephemeralTable, ViewThroughCache(k.impl, s'.impl, DiskView(k, s'))))
{
    WFDiskStateInduction(k, s, s', step);
    var lv := EphemeralLookupView(k.impl, s'.impl, DiskView(k, s'));
    assert LookupView(k.impl, s'.impl.ephemeralTable, ViewThroughCache(k.impl, s'.impl, DiskView(k, s')))
        == lv;
    forall datum1, datum2
        ensures DatumsUniqueInView(lv, datum1, datum2)
    {
        if (datum1 in AllValueLookups(lv) && datum2 in AllValueLookups(lv) && datum1.key == datum2.key) {
            var lookup1 := LookupForDatum(lv, datum1);
            var lookup2 := LookupForDatum(lv, datum2);
            var commonPrefixLength := CommonPrefixOfLookups(lookup1, lookup2);
            if (commonPrefixLength == |lookup1.layers| == |lookup2.layers|) {
                assume false;   // XXX timeout for now
                ExploitLookupsAgree(lookup1, lookup2, commonPrefixLength, commonPrefixLength-1);    // XXX pull up
                assert DatumsUniqueInView(lv, datum1, datum2);
            } else if (commonPrefixLength < |lookup1.layers| && commonPrefixLength < |lookup2.layers|) {
                // at the first divergent layer, the addr & node agree because the previous layer pointed at it.
                var j:=commonPrefixLength;
                if (commonPrefixLength == 0) {
                  assert commonPrefixLength == 0;
                } else if (commonPrefixLength > 0) {
                    var i := commonPrefixLength-1;
                    ExploitLookupsAgree(lookup1, lookup2, commonPrefixLength, i);
                    assert lookup1.layers[i] == lookup2.layers[i];
                    assert i == j-1;
                    assert lookup1.layers[i] == lookup1.layers[j-1];
                    calc {
                        lookup1.layers[j-1];
                            { assert i == j-1; }
                        lookup1.layers[i];
                        lookup2.layers[i];
                        lookup2.layers[j-1];
                    }
                    assert lookup1.layers[j-1] == lookup2.layers[j-1];
                } else {
                    assert false;
                }
    assert j==0 || lookup1.layers[j-1] == lookup2.layers[j-1];
                assume false; // XXX
                DivergentLayerAgreesOnAddrAndNodes(lv, lookup1, lookup2, commonPrefixLength);
                assert lookup1.layers[commonPrefixLength].addr == lookup2.layers[commonPrefixLength].addr;
                assert lookup1.layers[commonPrefixLength].node == lookup2.layers[commonPrefixLength].node;
                // The slots must disagree (by an argument later?)
                assert lookup1.layers[commonPrefixLength].slot != lookup2.layers[commonPrefixLength].slot;
                // and hence the ranges don't overlap.
                var range1 := lookup1.layers[commonPrefixLength].slotRange;
                var range2 := lookup2.layers[commonPrefixLength].slotRange;
                //assert RangesDisjoint(range1, range2);
                assert DatumsUniqueInView(lv, datum1, datum2);
            } else {
                assume false; // XXX
                if (commonPrefixLength == |lookup1.layers|) {
                    DifferentDatums(k, s, s', step, lv, datum1, datum2, lookup1, lookup2, commonPrefixLength);
                } else {
                    assert commonPrefixLength == |lookup2.layers|;
                    IsGreatestCommonPrefixIsSymmetric(lookup1, lookup2, commonPrefixLength);
                    DifferentDatums(k, s, s', step, lv, datum2, datum1, lookup2, lookup1, commonPrefixLength);
                }
            }
//                assert LookupHonorsRanges(lookup1);
//                assert LookupHonorsRanges(lookup2);
//                assert datum1 == ImmutableDiskTreeImpl.TerminalSlot(lookup1).datum;
//                assert datum2 == ImmutableDiskTreeImpl.TerminalSlot(lookup2).datum;
    ////            if (commonPrefixLength == |lookup1.layers|) {
    ////                //var termLayer1 := lookup1.layers[commonPrefixLength - 1];
    ////                //assert termLayer1.node.slots[termLayer1.slot].Pointer?;
    ////                assert false;
    ////            }
    ////            assert commonPrefixLength < |lookup1.layers|;
    //            if (commonPrefixLength == |lookup2.layers|) {
    //                var termLayer1 := lookup1.layers[commonPrefixLength - 1];
    //                //assert 0<=commonPrefixLength<|lookup1.layers|;
    //                assert ImmutableDiskTreeImpl.LookupHonorsPointerLinksAtLayer(lookup1, commonPrefixLength);  // OBSERVE
    //                assert commonPrefixLength - 1 != 0; // this line causes timeouts by itself!
    //                assert termLayer1.node.slots[termLayer1.slot].Pointer?;
    //
    //                var termLayer2 := lookup2.layers[commonPrefixLength - 1];
    //                assert termLayer2.node.slots[termLayer2.slot].Value?;
    //                /*
    //                assert ValidValueLookup(lv, lookup2);
    //                assert ImmutableDiskTreeImpl.ValidLookupInView(lv.k, lv.table, lv.view, lookup2);
    //                assert ImmutableDiskTreeImpl.LookupHonorsPointerLinks(lookup2);
    //                assert 0<=commonPrefixLength<|lookup2.layers|;
    //                assert ImmutableDiskTreeImpl.LookupHonorsPointerLinksAtLayer(lookup2, commonPrefixLength);
    //                assert termLayer2.node.slots[termLayer2.slot].Pointer?;
    //                */
    //                assert false;
    //            }
    //            assert commonPrefixLength < |lookup2.layers|;
    //            assert false;
    //            assert commonPrefixLength < |lookup2.layers|;   // Else commonPrefixLength slot isn't a Value.
    //
    //            assert lookup1.layers[commonPrefixLength].node == lookup2.layers[commonPrefixLength].node;
    //            assert lookup1.layers[commonPrefixLength].slot != lookup2.layers[commonPrefixLength].slot;
    //            assert lookup1.layers[commonPrefixLength].slotRange != lookup2.layers[commonPrefixLength].slotRange;
    //            // They're going to have different ranges.
        }
        assert DatumsUniqueInView(lv, datum1, datum2);
    }
}

lemma InvInduction(k:Constants, s:Variables, s':Variables, step:Step)
    requires NextStep(k, s, s', step)
    requires SysInv(k, s)
    ensures SysInv(k, s')
{
    assert WFDiskState(k, s');
    assert CacheLbasFitOnDisk(k.impl, s'.impl);
    TreeInvInduction(k, s, s', step);
    OneDatumPerKeyInvInduction(k, s, s', step);
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
        case QueryActionStep(lookup, key, value) => {
            if (value.Some?) {
                LemmaQueryNext(k, s, s', step);
            } else {
                assume false;
            }
        }
        case InsertActionStep(edit, key, oldValue, newValue) => {
            assume false;
            assert CrashableMap.Write(Ik, Is, Is', key, Some(newValue));
            assert CrashableMap.NextStep(Ik, Is, Is', CrashableMap.WriteStep(key, Some(newValue)));
        }
        case DeleteActionStep(edit, key, oldValue) => {
            assume false;
            assert CrashableMap.Write(Ik, Is, Is', key, None);
            assert CrashableMap.NextStep(Ik, Is, Is', CrashableMap.WriteStep(key, None));
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
