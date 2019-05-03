include "CrashableMap.dfy"
include "ImmutableDiskTreeCacheInv.dfy"

module ImmutableDiskTreeRefinement {
import opened KVTypes
import opened TreeTypes
import ImmutableDiskTreeImpl
import opened ImmutableDiskTree
import opened ImmutableDiskTreeInv
import opened ImmutableDiskTreeHeight
import opened ImmutableDiskTreeContent
import opened ImmutableDiskTreeInterpretation
import opened ImmutableDiskTreeCacheInv 
import opened MissingLibrary
import CrashableMap

type View = Impl.View
function DiskSize(k:Constants) : int { Impl.DiskSize(k.impl) }
function ROOT_ADDR() : TableAddress { Impl.ROOT_ADDR() }

predicate WFDiskState(k:Constants, s:Variables)
{
    && TreeDisk.WF(k.disk, s.disk)
    && k.disk.size == DiskSize(k)
}

function DiskView(k:Constants, s:Variables) : (diskView:View)
    requires WFDiskState(k, s)
    ensures Impl.FullView(k.impl, diskView)
{
    Impl.ViewOfDisk(s.disk.sectors)
}

function LV(k:Constants, s:Variables) : LookupView
    requires WFDiskState(k, s)
{
    LookupView(k.impl, s.impl.ephemeralTable, ViewThroughCache(k.impl, s.impl, DiskView(k, s)))
}

predicate SysInv(k:Constants, s:Variables)
{
    && WFDiskState(k, s)
    && TreeInv(k.impl, s.impl, DiskView(k, s))  // TODO remove this dependency until GC time

    && ValidCacheIndicesInv(k, s)
    && CleanCacheSectorsMatchDiskInv(k, s)

    && CacheLbasFitOnDisk(k.impl, s.impl)
    && PivotsOrderedInv(LV(k, s))
    && PivotsHonorRangesInv(LV(k, s))
    && DatumsAreInTheRightPlaceInv(LV(k, s))
    && OneDatumPerKeyInv(LV(k, s))
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
    forall lookup | ValidValueLookup(PersistentLookupView(k.impl, DiskView(k, s)), lookup)
        ensures false
    {
        if (Impl.ValidLayerIndex(lookup, 0)
            && Impl.LookupHasValidAddresses(k.impl, lookup)
            && |lookup.layers|>1) {
            assert Impl.LookupHonorsPointerLinksAtLayer(lookup, 1);    // instantiate
            assert false;
        }
    }
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
        Impl.ViewOfCache(s.impl.cache),
        ViewThroughCache(k.impl, s.impl, DiskView(k, s)))
{
    Impl.reveal_ViewOfCache();
    //reveal_ViewThroughCache();
    var cacheView := Impl.ViewOfCache(s.impl.cache);   // OBSERVE trigger
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
    Impl.reveal_NextStep();
    reveal_AllValueLookups();
    ViewOfCacheNestsInViewThroughCache(k, s);
    reveal_AllKeys();
    reveal_ReachableValues();
    var lv := LookupView(k.impl, s.impl.ephemeralTable, ViewThroughCache(k.impl, s.impl, DiskView(k, s)));

    // Instantiate DatumsUniqueInView from OneDatumPerKeyInv to demonstrate
    // that the lookup QueryAction used to satisfy the query is unique, and
    // hence matches whatever is allowed by the refinement interperetation.
    if (step.impl.value.Some?) {
        var datum := Datum(step.impl.key, step.impl.value.value);

        forall d2 | d2 in AllValueLookups(lv) && d2.key == datum.key
            ensures d2.value == datum.value
        {
            assert DatumsUniqueInView(lv, datum, d2);
        }
    }
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

function LookupForDatum(lv:LookupView, datum:Datum) : (lookup:Impl.Lookup)
    requires datum in AllValueLookups(lv)
    ensures ValidValueLookup(lv, lookup)
    ensures Impl.TerminalSlot(lookup).datum == datum
{
    reveal_AllValueLookups();
    var lookup :| ValidValueLookup(lv, lookup) && Impl.TerminalSlot(lookup).datum == datum;
    lookup
}

lemma DivergentLayerAgreesOnAddrAndNodes(lv:LookupView, lookup1:Impl.Lookup, lookup2:Impl.Lookup, i:int)
    requires ValidLookupInLV(lv, lookup1)
    requires ValidLookupInLV(lv, lookup2)
    requires 0 <= i < |lookup1.layers|
    requires 0 <= i < |lookup2.layers|
    requires i==0 || lookup1.layers[i-1] == lookup2.layers[i-1]
    ensures lookup1.layers[i].addr == lookup2.layers[i].addr
    ensures lookup1.layers[i].node == lookup2.layers[i].node
{
    assert Impl.LookupHonorsPointerLinksAtLayer(lookup1, i);   // OBSERVE trigger
    assert Impl.LookupHonorsPointerLinksAtLayer(lookup2, i);   // OBSERVE trigger
    assert Impl.ValidLayerIndex(lookup1, i);
    assert Impl.ValidLayerIndex(lookup2, i);
}

lemma PivotsOrderedTransitive(node:Node, i1:nat, i2:nat)
    requires PivotsOrdered(node)
    requires 0 <= i1 <= i2 < |node.pivots|
    ensures KeyLeq(node.pivots[i1], node.pivots[i2])
{
    if (i1 < i2) {
        PivotsOrderedTransitive(node, i1, i2-1);
        assert PivotsOrderedAtIdx(node, i2-1);  // instantiate
        KeyLeqTransitive();
    }
}

// If two lookups agree to depth cPL, but one stops there and the other
// continues, that's just straight up nonsense: the short one must terminate in
// a Value?, and the other must have a Pointer? in the same (matching!?) slot.
lemma LookupsAtDifferentDepthsContradiction(
    k:Constants, s:Variables, s':Variables, step:Step, lv:LookupView, datum1:Datum, datum2:Datum,
    lookup1:Impl.Lookup, lookup2:Impl.Lookup, commonPrefixLength:nat)
    requires WFDiskState(k, s)
    requires WFDiskState(k, s')
    requires lv == EphemeralLookupView(k.impl, s'.impl, DiskView(k, s'))
    requires datum1 in AllValueLookups(lv)
    requires datum2 in AllValueLookups(lv)
    requires lookup1 == LookupForDatum(lv, datum1)
    requires lookup2 == LookupForDatum(lv, datum2)
    requires IsGreatestCommonPrefix(lookup1, lookup2, commonPrefixLength)
    requires commonPrefixLength == |lookup1.layers|
    requires commonPrefixLength < |lookup2.layers|
    ensures false;
{
    var i := commonPrefixLength-1;
    assert Impl.ValidLayerIndex(lookup1, i);   // instantiate
    assert Impl.ValidLayerIndex(lookup2, i);   // instantiate
    var slot1 := lookup1.layers[i].slot;
    var slot2 := lookup2.layers[i].slot;
    //assert lookup1.layers[i].node.slots[slot1].Value?;
    assert Impl.LookupHonorsPointerLinksAtLayer(lookup2, commonPrefixLength);  // instantiate
    //assert lookup2.layers[i].node.slots[slot2].Pointer?;
    ExploitLookupsAgree(lookup1, lookup2, commonPrefixLength, i);   // instantiate
    //assert lookup1.layers[i].node == lookup2.layers[i].node;
    //assert slot1 != slot2;
}

lemma DisjointRangesAsym(lv:LookupView, lookup1:Impl.Lookup, lookup2:Impl.Lookup, i:nat,
    datum1:Datum, datum2:Datum)
    requires PivotsOrderedInv(lv)
    requires ValidLookupInLV(lv, lookup1)
    requires ValidLookupInLV(lv, lookup2)
    requires i < |lookup1.layers|
    requires i < |lookup2.layers|
    requires LookupsAgreeToLen(lookup1, lookup2, i)
    requires lookup1.layers[i].node == lookup2.layers[i].node;
    requires lookup1.layers[i].slot < lookup2.layers[i].slot;
    requires Impl.RangeContains(lookup1.layers[i].slotRange, datum1.key)
    requires Impl.RangeContains(lookup2.layers[i].slotRange, datum2.key)
    ensures datum1.key != datum2.key
{
    KeyLeqTransitive();
    var node := lookup1.layers[i].node;
    var slot1 := lookup1.layers[i].slot;
    var slot2 := lookup2.layers[i].slot;

    assert KeyLeq(lookup2.layers[i].slotRange.loinc, datum2.key);
//    assert Impl.LookupHasValidSlotIndices(lookup1);
    assert Impl.ValidLayerIndex(lookup1, i);
    assert Impl.ValidLayerIndex(lookup2, i);
    assert Impl.WFNode(node);
    assert Impl.ValidSlotIndex(node, slot1);
    assert slot1 < slot2 < |node.pivots|+1;
    assert 0 <= slot1 < |node.pivots|;
    assert lookup1.layers[i].slotRange.hiexc == node.pivots[slot1];
    assert Impl.ValidSlotIndex(node, slot2);
    assert 0 <= slot2-1 < |node.pivots|;
    assert lookup2.layers[i].slotRange.loinc == node.pivots[slot2-1];

    PivotsOrderedTransitive(node, slot1, slot2-1);
    assert KeyLeq(lookup1.layers[i].slotRange.hiexc, lookup2.layers[i].slotRange.loinc);
//    assert lookup1.layers[i].slotRange.hiexc == lookup2.layers[i].slotRange.hiexc;
    assert KeyLe(datum1.key, lookup1.layers[i].slotRange.hiexc);
    assert KeyLe(datum1.key, datum2.key);
    assert datum1.key != datum2.key;
/*
LookupsHonorRanges(lv:LookupView, lookup:Lookup, datum:Datum)
    ensures RangeContains(Impl.TerminalSlot(lookup).slotRange, datum.key)
    */
}

// Keys in disjoint ranges aren't equal.
lemma DisjointRanges(lv:LookupView, lookup1:Impl.Lookup, lookup2:Impl.Lookup, i:nat,
    datum1:Datum, datum2:Datum)
    requires PivotsOrderedInv(lv)
    requires ValidLookupInLV(lv, lookup1)
    requires ValidLookupInLV(lv, lookup2)
    requires i < |lookup1.layers|
    requires i < |lookup2.layers|
    requires LookupsAgreeToLen(lookup1, lookup2, i)
    requires lookup1.layers[i].node == lookup2.layers[i].node;
    requires lookup1.layers[i].slot != lookup2.layers[i].slot;
    requires Impl.RangeContains(lookup1.layers[i].slotRange, datum1.key)
    requires Impl.RangeContains(lookup2.layers[i].slotRange, datum2.key)
    ensures datum1.key != datum2.key
{
    if (lookup1.layers[i].slot < lookup2.layers[i].slot) {
       DisjointRangesAsym(lv, lookup1, lookup2, i, datum1, datum2); 
       assert datum1.key != datum2.key;
    } else {
        LookupsAgreeToLenSymmetry(lookup1, lookup2, i);
       DisjointRangesAsym(lv, lookup2, lookup1, i, datum2, datum1); 
       assert datum2.key!=datum1.key;
       assert datum1.key != datum2.key;
    }
}


lemma KeyLeqTransitive()
    ensures forall a, b, c :: KeyLe(a,b) && KeyLe(b,c) ==> KeyLe(a,c)
    ensures forall a, b, c :: KeyLe(a,b) && KeyLeq(b,c) ==> KeyLe(a,c)
    ensures forall a, b, c :: KeyLeq(a,b) && KeyLe(b,c) ==> KeyLe(a,c)
    ensures forall a, b, c :: KeyLeq(a,b) && KeyLeq(b,c) ==> KeyLeq(a,c)
{
    KeyLeTransitive();
}

lemma LookupRangesNestStep(lv:LookupView, lookup:Impl.Lookup, j:int, k:int, key:Key)
    requires ValidLookupInLV(lv, lookup)
    requires PivotsHonorRangesInv(lv);
    requires j+1==k
    requires Impl.ValidLayerIndex(lookup, j);
    requires Impl.ValidLayerIndex(lookup, k);
    requires Impl.RangeContains(lookup.layers[k].slotRange, key)
    ensures Impl.RangeContains(lookup.layers[j].slotRange, key)
{
    // Left side
    var lslot := lookup.layers[k].slot;
    if (0 < lslot) {
        assert PivotsHonorRanges(lv, lookup, k, lslot); // instantiate
    }   // else k inherit's j's loinc

    // Right side
    var rslot := lookup.layers[k].slot;
    if (rslot < |lookup.layers[k].node.slots| - 1) {
        assert PivotsHonorRanges(lv, lookup, k, rslot + 1); // instantiate
    }   // else k inherit's j's hiexc

    KeyLeqTransitive();
}

lemma LookupRangesNest(lv:LookupView, lookup:Impl.Lookup, i:int, k:int, key:Key)
    requires ValidLookupInLV(lv, lookup)
    requires 0 <= i <= k < |lookup.layers|
    requires Impl.RangeContains(lookup.layers[k].slotRange, key)
    requires PivotsHonorRangesInv(lv);
    ensures Impl.RangeContains(lookup.layers[i].slotRange, key)
{

    if (i<k) {
        var j:=k-1;
        LookupRangesNestStep(lv, lookup, j, k, key);
        LookupRangesNest(lv, lookup, i, j, key);
    }
}

// TODO (jwilcox): right now I have to opaque NextStep. Maybe instantiating it
// with a single k,s,s' will be tolerable? Messy, though.
lemma CautiouslyRevealNextStep(k:Impl.Constants, s:Impl.Variables, s':Impl.Variables, diskStep:TreeDisk.Step, step:Impl.Step)
    ensures step.QueryActionStep? ==> Impl.QueryAction(k, s, s', diskStep, step.lookup, step.key, step.value)
    ensures step.InsertActionStep? ==> Impl.InsertAction(k, s, s', diskStep, step.edit, step.key, step.oldValue, step.newValue)
    ensures step.DeleteActionStep? ==> Impl.DeleteAction(k, s, s', diskStep, step.edit, step.key, step.deletedValue)
    ensures step.ExpandActionStep? ==> Impl.ExpandAction(k, s, s', diskStep, step.j)
    ensures step.ContractActionStep? ==> Impl.ContractAction(k, s, s', diskStep, step.j)
    ensures step.WriteBackActionStep? ==> Impl.WriteBackAction(k, s, s', diskStep, step.lba)
    ensures step.EmitTableActionStep?
                ==> Impl.EmitTableAction(k, s, s', diskStep, step.persistentTi, step.super, step.tblSectorIdx)
    ensures step.CommitActionStep? ==> Impl.CommitAction(k, s, s', diskStep, step.persistentTi, step.super)
    ensures step.CrashActionStep? ==> Impl.CrashAction(k, s, s', diskStep)
    ensures step.RecoverActionStep? ==> Impl.RecoverAction(k, s, s', diskStep, step.super, step.persistentTl)
    ensures step.CacheFaultActionStep? ==> Impl.CacheFaultAction(k, s, s', diskStep, step.lba, step.sector)
    ensures step.CacheEvictActionStep? ==> Impl.CacheEvictAction(k, s, s', diskStep, step.lba)
{}

// TODO I'm doing a lot of tedious fully qualified naming to preserve my
// ability to give every module a Constants, Variables, Init and Next. Consider
// a hackaround to enable import opened.

// ApplyEdit only affects lookups that touch the edited node.
lemma EditStability(k:Constants, s:Variables, s':Variables, step:Step, edit:Impl.NodeEdit, key:Key, oldValue:Option<Value>)
    requires Impl.ApplyEdit(k.impl, s.impl, s'.impl, step.disk, edit, key, oldValue)
    //requires NextStep(k, s, s', step)
    requires SysInv(k, s)
    //ensures WFDiskState(k, s');
    ensures forall nba, node :: nba != edit.replacementNba ==>
        Impl.NbaResolvesToNode(k.impl, LV(k, s).table, LV(k, s).view, nba, node)
        <==> Impl.NbaResolvesToNode(k.impl, LV(k, s').table, LV(k, s').view, nba, node);
{
}

lemma ValidLookupNests(lv:LookupView, lookup:Impl.Lookup, prefix:Impl.Lookup)
    requires ValidLookupInLV(lv, lookup)
    requires prefix == Impl.Lookup(lookup.layers[..|lookup.layers|-1]);
    ensures |prefix.layers|>0 ==> ValidLookupInLV(lv, prefix)
{
    if |prefix.layers|>0 {
        forall i | 0<=i<|lookup.layers|-1
            ensures Impl.ValidLayerIndex(prefix, i)
            ensures Impl.WFNode(prefix.layers[i].node)
        {
            assert Impl.ValidLayerIndex(lookup, i);
            assert Impl.ValidLayerIndex(prefix, i);
            var layer := lookup.layers[i];
            var player := prefix.layers[i];
            assert Impl.LayerHasValidSlotIndex(layer);
            assert Impl.LayerHasValidSlotIndex(player);
            assert Impl.ValidAddress(lv.k, player.addr);
        }
        forall i | 0<=i<|lookup.layers|-1
            ensures Impl.ValidLayerIndex(prefix, i)
            ensures Impl.WFNode(prefix.layers[i].node)
         {
            assert Impl.LookupHonorsPointerLinksAtLayer(lookup, i);
            assert Impl.LookupHonorsPointerLinksAtLayer(prefix, i);
            assert Impl.LookupHonorsRangesAt(prefix, i);
        }
        assert Impl.ValidLookupInView(lv.k, lv.table, lv.view, prefix);
    }
}

function LookupPrefix(lv:LookupView, lookup:Impl.Lookup) : (prefix:Impl.Lookup)
    requires ValidLookupInLV(lv, lookup)
    ensures |prefix.layers|>0 ==> ValidLookupInLV(lv, prefix)
{
    var prefix := Impl.Lookup(lookup.layers[..|lookup.layers|-1]);
    ValidLookupNests(lv, lookup, prefix);
    prefix
}

function TranslateLookupAcrossEdit(k:Constants, s:Variables, s':Variables, step:Step, lookup':Impl.Lookup) : (lookup:Impl.Lookup)
    requires NextStep(k, s, s', step)
    requires SysInv(k, s)
    requires ValidLookupInLV(LV(k, s'), lookup')
    // more requireses that you're not looking up something that just got Insert-ed.
    ensures ValidLookupInLV(LV(k, s), lookup)
    decreases |lookup'.layers|
{
    var last' := Last(lookup'.layers);
    assert Impl.ValidLayerIndex(lookup', |lookup'.layers|-1);
    var nba' := Impl.TableAt(k.impl, LV(k, s').table, last'.addr);

    var prefix' := LookupPrefix(LV(k, s'), lookup');
    var prefix :=
        if |prefix'.layers|==0
        then []
        else TranslateLookupAcrossEdit(k, s, s', step, prefix').layers;

    if (step.impl.InsertActionStep? || step.impl.DeleteActionStep?)
        && step.impl.edit.replacementNba == nba' then
        step.impl.edit.lookup
    else if step.impl.ExpandActionStep?
        && step.impl.j.edit.replacementNba == nba' then
        Impl.Lookup(prefix)
    else if step.impl.ContractActionStep?
        && step.impl.j.edit.replacementNba == nba' then
        step.impl.j.edit.lookup
    else
        Impl.Lookup(prefix + [Last(lookup'.layers)])
}

lemma PivotsOrderedInvInduction(k:Constants, s:Variables, s':Variables, step:Step)
    requires NextStep(k, s, s', step)
    requires SysInv(k, s)
    ensures WFDiskState(k, s');
    ensures PivotsOrderedInv(LV(k, s'));
{
    CautiouslyRevealNextStep(k.impl, s.impl, s'.impl, step.disk, step.impl);
    match step.impl {
        case QueryActionStep(lookup, key, value) => {
            assert LV(k, s') == LV(k, s);
            assert PivotsOrderedInv(LV(k, s'));
        }
        case InsertActionStep(edit, key, oldValue, newValue) => {
            var lv := LV(k, s);
            var lv' := LV(k, s');
            forall lookup, i |
                && ValidLookupInLV(lv', lookup)
                && Impl.ValidLayerIndex(lookup, i)
            ensures PivotsOrdered(lookup.layers[i].node)
            {
                var tableAddr := Impl.EditLast(step.impl.edit).addr;
                var layer := lookup.layers[i];
                var addr := layer.addr;
                var nba := Impl.TableAt(k.impl, lv'.table, layer.addr);
                var node := layer.node;
                if (nba == step.impl.edit.replacementNba) {
                    assert PivotsOrdered(lookup.layers[i].node);
                } else {
                    EditStability(k, s, s', step, step.impl.edit, step.impl.key, step.impl.oldValue);
                    //assert Impl.LookupMatchesViewAtLayer(k.impl, lv'.table, lv'.view, lookup, i);
                    assert Impl.NbaResolvesToNode(k.impl, lv'.table, lv'.view, nba, node);
                    assert Impl.NbaResolvesToNode(k.impl, lv.table, lv.view, nba, node);

                    // This is going to require demonstrating that all the rest of the nodes
                    // (and table translations) in the lookup didn't change, AND that the
                    // node and table translation we just edited are at the bottom of the lookup.
                    // (And THAT strategy will die when we move on to janitorial edits... we
                    // might want to think those through first, since the simpler edits will
                    // likely be a special case of them.)
                    assert ValidLookupInLV(lv, lookup);
                    assert Impl.ValidLayerIndex(lookup, i);

                    assert PivotsOrdered(lookup.layers[i].node);
                }
            }
            assert PivotsOrderedInv(LV(k, s'));
        }
        case DeleteActionStep(edit, key, oldValue) => {
            assume false;
            assert PivotsOrderedInv(LV(k, s'));
        }
        case ExpandActionStep(j) => {
            assume false;
            assert PivotsOrderedInv(LV(k, s'));
        }
        case ContractActionStep(j) => {
            assume false;
            assert PivotsOrderedInv(LV(k, s'));
        }
        case WriteBackActionStep(lba) => {
            assert ViewThroughCache(k.impl, s.impl, DiskView(k, s)) == ViewThroughCache(k.impl, s'.impl, DiskView(k, s'));
            assert LV(k, s') == LV(k, s);
            assert PivotsOrderedInv(LV(k, s'));
        }
        case EmitTableActionStep(persistentTi, super, tblSectorIdx) => {
            // This proof will hinge on the fact that, when we wrote into the cache, we didn't touch sectors
            // that store node (and hence pivot) information.
            assume false;
            assert LV(k, s') == LV(k, s);
            assert PivotsOrderedInv(LV(k, s'));
        }
        case CommitActionStep(persistentTi, super) => {
            assume false;
            assert PivotsOrderedInv(LV(k, s'));
        }
        case CrashActionStep => {
            assume false;   // gonna need an invariant here: PivotsOrdered holds on persistent table.
            assert PivotsOrderedInv(LV(k, s'));
        }
        case RecoverActionStep(super, persistentTl) => {
            assume false;   // gonna need an invariant here: PivotsOrdered holds on persistent table.
            assert PivotsOrderedInv(LV(k, s'));
        }
        case CacheFaultActionStep(lba, sector) => {
            var vtc := ViewThroughCache(k.impl, s.impl, DiskView(k, s));
            var vtc' := ViewThroughCache(k.impl, s'.impl, DiskView(k, s'));
            assert vtc == vtc'; // instantiate. (XXX James: Weird!)
            assert LV(k, s') == LV(k, s);
            assert PivotsOrderedInv(LV(k, s'));
        }
        case CacheEvictActionStep(lba) => {
            assert ViewThroughCache(k.impl, s.impl, DiskView(k, s)) == ViewThroughCache(k.impl, s'.impl, DiskView(k, s'));
            assert LV(k, s') == LV(k, s);
            assert PivotsOrderedInv(LV(k, s'));
        }
    }
}

lemma PivotsHonorRangesInvInduction(k:Constants, s:Variables, s':Variables, step:Step)
    requires NextStep(k, s, s', step)
    requires SysInv(k, s)
    ensures WFDiskState(k, s');
    ensures PivotsHonorRangesInv(LookupView(k.impl, s'.impl.ephemeralTable, ViewThroughCache(k.impl, s'.impl, DiskView(k, s'))))
{
}

lemma DatumsAreInTheRightPlaceInvInduction(k:Constants, s:Variables, s':Variables, step:Step)
    requires NextStep(k, s, s', step)
    requires SysInv(k, s)
    ensures WFDiskState(k, s');
    ensures DatumsAreInTheRightPlaceInv(LookupView(k.impl, s'.impl.ephemeralTable, ViewThroughCache(k.impl, s'.impl, DiskView(k, s'))))
{
}

lemma OneDatumPerKeyInvInduction(k:Constants, s:Variables, s':Variables, step:Step)
    requires NextStep(k, s, s', step)
    requires SysInv(k, s)
    // caller dispatches these invs before getting here
    requires PivotsOrderedInv(LV(k, s'));
    requires PivotsHonorRangesInv(LV(k, s'));
    requires DatumsAreInTheRightPlaceInv(LV(k, s'));
    ensures WFDiskState(k, s');
    ensures OneDatumPerKeyInv(LV(k, s'))
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
                // Hey, these are the same lookups! So they end at the same datum.
                ExploitLookupsAgree(lookup1, lookup2, commonPrefixLength, commonPrefixLength-1);
                assert DatumsUniqueInView(lv, datum1, datum2);
            } else if (commonPrefixLength == |lookup1.layers|) {
                LookupsAtDifferentDepthsContradiction(k, s, s', step, lv, datum1, datum2, lookup1, lookup2, commonPrefixLength);
            } else if (commonPrefixLength == |lookup2.layers|) {
                IsGreatestCommonPrefixSymmetry(lookup1, lookup2, commonPrefixLength);
                LookupsAtDifferentDepthsContradiction(k, s, s', step, lv, datum2, datum1, lookup2, lookup1, commonPrefixLength);
            } else {
                // at the first divergent layer, the addr & node agree because the previous layer pointed at it.
                if (commonPrefixLength > 0) {
                    ExploitLookupsAgree(lookup1, lookup2, commonPrefixLength, commonPrefixLength-1);
                }
                DivergentLayerAgreesOnAddrAndNodes(lv, lookup1, lookup2, commonPrefixLength);

                // The slots must disagree (by contradiction)
                if (lookup1.layers[commonPrefixLength].slot == lookup2.layers[commonPrefixLength].slot) {
                    // These triggers enable the proof that the slotRanges are equal.
                    assert Impl.ValidLayerIndex(lookup1, commonPrefixLength);  // OBSERVE trigger
                    assert Impl.ValidLayerIndex(lookup2, commonPrefixLength);  // OBSERVE trigger
                    assert false;
                }
                // assert lookup1.layers[commonPrefixLength].slot != lookup2.layers[commonPrefixLength].slot;

                // and hence the ranges don't overlap.
                var range1 := lookup1.layers[commonPrefixLength].slotRange;
                var range2 := lookup2.layers[commonPrefixLength].slotRange;
                assert Impl.SlotSatisfiesQuery(Impl.TerminalSlot(lookup1), datum1.key, Some(datum1.value));   // Trigger DatumsAreInTheRightPlaceInv
                assert Impl.SlotSatisfiesQuery(Impl.TerminalSlot(lookup2), datum2.key, Some(datum2.value));   // Trigger DatumsAreInTheRightPlaceInv
                // Pull that non-overlapping observation down to the bottom of the lookup stacks
                LookupRangesNest(lv, lookup1, commonPrefixLength, |lookup1.layers|-1, datum1.key);
                LookupRangesNest(lv, lookup2, commonPrefixLength, |lookup2.layers|-1, datum2.key);
                // If the ranges don't overlap, the keys aren't equal, which contradicts the assumption
                // in the if above.
                DisjointRanges(lv, lookup1, lookup2, commonPrefixLength, datum1, datum2);
                assert false;
            }
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
    PivotsOrderedInvInduction(k, s, s', step);
    PivotsHonorRangesInvInduction(k, s, s', step);
    DatumsAreInTheRightPlaceInvInduction(k, s, s', step);
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
