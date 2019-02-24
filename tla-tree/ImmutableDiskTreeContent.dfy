include "ImmutableDiskTreeHeight.dfy"

module ImmutableDiskTreeContent {
import opened KVTypes
import opened TreeTypes
import opened ImmutableDiskTreeImpl
import opened ImmutableDiskTreeHeight // TODO not sure we need any of Height ... until GC
import opened MissingLibrary

datatype LookupView = LookupView(k:Constants, table:Table, view:View)

predicate ValidValueLookup(lv:LookupView, lookup:Lookup)
{
    && ValidLookupInView(lv.k, lv.table, lv.view, lookup)
    && TerminalSlot(lookup).Value?
}

function {:opaque} AllValueLookups(lv:LookupView) : iset<Datum>
{
    iset lookup | ValidValueLookup(lv, lookup) :: TerminalSlot(lookup).datum
}

function {:opaque} AllKeys(lv:LookupView) : (keys:iset<Key>)
    ensures forall key :: key in keys ==> exists datum:Datum :: datum in AllValueLookups(lv) && datum.key == key
{
    iset datum | datum in AllValueLookups(lv) :: datum.key
}

function ValueFor(lv:LookupView, key:Key) : Value
    requires key in AllKeys(lv)
{
    var datum :| datum in AllValueLookups(lv) && datum.key == key;
    datum.value
}

function {:opaque} ReachableValues(lv:LookupView) : (m:imap<Key, Value>)
    ensures m.Keys == AllKeys(lv)
{
    imap key | key in AllKeys(lv) :: ValueFor(lv, key)
}

predicate ViewsNest(k:Constants, cacheView:View, throughView:View)
{
    && cacheView.Keys <= throughView.Keys
    && (forall key :: key in cacheView ==> cacheView[key] == throughView[key])
}

lemma ValidLookupInNestedView(k:Constants, table:Table, cacheView:View, diskView:View, lookup:Lookup)
    requires ViewsNest(k, cacheView, diskView)
    requires ValidLookupInView(k, table, cacheView, lookup)
    ensures ValidLookupInView(k, table, diskView, lookup)
{
}

predicate CacheLbasFitOnDisk(k:Constants, s:Variables)
{
    forall lba :: lba in s.cache ==> 0 <= lba < DiskSize(k)
}

predicate OneDatumPerKeyInv(lv:LookupView)
{
    forall datum1, datum2 :: datum1 in AllValueLookups(lv) && datum2 in AllValueLookups(lv) && datum1.key == datum2.key
        ==> datum1 == datum2
}

//XXX
//lemma UniqueKeysPredictsReachableValues(lv:LookupView, datum:Datum)
//    requires OneDatumPerKeyInv(lv)
//    requires datum in AllValueLookups(lv)
//    requires datum.key in AllKeys(lv)
//    ensures ReachableValues(lv)[datum.key] == datum.value
//{
//    reveal_ReachableValues();
//    var reachableValue := ReachableValues(lv)[datum.key];
//    assert reachableValue == ValueFor(lv, datum.key);
//    var reachableDatum := Datum(datum.key, reachableValue);
//    assert reachableDatum in AllValueLookups(lv);
//    assert reachableDatum == datum;
//}

} // module
