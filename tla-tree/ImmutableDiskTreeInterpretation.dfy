include "ImmutableDiskTreeContent.dfy"
include "CrashableMap.dfy"

module ImmutableDiskTreeInterpretation {
import opened KVTypes
import opened TreeTypes
import opened ImmutableDiskTreeImpl
import opened ImmutableDiskTreeInv
import opened ImmutableDiskTreeHeight
import opened ImmutableDiskTreeContent
import opened MissingLibrary
import CrashableMap


predicate PersistentGraphSane(k:Constants, diskView:View) // TODO belongs in Inv
{
    && FullView(k, diskView)
    && PlausibleDiskSize(k)
    && TableBlocksTypeCorrect(k, diskView)
    && var table := PersistentTable(k, diskView);
    && WFTable(k, table)
    && AllocatedNbasValid(k, table)
    && AllocatedNodeBlocksTypeCorrect(k, diskView, table)
}

function PersistentGraph(k:Constants, diskView:View) : (gv:GraphView)
    requires PersistentGraphSane(k, diskView)
    ensures SaneTableInView(gv)
{
    var table := PersistentTable(k, diskView);
    GraphView(k, table, diskView)
}

function ViewLbaThroughCache(k:Constants, s:Variables, diskView:View, lba:LBA) : Sector
    requires FullView(k, diskView)
    requires 0 <= lba < DiskSize(k)
{
    if lba in s.cache then s.cache[lba].sector else diskView[lba]
}

function ViewThroughCache(k:Constants, s:Variables, diskView:View) : (cacheView:View)
    requires FullView(k, diskView)
    ensures FullView(k, cacheView)
    ensures forall lba :: (0 <= lba < DiskSize(k)) ==> cacheView[lba] == ViewLbaThroughCache(k, s, diskView, lba)
{
    map lba | lba in diskView :: ViewLbaThroughCache(k, s, diskView, lba)
}

function EphemeralGraph(k:Constants, s:Variables, diskView:View) : GraphView
    requires FullView(k, diskView)
{
    var table := s.ephemeralTable;
    var view := ViewThroughCache(k, s, diskView);
    GraphView(k, table, view)
}

//  XXX jon thinks this is dead
predicate TreeShapedGraph(gv:GraphView)
{
    && SaneTableInView(gv)
    && CycleFree(gv, GraphAddrHeightMap(gv))
}

//  XXX jon thinks this is dead
predicate TreeInv(k:Constants, s:Variables, diskView:View)
{
    && PersistentGraphSane(k, diskView)
    && TreeShapedGraph(PersistentGraph(k, diskView))
    && SaneNodeInView(PersistentGraph(k, diskView),  ROOT_ADDR())

    && FullView(k, diskView)
    && TreeShapedGraph(EphemeralGraph(k, s, diskView))
    && SaneNodeInView(EphemeralGraph(k, s, diskView),  ROOT_ADDR())
}

//////////////////////////////////////////////////////////////////////////////

datatype TreeView = TreeView(gv:GraphView)

predicate WFTreeView(tv:TreeView)
{
    && TreeShapedGraph(tv.gv)
}

predicate SaneNodeInTreeView(tv:TreeView, addr:TableAddress)
{
    && WFTreeView(tv)
    && SaneNodeInView(tv.gv, addr)
}

function TVNode(tv:TreeView, addr:TableAddress) : Node
    requires SaneNodeInTreeView(tv, addr)
{
    NodeAt(tv.gv, addr)
}

function HeightAt(tv:TreeView, addr:TableAddress) : int
    requires WFTreeView(tv)
    requires addr in AllocatedAddresses(tv.gv.k, tv.gv.table)
{
    GraphAddrHeightMap(tv.gv)[addr]
}

// The datums at or below slot slotIdx of the tree at table[addr].
function {:opaque} ISlotView(tv:TreeView, addr:TableAddress, slotIdx:int) : CrashableMap.View
    requires SaneNodeInTreeView(tv, addr)
    requires ValidSlotIndex(TVNode(tv, addr), slotIdx)
    decreases HeightAt(tv, addr), 0
{
    var slot := TVNode(tv, addr).slots[slotIdx];
    match slot {
        case Empty => EmptyImap()
        case Value(datum) => SingletonImap(datum.key, Some(datum.value))
        case Pointer(addr) => ISubtreeView(tv, addr)
    }
}

// The datums in the first slotCount slots of the tree at table[addr].
function {:opaque} ISubtreePrefixView(tv:TreeView, addr:TableAddress, slotCount:int) : CrashableMap.View
    requires SaneNodeInTreeView(tv, addr)
    requires 0 <= slotCount <= |TVNode(tv, addr).slots|
    requires SaneNodeInTreeView(tv, addr)
    decreases HeightAt(tv, addr), 1, slotCount
{
    if slotCount==0
    then EmptyImap<Key,Option<Value>>()
    else ImapUnionPreferB(      // We don't prefer B; the pieces had better be disjoint!
        ISubtreePrefixView(tv, addr, slotCount - 1),
        ISlotView(tv, addr, slotCount - 1))
}

function ISubtreeView(tv:TreeView, addr:TableAddress) : CrashableMap.View
    requires WFTreeView(tv)
    requires SaneNodeInTreeView(tv, addr)
    decreases HeightAt(tv, addr), 1
{
    var slotCount := |TVNode(tv, addr).slots|;
    ISubtreePrefixView(tv, addr, slotCount)
}

// The definitions above manipulate incomplete views; this definition fills in
// all the gaps in the keyspace to match the CrashableMap model.
// (TODO maybe CrashableMap should model missing keys explicitly?)
function {:opaque} CompletifyView(iv:CrashableMap.View) : (ov:CrashableMap.View)
    ensures CrashableMap.ViewComplete(ov)
    ensures forall k :: k in iv ==> ov[k] == iv[k]
    ensures forall k :: !(k in iv) ==> ov[k] == None
{
    imap k | true :: if k in iv then iv[k] else None
}

function ITreeView(tv:TreeView) : (iview:CrashableMap.View)
    requires WFTreeView(tv)
    requires SaneNodeInTreeView(tv, ROOT_ADDR())
    ensures CrashableMap.ViewComplete(iview)
{
    CompletifyView(ISubtreeView(tv, ROOT_ADDR()))
}

//////////////////////////////////////////////////////////////////////////////

function PersistentLookupView(k:Constants, diskView:View) : LookupView
    requires PlausibleDiskSize(k)
    requires FullView(k, diskView)
    requires TableBlocksTypeCorrect(k, diskView)
{
    LookupView(k, PersistentTable(k, diskView), diskView)
}

function EphemeralLookupView(k:Constants, s:Variables, diskView:View) : LookupView
    requires FullView(k, diskView)
{
    LookupView(k, s.ephemeralTable, ViewThroughCache(k, s, diskView))
}

function ILookupView(lv:LookupView) : (iview:CrashableMap.View)
    ensures CrashableMap.ViewComplete(iview)
{
    CompletifyView(ReachableValues(lv))
}

function IEphemeralView(k:Constants, s:Variables, diskView:View) : (iview:CrashableMap.View)
    requires FullView(k, diskView)
    requires TreeShapedGraph(EphemeralGraph(k, s, diskView))   // TODO belongs in Inv
    requires SaneNodeInView(EphemeralGraph(k, s, diskView),  ROOT_ADDR()) // TODO Inv
    ensures CrashableMap.ViewComplete(iview)
{
    ILookupView(EphemeralLookupView(k, s, diskView))
}

function IPersistentView(k:Constants, diskView:View) : (iview:CrashableMap.View)
    requires PersistentGraphSane(k, diskView)
    requires TreeShapedGraph(PersistentGraph(k, diskView))   // TODO belongs in Inv
    requires SaneNodeInView(PersistentGraph(k, diskView),  ROOT_ADDR()) // TODO Inv
    ensures CrashableMap.ViewComplete(iview)
{
    ILookupView(PersistentLookupView(k, diskView))
}

function IViews(k:Constants, s:Variables, diskView:View) : (iviews:seq<CrashableMap.View>)
    requires TreeInv(k, s, diskView)
    ensures CrashableMap.AllViewsComplete(iviews)
{
    if s.ready
    then [IEphemeralView(k, s, diskView), IPersistentView(k, diskView)]
    else [IPersistentView(k, diskView)]
}

function Ik(k:Constants) : CrashableMap.Constants
{
    CrashableMap.Constants()
}

function I(k:Constants, s:Variables, diskView:View) : CrashableMap.Variables
    requires TreeInv(k, s, diskView)
{
    CrashableMap.Variables(IViews(k, s, diskView))
}

} // module
