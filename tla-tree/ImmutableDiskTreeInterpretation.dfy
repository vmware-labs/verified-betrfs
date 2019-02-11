include "ImmutableDiskTreeHeight.dfy"
include "CrashableMap.dfy"

module ImmutableDiskTreeInterpretation {
import opened TreeTypes
import opened ImmutableDiskTree
import opened ImmutableDiskTreeInv
import opened ImmutableDiskTreeHeight
import opened MissingLibrary
import CrashableMap


function PersistentGraph(k:Constants, s:Variables) : (gv:GraphView)
    requires PersistentGraphSane(k, s)
    ensures SaneTableInView(gv)
{
    var view := ViewOfDisk(k.disk, s.disk);
    var table := PersistentTable(k, view);
    GraphView(k, table, view)
}

function EphemeralGraph(k:Constants, s:Variables) : GraphView
    requires TreeDisk.WF(k.disk, s.disk)
{
    var table := s.ephemeralTable;
    var view := ViewThroughCache(k, s);
    GraphView(k, table, view)
}

predicate TreeShapedGraph(gv:GraphView)
{
    && SaneTableInView(gv)
    && CycleFree(gv, GraphAddrHeightMap(gv))
}

predicate TreeInv(k:Constants, s:Variables)
{
    && PersistentGraphSane(k, s)
    && TreeShapedGraph(PersistentGraph(k, s))
    && SaneNodeInView(PersistentGraph(k, s),  ROOT_ADDR())

    && TreeDisk.WF(k.disk, s.disk)
    && TreeShapedGraph(EphemeralGraph(k, s))
    && SaneNodeInView(EphemeralGraph(k, s),  ROOT_ADDR())
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
        case Empty => CrashableMap.EmptyMap()
        case Value(datum) => SingletonImap(datum.key, datum.value)
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
    then CrashableMap.EmptyMap()
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

function ITreeView(tv:TreeView) : CrashableMap.View
    requires WFTreeView(tv)
    requires SaneNodeInTreeView(tv, ROOT_ADDR())
{
    ISubtreeView(tv, ROOT_ADDR())
}

function EphemeralTreeView(k:Constants, s:Variables) : (tv:TreeView)
    requires TreeDisk.WF(k.disk, s.disk)
    requires TreeShapedGraph(EphemeralGraph(k, s))   // TODO belongs in Inv
    ensures WFTreeView(tv)
{
    TreeView(EphemeralGraph(k, s))
}

predicate PersistentGraphSane(k:Constants, s:Variables) // TODO belongs in Inv
{
    && TreeDisk.WF(k.disk, s.disk)
    && PlausibleDiskSize(k)
    && var view := ViewOfDisk(k.disk, s.disk);
    && TableBlocksTypeCorrect(k, view)
    && var table := PersistentTable(k, view);
    && WFTable(k, table)
    && AllocatedNbasValid(k, table)
    && FullView(k, view)
    && AllocatedNodeBlocksTypeCorrect(k, view, table)
}

function PersistentTreeView(k:Constants, s:Variables) : (tv:TreeView)
    requires PersistentGraphSane(k, s)
    requires TreeShapedGraph(PersistentGraph(k, s))   // TODO belongs in Inv
    ensures WFTreeView(tv)
{
    TreeView(PersistentGraph(k, s))
}

function IEphemeralView(k:Constants, s:Variables) : CrashableMap.View
    requires TreeDisk.WF(k.disk, s.disk)
    requires TreeShapedGraph(EphemeralGraph(k, s))   // TODO belongs in Inv
    requires SaneNodeInView(EphemeralGraph(k, s),  ROOT_ADDR()) // TODO Inv
{
    ITreeView(EphemeralTreeView(k, s))
}

function IPersistentView(k:Constants, s:Variables) : CrashableMap.View
    requires PersistentGraphSane(k, s)
    requires TreeShapedGraph(PersistentGraph(k, s))   // TODO belongs in Inv
    requires SaneNodeInView(PersistentGraph(k, s),  ROOT_ADDR()) // TODO Inv
{
    ITreeView(PersistentTreeView(k, s))
}

function IViews(k:Constants, s:Variables) : seq<CrashableMap.View>
    requires TreeInv(k, s)
{
    if s.ready
    then [IEphemeralView(k, s), IPersistentView(k, s)]
    else [IPersistentView(k, s)]
}

function I(k:Constants, s:Variables) : CrashableMap.Variables
    requires TreeInv(k, s)
{
    CrashableMap.Variables(IViews(k, s))
}

} // module
