include "ImmutableDiskTreeInv.dfy"
include "CrashableMap.dfy"

module RefinementProof {
import opened KVTypes
import opened ImmutableDiskTree
import opened ImmutableDiskTreeInv
import opened MissingLibrary
import CrashableMap

function NodeAt(k:Constants, table:Table, view:View, addr:int) : Node
    requires PlausibleDiskSize(k)
    requires WFTable(k, table)
    requires AllocatedNbasValid(k, table)
    requires addr in AllocatedAddresses(k, table)
    requires FullView(k, view)
{
    var nba := table[addr];
    var lba := LbaForNba(k, nba);
    var sector := view[lba];
    sector.node
}

type Height = Option<int>
type AddrHeightMap = map<int,int>   // Maps from addresses to height of the tree at that address. Zero is an Unused addr.

predicate LeafNode(node:Node)
{
    forall idx :: ValidSlotIndex(node, idx) ==> !node.slots[idx].Pointer?
}

function HeightForSlot(slot:Slot, heightMap:AddrHeightMap) : (h:Height)
{
    match slot {
        case Empty => Some(1)
        case Value(datum) => Some(1)
        case Pointer(idx) => if idx in heightMap then Some(heightMap[idx]) else None
    }
}

predicate HeightAtMost(height:Height, bound:int)
{
    height.Some? && height.value <= bound
}

predicate AllSlotHeightsAtMost(node:Node, heightMap:AddrHeightMap, slotCount:int, bound:int)
{
    forall i :: 0<=i<slotCount ==> HeightAtMost(HeightForSlot(node.slots[i], heightMap), bound)
}

function CombineHeights(h1:Height, h2:Height) : Height
{
    if h1.Some? && h2.Some?
    then Some(max(h1.value, h2.value))
    else None
}

function {:opaque} DefineHeightNonLeafPrefix(node:Node, heightMap:AddrHeightMap, slotCount:int) : (h:Height)
    ensures h.Some? ==> AllSlotHeightsAtMost(node, heightMap, slotCount, h.value)
{
    if slotCount==0
    then Some(1)
    else
        CombineHeights(
            DefineHeightNonLeafPrefix(node, heightMap, slotCount-1),
            HeightForSlot(node.slots[slotCount-1], heightMap))
}

function DefineHeightAddr(k:Constants, table:Table, view:View, heightMap:AddrHeightMap, addr:int) : (h:Height)
    ensures h.Some? ==> 0<=h.value
{
    if table[addr].Unused?
    then Some(0)
    else
        var node := NodeAt(k, table, view, addr);
        DefineHeightNonLeafPrefix(node, heightMap, |node.slots|)

}

function {:opaque} SlotHeightMapDef(k:Constants, table:Table, view:View, maxHeight:int) : AddrHeightMap
{
    if maxHeight == 0
    then
        map addr | addr in ValidAddresses(k) && table[addr].Used? :: 0
    else
        map addr | 
            addr in ValidAddresses(k)
            && DefineHeightAddr(k, table, view, SlotHeightMapDef(k, table, view, maxHeight-1), addr).Some?
            :: DefineHeightAddr(k, table, view, SlotHeightMapDef(k, table, view, maxHeight-1), addr).value
}

function SlotHeightMap(k:Constants, table:Table, view:View) : AddrHeightMap
{
    SlotHeightMapDef(k, table, view, k.tableEntries)
}

// If there are no cycles, then every address can be assigned a height.
predicate CycleFree(k:Constants, heightMap:AddrHeightMap)
{
    heightMap.Keys == ValidAddresses(k)
}


//// left off here
/*

// The datums at or below slot slotNum of the tree at table[addr].
function {:opaque} ISlotView(k:Constants, table:Table, view:View, addr:int, slotNum:int) : CrashableMap.View
{
    var node := NodeAt(k, table, view, addr);
    var slot := node[slotNum];
    match slot {
        case Empty => CrashableMap.EmptyMap()
        case Value(datum) => SingletonMap(datum.key, datum.value)
        case Pointer(idx) => ITreeView(k, table, view, idx, 
    if slot.Empty
    then 
    els
}

// The datums in the first slotCount slots of the tree at table[addr].
function {:opaque} ISubtreePrefixView(k:Constants, table:Table, view:View, addr:int, slotCount:int) : CrashableMap.View
{
    if slotCount==0
    then CrashableMap.EmptyMap()
    else JoinMap(ISubtreeView(k, table, view, addr, slotCount - 1), ISlotView(k, table, view, addr, slotCount - 1))
}

function ISubtreeView(k:Constants, table:Table, view:View, addr:int) : CrashableMap.View
{
    var slotCount := |NodeAt(k, table, view, addr).slots|;
    ISubtreePrefixView(k, table, view, addr, slotCount)
}

function ITreeView(k:Constants, table:Table, view:View) : CrashableMap.View
{
    ISubtreePrefixView(k, table, view, ROOT_ADDR())
}

function IEphemeralView(k:Constants, s:Variables) : CrashableMap.View
{
    ITreeView(k, s.ephemeralTable, ViewOfCache(s.cache))
}

function PersistentTable(k:Constants, s:Variables) : Table
    requires ValidDiskSize(k, s)
    requires TableBlocksTypeCorrect(k, s)
{
    var super := s.disk.sectors[SUPERBLOCK_LBA()];
    var ti := super.liveTable;
    var sectors := s.disk.sectors[TableBegin(k, ti) .. TableBegin(k, ti) + k.tableSectors];
    UnmarshallTable(k, sectors)
}

function IPersistentView(k:Constants, s:Variables) : CrashableMap.View
    requires ValidDiskSize(k, s)
    requires TableBlocksTypeCorrect(k, s)
    requires AllocatedNbasValid(k, PersistentTable(k, s))
    requires PersistentAllocatedNodesTypeCorrect(k, s)
{
    ITreeView(k, PersistentTable(k, s), ViewOfDisk(s.disk))
}

function IViews(k:Constants, s:Variables) : seq<CrashableMap.View>
    requires Inv(k, s)
{
    if s.ready?
    then [IEphemeralView(k, s), IPersistentView(k, s)]
    else [IPersistentView(k, s)]
}

function I(k:Constants, s:Variables) : CrashableMap.Variables
    requires Inv(k, s)
{
    CrashableMap.Variables(IViews(k, s))
}
*/

} // module
