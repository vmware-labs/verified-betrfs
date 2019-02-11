include "ImmutableDiskTreeInv.dfy"

module ImmutableDiskTreeHeight {
import opened TreeTypes
import opened ImmutableDiskTree
import opened ImmutableDiskTreeInv
import opened MissingLibrary

// A view of a thing we expect to be a tree -- but at this point we're still proving it.
// So it's just a "graph" for now.
datatype GraphView = GraphView(k:Constants, table:Table, view:View)

predicate SaneTableInView(gv:GraphView)
{
    && PlausibleDiskSize(gv.k)
    && WFTable(gv.k, gv.table)
    && AllocatedNbasValid(gv.k, gv.table)
    && FullView(gv.k, gv.view)
    && TableBlocksTypeCorrect(gv.k, gv.view)
    && AllocatedNodeBlocksTypeCorrect(gv.k, gv.view, gv.table)
}

predicate SaneNodeInView(gv:GraphView, addr:TableAddress)
{
    && SaneTableInView(gv)
    && addr in AllocatedAddresses(gv.k, gv.table)
}

function NodeAt(gv:GraphView, addr:TableAddress) : Node
    requires SaneNodeInView(gv, addr)
{
    var nba := TableAt(gv.k, gv.table, addr);
    var lba := LbaForNba(gv.k, nba);
    var sector := gv.view[lba];
    sector.node
}

type Height = Option<int>
type AddrHeightMap = map<TableAddress,int>   // Maps from addresses to height of the tree at that address. Zero is an Unused addr.

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
    requires slotCount <= |node.slots|
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
    requires 0<=slotCount<=|node.slots|
    ensures h.Some? ==> AllSlotHeightsAtMost(node, heightMap, slotCount, h.value)
    ensures h.Some? ==> 0<=h.value
    ensures h.Some? ==> forall slotIdx
        :: ValidSlotIndex(node, slotIdx) && slotIdx < slotCount && node.slots[slotIdx].Pointer?
        ==> node.slots[slotIdx].addr in heightMap
{
    if slotCount==0
    then Some(1)
    else
        CombineHeights(
            DefineHeightNonLeafPrefix(node, heightMap, slotCount-1),
            HeightForSlot(node.slots[slotCount-1], heightMap))
}

function DefineHeightAddr(gv:GraphView, heightMap:AddrHeightMap, addr:TableAddress) : (h:Height)
    requires SaneNodeInView(gv, addr)
    ensures h.Some? ==> 0<=h.value
{
    if TableAt(gv.k, gv.table, addr).Unused?
    then Some(0)
    else
        var node := NodeAt(gv, addr);
        DefineHeightNonLeafPrefix(node, heightMap, |node.slots|)

}

predicate WFHeightMap(heightMap:AddrHeightMap)
{
    forall addr :: addr in heightMap ==> 0 <= heightMap[addr]
}

predicate HeightMapNests(gv:GraphView, heightMap:AddrHeightMap)
    requires SaneTableInView(gv)
{
    forall addr, idx :: (
            && addr in AllocatedAddresses(gv.k, gv.table)
            && addr in heightMap
            && ValidSlotIndex(NodeAt(gv, addr), idx)
            && NodeAt(gv, addr).slots[idx].Pointer?
        ) ==> NodeAt(gv, addr).slots[idx].addr in heightMap
}

predicate HeightMapDecreases(gv:GraphView, heightMap:AddrHeightMap)
    requires SaneTableInView(gv)
    requires HeightMapNests(gv, heightMap)
{
    forall addr, idx :: (
            && addr in AllocatedAddresses(gv.k, gv.table)
            && addr in heightMap
            && ValidSlotIndex(NodeAt(gv, addr), idx)
            && NodeAt(gv, addr).slots[idx].Pointer?
        ) ==> heightMap[NodeAt(gv, addr).slots[idx].addr] < heightMap[addr]
}

function {:opaque} SlotHeightMapDef(gv:GraphView, maxHeight:int) : (heightMap:AddrHeightMap)
    requires 0<=maxHeight
    requires SaneTableInView(gv)
    ensures WFHeightMap(heightMap)
{
    if maxHeight == 0
    then
        map addr | addr in ValidAddresses(gv.k) && TableAt(gv.k, gv.table, addr).Unused? :: 0
    else
        map addr | 
            && addr in AllocatedAddresses(gv.k, gv.table)
            && DefineHeightAddr(gv, SlotHeightMapDef(gv, maxHeight-1), addr).Some?
            :: DefineHeightAddr(gv, SlotHeightMapDef(gv, maxHeight-1), addr).value
}

lemma
    DefineHeightAddr(gv, SlotHeightMapDef(gv, maxHeight-1), addr).Some?
    ==> DefineHeightAddr(gv, SlotHeightMapDef(gv, maxHeight), addr).Some?

Okay, brain.
At maxheight 0, there's some stuff in the table (unused addrs).
At maxheight 1, all those things are in the table (DefineHeightAddr defn), plus things defined by
DefineHeightNonLeafPrefix.
At maxheight 2, some new things are in the table, but everything that was in the table before is still
in there for the same reason it was before.

lemma HeightMapMonotonic(gv:GraphView, maxHeight:int)
    requires SaneTableInView(gv)
    requires 0 < maxHeight
    ensures SlotHeightMapDef(gv, maxHeight-1).Keys <= SlotHeightMapDef(gv, maxHeight).Keys
{
    reveal_SlotHeightMapDef();
    var lo := SlotHeightMapDef(gv, maxHeight-1);
    var hi := SlotHeightMapDef(gv, maxHeight);
    forall addr | addr in lo
        ensures addr in hi
    {
        if (maxHeight == 1) {
            assert addr in ValidAddresses(gv.k);
            assert TableAt(gv.k, gv.table, addr).Unused?;
            assert addr in hi;
        } else {
            assert addr in AllocatedAddresses(gv.k, gv.table)
           assert DefineHeightAddr(gv, SlotHeightMapDef(gv, maxHeight-2), addr).Some?
            HeightMapMonotonic(gv, lo-1, addr);
            assert addr in hi;
        }
    }
}

lemma SlotHeightMapDefProperties(gv:GraphView, maxHeight:int, heightMap:AddrHeightMap)
    requires 0<=maxHeight
    requires SaneTableInView(gv)
    requires SlotHeightMapDef(gv, maxHeight) == heightMap
    ensures HeightMapNests(gv, heightMap)
    ensures HeightMapDecreases(gv, heightMap)
{
    reveal_SlotHeightMapDef();
    forall addr, idx | (
            && addr in AllocatedAddresses(gv.k, gv.table)
            && addr in heightMap
            && ValidSlotIndex(NodeAt(gv, addr), idx)
            && NodeAt(gv, addr).slots[idx].Pointer?
        ) 
        ensures NodeAt(gv, addr).slots[idx].addr in heightMap
    {
        assert addr in heightMap;
        var node := NodeAt(gv, addr);
        if (maxHeight == 0) {
            assert node.slots[idx].addr in heightMap;
        } else {
            var subhm := SlotHeightMapDef(gv, maxHeight-1);
            var dha := DefineHeightAddr(gv, subhm, addr);
            assert dha.Some?;

            assert dha == if TableAt(gv.k, gv.table, addr).Unused?
                then Some(0)
                else
                    var node := NodeAt(gv, addr);
                    DefineHeightNonLeafPrefix(node, subhm, |node.slots|);

            if TableAt(gv.k, gv.table, addr).Unused? {
                assert node.slots[idx].addr in heightMap;
            } else {
                assert dha == DefineHeightNonLeafPrefix(node, subhm, |node.slots|);
                reveal_DefineHeightNonLeafPrefix();
                assert dha == CombineHeights(
                    DefineHeightNonLeafPrefix(node, subhm, |node.slots|-1),
                    HeightForSlot(node.slots[|node.slots|-1], subhm));
                assert node.slots[idx].addr in subhm;
                var subaddr := node.slots[idx].addr;
                SlotHeightMapDefProperties(gv, maxHeight-1, subhm);

                assert subaddr in AllocatedAddresses(gv.k, gv.table);
                assert subaddr in heightMap;
                assert ValidSlotIndex(NodeAt(gv, subaddr), idx);
                assert NodeAt(gv, subaddr).slots[idx].Pointer?;

                assert node.slots[idx].addr in heightMap;
            }
        }
    }
    assert HeightMapDecreases(gv, heightMap);
}

function SlotHeightMap(gv:GraphView) : AddrHeightMap
    requires SaneTableInView(gv)
{
    SlotHeightMapDefProperties(gv, gv.k.tableEntries, SlotHeightMapDef(gv, gv.k.tableEntries));
    SlotHeightMapDef(gv, gv.k.tableEntries)
}

predicate HeightMapComplete(k:Constants, heightMap:AddrHeightMap)
{
    heightMap.Keys == ValidAddresses(k)
}

// If there are no cycles, then every address can be assigned a height.
predicate CycleFree(gv:GraphView, heightMap:AddrHeightMap)
{
    && WFHeightMap(heightMap)
    && SaneTableInView(gv)
    && HeightMapNests(gv, heightMap)
    && HeightMapDecreases(gv, heightMap)
    && HeightMapComplete(gv.k, heightMap)
}

} // module
