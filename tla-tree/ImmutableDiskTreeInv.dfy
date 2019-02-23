include "ImmutableDiskTree.dfy"

module ImmutableDiskTreeInv {
import opened TreeTypes
import opened ImmutableDiskTreeImpl

predicate SuperblockTypeCorrect(k:Constants, view:View)
    requires PlausibleDiskSize(k)
    requires FullView(k, view)
{
    && view[0].Superblock?
}

function PersistentTableIndex(k:Constants, view:View) : TableIndex
    requires PlausibleDiskSize(k)
    requires FullView(k, view)
    requires SuperblockTypeCorrect(k, view)
{
    view[0].liveTable
}

predicate TableBlocksTypeCorrect(k:Constants, view:View)
    requires PlausibleDiskSize(k)
    requires FullView(k, view)
{
    && SuperblockTypeCorrect(k, view)
    && WFTableIndex(PersistentTableIndex(k, view))
    && forall sectorIdx :: ValidTableSectorIndex(k, sectorIdx) ==>
        view[TableBegin(k, PersistentTableIndex(k, view)) + sectorIdx].TableSector?
}

function PersistentTable(k:Constants, view:View) : Table
    requires PlausibleDiskSize(k)
    requires FullView(k, view)
    requires TableBlocksTypeCorrect(k, view)
{
    var super := view[SUPERBLOCK_LBA()];
    var ti := PersistentTableIndex(k, view);
    var sectors := SubsequenceFromFullView(k, view, TableBegin(k, ti), k.tableSectors);
    UnmarshallTable(k, sectors)
}

function {:opaque} AllocatedAddresses(k:Constants, table:Table) : (alloced:set<TableAddress>)
    requires WFTable(k, table)
    ensures forall addr :: addr in alloced <==> addr in ValidAddresses(k) && TableAt(k, table, addr).Used?
{
    set addr | addr in ValidAddresses(k) && TableAt(k, table, addr).Used?
}

predicate AllocatedNbasValid(k:Constants, table:Table)
    requires WFTable(k, table)
{
    forall addr :: addr in AllocatedAddresses(k, table) ==> ValidNba(k, TableAt(k, table, addr))
}

predicate AllocatedNodeBlocksTypeCorrect(k:Constants, view:View, table:Table)
    requires PlausibleDiskSize(k)
    requires FullView(k, view)
    requires TableBlocksTypeCorrect(k, view)
    requires WFTable(k, table)
    requires AllocatedNbasValid(k, table)
{
    forall addr :: addr in AllocatedAddresses(k, table) ==> view[LbaForNba(k, TableAt(k, table, addr))].NodeSector?
}

predicate PersistentAllocatedNodesTypeCorrect(k:Constants, view:View)
    requires PlausibleDiskSize(k)
    requires FullView(k, view)
    requires TableBlocksTypeCorrect(k, view)
    requires AllocatedNbasValid(k, PersistentTable(k, view))
{
    AllocatedNodeBlocksTypeCorrect(k, view, PersistentTable(k, view))
}

} // module
