include "MissingLibrary.dfy"
include "KVTypes.dfy"
include "Disk.dfy"

module TreeTypes {
import opened KVTypes

datatype TableIndex = TableIndex(i:int)

predicate WFTableIndex(ti:TableIndex)   // There are two tables.
{
    0 <= ti.i <= 1
}

function OppositeTableIndex(ti:TableIndex) : TableIndex
{
    TableIndex(1 - ti.i)
}

datatype TableAddress = TableAddress(a:int)

datatype Slot = Value(datum:Datum) | Pointer(addr:TableAddress) | Empty
datatype Node = Node(pivots:seq<Key>, slots:seq<Slot>)

}

module TreeDisk refines Disk {
import opened TreeTypes

datatype Sector =
    | Superblock(liveTable:TableIndex)
    | TableSector
    | NodeSector(node:Node)

} // module TreeDisk



// TODO I was lying awake thinking: we probably actually want three tables. The persistent table,
// which is on disk (and never in memory except to prime the ephemeral table), the ephemeral table,
// and then a checkpointed copy of the ephemeral table so that a commit writeback can proceed in
// parallel with ongoing activity. But I'm not sure it's worth frying that fish now, when we have
// big data structure changes to make later.

module ImmutableDiskTreeImpl {
import opened MissingLibrary
import opened KVTypes
import opened TreeTypes
import TreeDisk

type LBA = TreeDisk.LBA
type Sector = TreeDisk.Sector

type View = map<LBA, Sector>    // A view of the disk, either through a cache or just by looking at the disk.

datatype CacheLineState = Dirty | Clean
datatype CacheLine = CacheLine(sector:Sector, state:CacheLineState)
type Cache = map<LBA, CacheLine>
function {:opaque} ViewOfCache(cache:Cache) : View
{
    map lba | lba in cache :: cache[lba].sector
}


datatype NBA = Unused | Used(nidx:int)  // A Node Block Address is an offset into the node-sectors region of the disk.

datatype Constants = Constants(
    tableEntries:int,    // How many entries in the table (allocatable data blocks on the disk)
    tableSectors:int     // How many sectors to set aside for each indirection table
    )

predicate WFConstants(k:Constants)
{
    && 0 < k.tableSectors
}

type Table = seq<NBA>   // An indirection table mapping addresses (indices into the table) to NBAs

predicate WFTable(k:Constants, table:Table)
{
    |table| == k.tableEntries
}

function HeaderSize(k:Constants) : int
{
    1                       // one superblock
    + 2*k.tableSectors      // two indirection tables
}

function DiskSize(k:Constants) : int
{
    HeaderSize(k)
    + k.tableEntries        // and a bunch of rewritable data sectors
}

predicate ValidNba(k:Constants, nba:NBA)
{
    && nba.Used?
    && 0 <= nba.nidx < DiskSize(k) - HeaderSize(k)
}

function LbaForNba(k:Constants, nba:NBA) : LBA
    requires ValidNba(k, nba)
{
    HeaderSize(k) + nba.nidx
}

datatype Variables = Variables(
    cache:Cache,
    ephemeralTable:Table,    // The ephemeral table, ready to write out on a commit

    // True only once the ephemeral table has a history tracking back to the
    // persistent table. (Cache can operate regardless of ready flag.)
    ready:bool
    )


// The superblock lives at the beginning of the disk
function SUPERBLOCK_LBA() : LBA { 0 }

predicate WFNode(node:Node) {
    |node.pivots| == |node.slots| - 1
}

predicate WFVariables(k:Constants, s:Variables)
{
    WFTable(k, s.ephemeralTable)  // maintained as an invariant, so not unreasonable to conjoin to actions.
}

function ROOT_ADDR() : TableAddress { TableAddress(0) }    // Address of the root node in either table

// We assume marshalling and unmarshalling functions for Tables to sectors.
function UnmarshallTable(k:Constants, sectors:seq<Sector>) : (tbl:Table)
    requires |sectors| == k.tableSectors
    ensures WFTable(k, tbl)

function MarshallTable(k:Constants, tbl:Table) : (sectors:seq<Sector>)
    requires WFTable(k, tbl)
    ensures |sectors| == k.tableSectors

lemma {:axiom} Marshalling(k:Constants)
    ensures forall t :: WFTable(k, t) ==>
        UnmarshallTable(k, MarshallTable(k, t)) == t
    ensures forall sectors :: |sectors| == k.tableSectors ==>
        MarshallTable(k, UnmarshallTable(k, sectors)) == sectors    // a bit too strong?

///////////////////////////////////////////////////////////////////////////////////////
// The view predicates are usable either on the cache (running case) or against the
// disk image (Init predicate).

predicate SectorInView(view:View, lba:LBA, sector:Sector)
{
    && lba in view
    && view[lba] == sector
}

function TableBegin(k:Constants, ti:TableIndex) : LBA
    requires WFTableIndex(ti)
{
    1 + k.tableSectors * ti.i
}

// Everything you need to look up the persistent table
datatype TableLookup = TableLookup(super:Sector, ti:TableIndex, table:Table, sectors:seq<Sector>)

predicate WFTableLookup(k:Constants, tl:TableLookup)
{
    && WFTableIndex(tl.ti)
    && WFTable(k, tl.table)
}

predicate ValidTableSectorIndex(k:Constants, tblSectorIdx:int)
{
    0 <= tblSectorIdx < k.tableSectors
}

function LbaForTableOffset(k:Constants, ti:TableIndex, tblSectorIdx:int) : LBA
    requires WFTableIndex(ti)
    requires ValidTableSectorIndex(k, tblSectorIdx)
{
    TableBegin(k, ti) + tblSectorIdx
}

predicate ViewContains(view:View, start:LBA, count:int)
{
    forall lba :: start <= lba < start+count ==> lba in view
}

predicate PlausibleViewRange(k:Constants, start:LBA, count:int)
{
    0 <= start <= start+count <= DiskSize(k)
}

function {:opaque} SubsequenceFromFullView(k:Constants, view:View, start:LBA, count:int) : (s:seq<Sector>)
    requires ViewContains(view, start, count)
    requires 0<count
    requires PlausibleViewRange(k, start, count)
    ensures |s| == count
    ensures forall i :: 0<=i<count ==> view[start + i] == s[i]
{
    if count == 1
    then [view[start]]
    else SubsequenceFromFullView(k, view, start, count-1) + [view[start+count-1]]
}

predicate TableInView(k:Constants, view:View, tl:TableLookup)
    requires WFConstants(k)
    requires WFTableIndex(tl.ti)
{
    && |tl.sectors| == k.tableSectors
    && PlausibleViewRange(k, TableBegin(k, tl.ti), k.tableSectors)
    && ViewContains(view, TableBegin(k, tl.ti), k.tableSectors)
    && tl.sectors == SubsequenceFromFullView(k, view, TableBegin(k, tl.ti), k.tableSectors)
    && tl.table == UnmarshallTable(k, tl.sectors)
}

predicate PersistentTableIndexInView(view:View, ti:TableIndex, super:Sector)
{
    && SectorInView(view, SUPERBLOCK_LBA(), super)
    && super == TreeDisk.Superblock(ti)
    && WFTableIndex(ti)    // If you need to fsck, this spec stalls.
}

//////////////////////////////////////////////////////////////////////////////
// These predicates are shorthands useful in the running case.

predicate ViewNodeRead(k:Constants, view:View, nba:NBA, node:Node)
    requires ValidNba(k, nba)
{
    && SectorInView(view, LbaForNba(k, nba), TreeDisk.NodeSector(node))
    // We toss WFNode in here to keep other expressions tidy; as with any WF, this can
    // create a liveness problem (can't read that disk sector with a malformed node).
    // Even if we don't prove liveness, we can mitigate that concern by including a
    // WF invariant.
    && WFNode(node)
}

predicate KnowTable(k:Constants, s:Variables, tl:TableLookup)
    requires WFConstants(k)
    requires WFTableIndex(tl.ti)
{
    TableInView(k, ViewOfCache(s.cache), tl)
}

predicate KnowPersistentTableIndex(k:Constants, s:Variables, ti:TableIndex, super:Sector)
{
    PersistentTableIndexInView(ViewOfCache(s.cache), ti, super)
}

predicate KnowPersistentTable(k:Constants, s:Variables, tl:TableLookup)
    requires WFConstants(k)
{
    && KnowPersistentTableIndex(k, s, tl.ti, tl.super)
    && KnowTable(k, s, tl)
}

//////////////////////////////////////////////////////////////////////////////
// Ranges
datatype Range = Range(loinc:Key, hiexc:Key)

function FULL_RANGE() : Range
{
    Range(MIN_KEY(), MAX_KEY())
}

predicate RangeContains(range:Range, key:Key)
{
    && KeyLeq(range.loinc, key)
    && KeyLe(key, range.hiexc)
}

predicate ValidSlotIndex(node:Node, idx:int)
{
     0 <= idx < |node.slots|
}

// If all of node's keys are bounded by nodeRange, then
// the keys in the i'th slot of node are bounded by range.
function RangeBoundForSlotIdx(node:Node, nodeRange:Range, idx:int) : (range:Range)
    requires WFNode(node)
    requires ValidSlotIndex(node, idx)
{
    Range(
        if idx==0 then nodeRange.loinc else node.pivots[idx-1],
        if idx==|node.slots|-1 then nodeRange.hiexc else node.pivots[idx])
}

//////////////////////////////////////////////////////////////////////////////
// Lookup
datatype Layer = Layer(
    addr:TableAddress,
    node:Node,      // the node at the addr
    slot:int,       // the slot pointing to the next node below
    slotRange:Range     // the range that bounds this slot (and hence the node below)
    )

datatype Lookup = Lookup(layers:seq<Layer>)

predicate WFLookup(lookup:Lookup)
{
    0 < |lookup.layers|
}

// Naming a term to encourage triggering on it.
predicate ValidLayerIndex(lookup:Lookup, i:int)
{
    0<=i<|lookup.layers|
}

predicate LookupHasValidNodes(lookup:Lookup)
{
    forall i {:trigger ValidLayerIndex(lookup, i)} :: ValidLayerIndex(lookup, i) ==> WFNode(lookup.layers[i].node)
}

predicate LookupHasValidSlotIndices(lookup:Lookup)
{
    forall i {:trigger ValidLayerIndex(lookup, i)} :: ValidLayerIndex(lookup, i) ==>
        && var layer := lookup.layers[i];
        && ValidSlotIndex(layer.node, layer.slot)
}

// Dafny weakness: You can build ValidAddress from ValidAddresses, but going
// the other way gives "Error: a set comprehension must produce a finite set,
// but Dafny's heuristics can't figure out..."
function {:opaque} ValidAddressesDef(k:Constants) : (va:set<TableAddress>)
{
    set a | 0 <= a < k.tableEntries :: TableAddress(a)
}

lemma ValidAddressesProp(k:Constants, va:set<TableAddress>)
    requires ValidAddressesDef(k) == va
    ensures forall addr :: addr in va <==> 0 <= addr.a < k.tableEntries
{
    reveal_ValidAddressesDef();
    forall addr:TableAddress | 0 <= addr.a < k.tableEntries ensures addr in va 
    {
    }
}

function ValidAddresses(k:Constants) : (va:set<TableAddress>)
    ensures forall addr :: addr in va <==> 0 <= addr.a < k.tableEntries
{
    ValidAddressesProp(k, ValidAddressesDef(k));
    ValidAddressesDef(k)
}

predicate ValidAddress(k:Constants, addr:TableAddress)
    ensures ValidAddress(k, addr) <==> 0 <= addr.a < k.tableEntries
{
    addr in ValidAddresses(k)
}

function TableAt(k:Constants, table:Table, addr:TableAddress) : NBA
    requires WFTable(k, table)
    requires ValidAddress(k, addr)
{
    table[addr.a]
}

predicate LookupHasValidAddresses(k:Constants, lookup:Lookup)
{
    forall i {:trigger ValidLayerIndex(lookup, i)} :: ValidLayerIndex(lookup, i)
        ==> ValidAddress(k, lookup.layers[i].addr)
}

predicate LookupHonorsPointerLinksAtLayer(lookup:Lookup, i:int)
    requires LookupHasValidSlotIndices(lookup)
    requires 0 <= i < |lookup.layers|
{
    var layer := lookup.layers[i];
    if i==0
    then layer.addr == ROOT_ADDR()
    else
        var uplayer := lookup.layers[i-1];
        uplayer.node.slots[uplayer.slot] == Pointer(layer.addr)
}

predicate LookupHonorsPointerLinks(lookup:Lookup)
    requires LookupHasValidSlotIndices(lookup)
{
    forall i :: 0<=i<|lookup.layers| ==>
        LookupHonorsPointerLinksAtLayer(lookup, i)
}

function NodeRangeAtLayer(lookup:Lookup, i:int) : Range
    requires 0<=i<|lookup.layers|
{
    if i==0 then FULL_RANGE() else lookup.layers[i-1].slotRange
}

predicate LookupHonorsRangesAt(lookup:Lookup, i:int)
    requires LookupHasValidNodes(lookup)
    requires LookupHasValidSlotIndices(lookup)
    requires ValidLayerIndex(lookup, i)
{
    var layer := lookup.layers[i];
    RangeBoundForSlotIdx(layer.node, NodeRangeAtLayer(lookup, i), layer.slot) == layer.slotRange
}

predicate LookupHonorsRanges(lookup:Lookup)
    requires LookupHasValidNodes(lookup)
    requires LookupHasValidSlotIndices(lookup)
{
    forall i :: ValidLayerIndex(lookup, i) ==> LookupHonorsRangesAt(lookup, i)
}

predicate AddressResolvesToNode(k:Constants, table:Table, view:View, addr:TableAddress, node:Node)
{
    && var nba := TableAt(k, table, addr);
    && ValidNba(k, nba)
    && ViewNodeRead(k, view, nba, node)
}

predicate LookupMatchesViewAtLayer(k:Constants, table:Table, view:View, lookup:Lookup, i:int)
    requires WFLookup(lookup)
    requires WFTable(k, table)
    requires LookupHasValidAddresses(k, lookup)
    requires ValidLayerIndex(lookup, i)
{
    && var layer := lookup.layers[i];
    && AddressResolvesToNode(k, table, view, layer.addr, layer.node)
}

predicate LookupMatchesView(k:Constants, table:Table, view:View, lookup:Lookup)
    requires WFLookup(lookup)
    requires WFTable(k, table)
    requires LookupHasValidAddresses(k, lookup)
{
    forall i {:trigger ValidLayerIndex(lookup, i)} :: ValidLayerIndex(lookup, i)
        ==> LookupMatchesViewAtLayer(k, table, view, lookup, i)
}

predicate ValidLookupInView(k:Constants, table:Table, view:View, lookup:Lookup)
{
    && WFLookup(lookup)
    && LookupHasValidNodes(lookup)
    && LookupHasValidSlotIndices(lookup)
    && LookupHasValidAddresses(k, lookup)
    && LookupHonorsPointerLinks(lookup)
    && LookupHonorsRanges(lookup)
    && WFTable(k, table)
    && LookupMatchesView(k, table, view, lookup)
}

predicate ValidLookup(k:Constants, s:Variables, lookup:Lookup)
{
    && ValidLookupInView(k, s.ephemeralTable, ViewOfCache(s.cache), lookup)
}

predicate SlotSatisfiesQuery(slot:Slot, key:Key, value:Option<Value>)
{
    || (slot.Value? && slot.datum.key == key && value.Some? && slot.datum.value == value.value)
    || (slot.Value? && slot.datum.key != key && value.None?)
    || (slot.Empty? && value.None?)
}

// The slot to which this lookup leads.
function TerminalSlot(lookup:Lookup) : Slot
    requires WFLookup(lookup)
    requires LookupHasValidSlotIndices(lookup)
{
    var lastLayer := Last(lookup.layers);
    lastLayer.node.slots[lastLayer.slot]
}

predicate LookupSatisfiesQuery(k:Constants, s:Variables, lookup:Lookup, key:Key, value:Option<Value>)
{
    && ValidLookup(k, s, lookup)
    && SlotSatisfiesQuery(TerminalSlot(lookup), key, value)
}

predicate QueryAction(k:Constants, s:Variables, s':Variables, diskStep:TreeDisk.Step, lookup:Lookup, key:Key, value:Option<Value>)
{
    && s.ready
    && LookupSatisfiesQuery(k, s, lookup, key, value)

    && diskStep == TreeDisk.IdleStep
    && s' == s
}

//////////////////////////////////////////////////////////////////////////////
// Mutations

function NodeReplaceSlot(node:Node, i:int, slot:Slot) : Node
    requires WFNode(node)
    requires 0<=i<|node.slots|
{
    Node(node.pivots,
        node.slots[..i] + [slot] + node.slots[i+1..])
}

// Replace slot (which starts at pivots[slot-1]) with newSlots, subdivided by newPivots.
function NodeReplaceSlotWithSlotSequence(node:Node, slot:int, newPivots:seq<Key>, newSlots:seq<Slot>) : Node
    requires WFNode(node)
    requires 0<=slot<|node.slots|
    requires |newSlots| == |newPivots| + 1
{
    Node(
        node.pivots[..slot] + newPivots + node.pivots[slot..],
        node.slots[..slot] + newSlots + node.slots[slot+1..])
}


function ReplaceSlotForInsert(node:Node, slotIdx:int, newDatum:Datum) : Node
    requires WFNode(node)
    requires ValidSlotIndex(node, slotIdx)
    requires !node.slots[slotIdx].Pointer?
{
    var slot := node.slots[slotIdx];

    if slot.Empty? || newDatum.key == slot.datum.key
        // Replace an empty or same-key datum in place
    then NodeReplaceSlot(node, slotIdx, Value(newDatum))
    else if KeyLe(newDatum.key, slot.datum.key)
        // New datum goes to the left, so we'll split a pivot to the right with the old key
    then NodeReplaceSlotWithSlotSequence(node, slotIdx, [slot.datum.key], [Value(newDatum), slot])
        // New datum goes to the right, so we'll split a pivot with the new key
    else NodeReplaceSlotWithSlotSequence(node, slotIdx, [newDatum.key], [slot, Value(newDatum)])
}

function {:opaque} AllocatedNodeBlocks(k:Constants, table:Table) : (alloc:set<NBA>)
    requires WFTable(k, table)
    ensures forall nba :: nba in alloc ==> nba.Used?
{
    set addr:TableAddress | addr in ValidAddresses(k) && TableAt(k, table, addr).Used? :: TableAt(k, table, addr)
}

predicate NBAUnusedInTable(k:Constants, table:Table, nba:NBA)
    requires WFTable(k, table)
{
    !(nba in AllocatedNodeBlocks(k, table))
}

predicate AllocateNBA(k:Constants, s:Variables, nba:NBA, persistentTl:TableLookup)
    requires WFConstants(k)
    requires WFTable(k, s.ephemeralTable)
{
    && ValidNba(k, nba)
    // Not used in the ephemeral table
    && NBAUnusedInTable(k, s.ephemeralTable, nba)
    // And not used in the persistent table
    && KnowPersistentTable(k, s, persistentTl)
    && NBAUnusedInTable(k, persistentTl.table, nba)
}

predicate AllocateAddr(k:Constants, s:Variables, childAddr:TableAddress)
    requires WFTable(k, s.ephemeralTable)
{
    && ValidAddress(k, childAddr)
    && TableAt(k, s.ephemeralTable, childAddr).Unused?
}

function WriteSectorToCache(k:Constants, cache:Cache, lba:LBA, sector:Sector) : Cache
{
    cache[lba := CacheLine(sector, Dirty)]
}

function WriteNodeToCache(k:Constants, cache:Cache, nba:NBA, node:Node) : Cache
    requires ValidNba(k, nba)
{
    WriteSectorToCache(k, cache, LbaForNba(k, nba), TreeDisk.NodeSector(node))
}

datatype NodeEdit = NodeEdit(   // What you need to know to edit a slot of a node in the tree:
    lookup:Lookup,              // Path to the adjusted node, to prove that it belongs to the tree
    tableLookup:TableLookup,    // Required to allocate without stomping references from persistent table
    replacementNba:NBA,         // node address for the replacement node (with the changed slot)
    replacementNode:Node        // the new node that will replace the one being edited
    )

function EditLast(edit:NodeEdit) : Layer
    requires 0 < |edit.lookup.layers|
{
    Last(edit.lookup.layers)
}

// This is a prototype action -- it has both enabling conditions and transition
// relations.  The caller supplies an additional constraint that ensures the
// 'edit' record does what its action needs.
predicate ApplyEdit(k:Constants, s:Variables, s':Variables, diskStep:TreeDisk.Step, edit:NodeEdit, key:Key, oldValue:Option<Value>)
    requires WFConstants(k)
{
    && s.ready
    && WFVariables(k, s)
    && LookupSatisfiesQuery(k, s, edit.lookup, key, oldValue)
    && AllocateNBA(k, s, edit.replacementNba, edit.tableLookup)

    && diskStep == TreeDisk.IdleStep
    && s'.cache == WriteNodeToCache(k, s.cache, edit.replacementNba, edit.replacementNode)
    // Through the magic of table indirection, lastLayer.node's child is suddenly switched to point to replacementNode.
    && s'.ephemeralTable == s.ephemeralTable[EditLast(edit).addr.a := edit.replacementNba]
    && s'.ready
}

predicate InsertAction(k:Constants, s:Variables, s':Variables, diskStep:TreeDisk.Step, edit:NodeEdit, key:Key, oldValue:Option<Value>, newValue:Value)
    requires WFConstants(k)
{
    && ApplyEdit(k, s, s', diskStep, edit, key, oldValue)
    && edit.replacementNode == ReplaceSlotForInsert(EditLast(edit).node, EditLast(edit).slot, Datum(key, newValue))
}

// Delete is un-insert.
predicate ReplacesSlotForDelete(oldNode:Node, newNode:Node, slotIdx:int, deletedDatum:Datum)
{
    // Caller is 'existing' a newNode into being; we need to force it to satisfy the preconditions
    // for ChildEquivalentToSlotGroup.
    // (TODO We could just reduce things to this version, and accept the fact
    // that this check will duplicate what the invariant already does.)
    && WFNode(newNode)
    && ValidSlotIndex(newNode, slotIdx)
    && !newNode.slots[slotIdx].Pointer?
    // TODO this could make up an "old" value that got inserted-over.
    && oldNode == ReplaceSlotForInsert(newNode, slotIdx, deletedDatum)
}

predicate DeleteAction(k:Constants, s:Variables, s':Variables, diskStep:TreeDisk.Step, edit:NodeEdit, key:Key, deletedValue:Value)
    requires WFConstants(k)
{
    && ApplyEdit(k, s, s', diskStep, edit, key, Some(deletedValue))
    && ReplacesSlotForDelete(EditLast(edit).node, edit.replacementNode, EditLast(edit).slot, Datum(key, deletedValue))
}

predicate ChildEquivalentToSlotGroup(directNode:Node, replacedSlot:int, indirectNode:Node, childAddr:TableAddress, childNode:Node)
    requires WFNode(indirectNode)
    requires 0<=replacedSlot<|indirectNode.slots|
    requires |childNode.slots| == |childNode.pivots| + 1
{
    && directNode == NodeReplaceSlotWithSlotSequence(indirectNode, replacedSlot, childNode.pivots, childNode.slots)
    && indirectNode.slots[replacedSlot] == Pointer(childAddr)
}

predicate ChildEquivalentToSlotGroupForExpand(directNode:Node, replacedSlot:int, indirectNode:Node, childAddr:TableAddress, childNode:Node)
{
    // Caller is 'existing' an indirectNode into being; we need to force it to satisfy the preconditions
    // for ChildEquivalentToSlotGroup.
    // (TODO We could just reduce things to this version, and accept the fact
    // that this check will duplicate what the invariant already does.)
    && WFNode(indirectNode)
    && 0<=replacedSlot<|indirectNode.slots|
    && WFNode(childNode)
    && ChildEquivalentToSlotGroup(directNode, replacedSlot, indirectNode, childAddr, childNode)
}

datatype Janitorial = Janitorial(
    edit:NodeEdit,              // The Lookup and edit info for the parent node being modified
    childAddr:TableAddress,     // table index where child is coming from or allocated to
    childNba:NBA,               // node address where child is coming from or allocated to
    childNode:Node,             // child node exchanging places with subrange of parent slots
    childEntry':NBA             // what becomes of the table reference for childAddr after the action
    )

// TODO consider breaking these weird abstract action-helpers into
// enabling-condition & update parts to make caller read more imperatively.
predicate JanitorialAction(k:Constants, s:Variables, s':Variables, diskStep:TreeDisk.Step, j:Janitorial)
    requires WFConstants(k)
    requires j.childNba.Used?
    requires ValidAddress(k, j.childAddr)
{
    && s.ready
    && WFVariables(k, s)
    && ValidLookup(k, s, j.edit.lookup)
    && AllocateNBA(k, s, j.edit.replacementNba, j.edit.tableLookup)
    && ValidNba(k, j.childNba)

    && diskStep == TreeDisk.IdleStep

    // The second write (j.childNba) "writes" the child to memory in the expand
    // case, and is a no-op in the contract case.
    && s'.cache == WriteNodeToCache(k,
                    WriteNodeToCache(k, s.cache, j.edit.replacementNba, j.edit.replacementNode),
                    j.childNba, j.childNode)

    // Through the magic of table indirection, lastLayer.node's parent is
    // suddenly switched to point to replacementNode.
    && s'.ephemeralTable ==
        s.ephemeralTable[EditLast(j.edit).addr.a := j.edit.replacementNba][j.childAddr.a := j.childEntry']
    && s'.ready
}

predicate ExpandAction(k:Constants, s:Variables, s':Variables, diskStep:TreeDisk.Step, j:Janitorial)
    requires WFConstants(k)
{
    && WFTable(k, s.ephemeralTable)
    && AllocateNBA(k, s, j.childNba, j.edit.tableLookup)
    && AllocateAddr(k, s, j.childAddr)
    && JanitorialAction(k, s, s', diskStep, j)
    && ChildEquivalentToSlotGroupForExpand(EditLast(j.edit).node, EditLast(j.edit).slot, j.edit.replacementNode, j.childAddr, j.childNode)
    && j.childEntry' == j.childNba  // record the allocated reference
}

predicate ContractAction(k:Constants, s:Variables, s':Variables, diskStep:TreeDisk.Step, j:Janitorial)
    requires WFConstants(k)
{
    && WFVariables(k, s)
    && ValidAddress(k, j.childAddr)
    && TableAt(k, s.ephemeralTable, j.childAddr).Used?
    && j.childNba == TableAt(k, s.ephemeralTable, j.childAddr)
    && JanitorialAction(k, s, s', diskStep, j)
    && Pointer(j.childAddr) == EditLast(j.edit).node.slots[EditLast(j.edit).slot]
    && ViewNodeRead(k, ViewOfCache(s.cache), j.childNba, j.childNode)
    && ChildEquivalentToSlotGroup(j.edit.replacementNode, EditLast(j.edit).slot, EditLast(j.edit).node, j.childAddr, j.childNode)
    && j.childEntry' == Unused  // free the child reference
}

predicate WriteCore(k:Constants, s:Variables, s':Variables, diskStep:TreeDisk.Step, lba:LBA, sector:Sector)
{
    && s.ready

    && diskStep == TreeDisk.WriteStep(lba, sector)
    && s'.cache == s.cache[lba := CacheLine(sector, Clean)]
    && s'.ephemeralTable == s.ephemeralTable
    && s'.ready == true
}

// It's always okay to write back cached sectors, whenever we feel like it,
// except: we can't write back the superblock pointer; that's a Commit.
predicate WriteBackAction(k:Constants, s:Variables, s':Variables, diskStep:TreeDisk.Step, lba:LBA)
{
    && 1 <= lba < DiskSize(k)
    && lba in s.cache
    && s.cache[lba].state.Dirty?    // performance spec: don't write clean things back. :v)
    && WriteCore(k, s, s', diskStep, lba, s.cache[lba].sector)
}

// Dirty a sector that stores the ephemeral table.
predicate EmitTableAction(k:Constants, s:Variables, s':Variables, diskStep:TreeDisk.Step, persistentTi:TableIndex, super:Sector, tblSectorIdx:int)
{
    && s.ready
    && WFVariables(k, s)
    && KnowPersistentTableIndex(k, s, persistentTi, super)
    && var ephemeralTi := OppositeTableIndex(persistentTi);
    && ValidTableSectorIndex(k, tblSectorIdx)
    && var lba := LbaForTableOffset(k, ephemeralTi, tblSectorIdx);
    // Actually, once we've constrained ti and ValidTableSectorIndex, we've got an
    // lba in the ephemeral table region; we can write whatever we want there.
    // The next line is just good advice about what might help to write. :v) 
    && var sector := MarshallTable(k, s.ephemeralTable)[tblSectorIdx];
    
    && diskStep == TreeDisk.IdleStep
    && s'.cache == WriteSectorToCache(k, s.cache, lba, sector)
    && s'.ephemeralTable == s.ephemeralTable
    && s'.ready == true
}

// TODO how about a writeback for node sectors?

predicate CacheIsClean(cache:Cache)
{
    forall lba :: lba in cache ==> cache[lba].state.Clean?
}

// Once we've written enough sectors (both table and node), life is good! Flip
// the flag.
// TODO For this version, we'll be simple and just demand that every line of
// the cache be Clean.
predicate CommitAction(k:Constants, s:Variables, s':Variables, diskStep:TreeDisk.Step, persistentTi:TableIndex, super:Sector)
{
    && s.ready
    && KnowPersistentTableIndex(k, s, persistentTi, super)
    && var ephemeralTi := OppositeTableIndex(persistentTi);
    // TODO and need to Know the Ephemeral Table
    && var newSuper := TreeDisk.Superblock(ephemeralTi);
    && CacheIsClean(s.cache)

    // Write the new superblock THROUGH the cache. Everything in the cache stays clean.
    && WriteCore(k, s, s', diskStep, SUPERBLOCK_LBA(), newSuper)
    // TODO unchanged everything else
}

// TODO trusted code
predicate CrashAction(k:Constants, s:Variables, s':Variables, diskStep:TreeDisk.Step)
{
    && diskStep == TreeDisk.IdleStep
    && s'.cache.Keys == {}
    // s'.ephemeralTable is unconstrained.
    && s'.ready == false
}

// You can make an ephemeral table ready to write
predicate RecoverAction(k:Constants, s:Variables, s':Variables, diskStep:TreeDisk.Step, super:Sector, persistentTl:TableLookup)
    requires WFConstants(k)
{
    && !s.ready
    && KnowPersistentTableIndex(k, s, persistentTl.ti, super)
    && WFTableIndex(persistentTl.ti)
    && KnowTable(k, s, persistentTl)

    && diskStep == TreeDisk.IdleStep
    && s'.cache == s.cache
    // we need to know the whole persistent table: the root ensures the
    // ephemeral tree state matches; the rest of the entries avoid incorrectly
    // marking unused sectors as allocated.
    && s'.ephemeralTable == persistentTl.table
    && s'.ready == true
}

// Bring a sector into the cache
predicate CacheFaultAction(k:Constants, s:Variables, s':Variables, diskStep:TreeDisk.Step, lba:LBA, sector:Sector)
{
    && !(lba in s.cache)    // Don't read a sector that's already cached ... if it's dirty, we'll lose data!
    && diskStep == TreeDisk.ReadStep(lba, sector)
    && s'.cache == s.cache[lba := CacheLine(sector, Clean)]
    && s'.ephemeralTable == s.ephemeralTable
    && s'.ready == s.ready
}

// It's okay to evict clean entries from the cache whenever.
predicate CacheEvictAction(k:Constants, s:Variables, s':Variables, diskStep:TreeDisk.Step, lba:LBA)
{
    && lba in s.cache
    && s.cache[lba].state.Clean?
    && diskStep == TreeDisk.IdleStep
    && s'.cache == MapRemove(s.cache, lba)
    && s'.ephemeralTable == s.ephemeralTable
    && s'.ready == s.ready
}

predicate InitTable(k:Constants, table:Table, rootNba:NBA)
{
    && 0 < |table|
    && WFTable(k, table)
    && TableAt(k, table, ROOT_ADDR()) == rootNba
    && (forall addr:TableAddress :: 0 <= addr.a < |table| && addr != ROOT_ADDR()
        ==> TableAt(k, table, addr).Unused?)
}

// Constraints on just the configuration (Constants)
predicate PlausibleDiskSize(k:Constants)
{
    && 0 < k.tableSectors
    && 0 < k.tableEntries
}

predicate FullView(k:Constants, view:View)
{
    forall lba :: 0 <= lba < DiskSize(k) <==> lba in view
}

datatype Mkfs = Mkfs(tl:TableLookup)

predicate DiskInMkfsState(k:Constants, mkfs:Mkfs, diskView:View)
    requires FullView(k, diskView)
{
    // right-sized disk
    && PlausibleDiskSize(k)
    && 0 < k.tableEntries

    // Empty persistent table
    && WFTableIndex(mkfs.tl.ti)
    && PersistentTableIndexInView(diskView, mkfs.tl.ti, mkfs.tl.super)
    && TableInView(k, diskView, mkfs.tl)
    // I arbitrarily demand that the root block be stored in node data sector 0.
    && InitTable(k, mkfs.tl.table, Used(0))
    && diskView[LbaForNba(k, Used(0))] == TreeDisk.NodeSector(Node([], [Empty]))
}

// Supply a concrete mkfs image to (a) demonstrate that it is actually possible to initialize the disk
// and (b) avoid an exists so Dafny can see the Init properties easily.
function mkfs(k:Constants) : Mkfs
    requires PlausibleDiskSize(k)
{
    var ti := TableIndex(0);
    var super := TreeDisk.Superblock(ti);
    var table := [Used(0)] + MemsetSeq(Unused, k.tableEntries-1);
    var sectors := MarshallTable(k, table);
    var mkfs := Mkfs(TableLookup(super, ti, table, sectors));
    mkfs
}

function {:opaque} ViewOfDisk(diskImage:seq<Sector>) : (view:View)
    ensures forall lba :: 0<=lba<|diskImage| <==> lba in view.Keys
    ensures forall lba :: 0<=lba<|diskImage| ==> view[lba] == diskImage[lba]
{
    map lba | 0 <= lba < |diskImage| :: diskImage[lba]
}

predicate Init(k:Constants, s:Variables, diskImage:seq<Sector>)
{
    && PlausibleDiskSize(k)
    && |diskImage| == DiskSize(k)
    && DiskInMkfsState(k, mkfs(k), ViewOfDisk(diskImage))
    && s.cache.Keys == {}
    // No constraint on ephemeralTable, because we'll use !s.ready to force a RecoveryAction.
    && s.ready == false // We'll simply RecoverAction the initial disk.
}

datatype Step =
    | QueryActionStep(lookup:Lookup, key:Key, value:Option<Value>)
    | InsertActionStep(edit:NodeEdit, key:Key, oldValue:Option<Value>, newValue:Value)
    | DeleteActionStep(edit:NodeEdit, key:Key, deletedValue:Value)
    | ExpandActionStep(j:Janitorial)
    | ContractActionStep(j:Janitorial)
    | WriteBackActionStep(lba:LBA)
    | EmitTableActionStep(persistentTi:TableIndex, super:Sector, tblSectorIdx:int)
    | CommitActionStep(persistentTi:TableIndex, super:Sector)
    | CrashActionStep
    | RecoverActionStep(super:Sector, persistentTl:TableLookup)
    | CacheFaultActionStep(lba:LBA, sector:Sector)
    | CacheEvictActionStep(lba:LBA)

predicate {:opaque} NextStep(k:Constants, s:Variables, s':Variables, diskStep:TreeDisk.Step, step:Step)
    requires WFConstants(k)
{
    match step {
        case  QueryActionStep(lookup, key, value) => QueryAction(k, s, s', diskStep, lookup, key, value)
        case  InsertActionStep(edit, key, oldValue, newValue) => InsertAction(k, s, s', diskStep, edit, key, oldValue, newValue)
        case  DeleteActionStep(edit, key, deletedValue) => DeleteAction(k, s, s', diskStep, edit, key, deletedValue)
        case  ExpandActionStep(j) => ExpandAction(k, s, s', diskStep, j)
        case  ContractActionStep(j) => ContractAction(k, s, s', diskStep, j)
        case  WriteBackActionStep(lba) => WriteBackAction(k, s, s', diskStep, lba)
        case  EmitTableActionStep(persistentTi, super, tblSectorIdx)
                => EmitTableAction(k, s, s', diskStep, persistentTi, super, tblSectorIdx)
        case  CommitActionStep(persistentTi, super) => CommitAction(k, s, s', diskStep, persistentTi, super)
        case  CrashActionStep => CrashAction(k, s, s', diskStep)
        case  RecoverActionStep(super, persistentTl) => RecoverAction(k, s, s', diskStep, super, persistentTl)
        case  CacheFaultActionStep(lba, sector) => CacheFaultAction(k, s, s', diskStep, lba, sector)
        case  CacheEvictActionStep(lba) => CacheEvictAction(k, s, s', diskStep, lba)
    }
}

/*XXX
predicate {:opaque} Next(k:Constants, s:Variables, s':Variables)
    requires WFConstants(k)
{
    exists step :: NextStep(k, s, s', step)
}
*/

} // module

module ImmutableDiskTree {
import opened MissingLibrary
import opened KVTypes
import opened TreeTypes
import TreeDisk
import ImmutableDiskTreeImpl

datatype Constants = Constants(
    disk:TreeDisk.Constants,
    impl:ImmutableDiskTreeImpl.Constants)

predicate WFConstants(k:Constants)
{
    k.disk.size == ImmutableDiskTreeImpl.DiskSize(k.impl)
}

datatype Variables = Variables(
    disk:TreeDisk.Variables,
    impl:ImmutableDiskTreeImpl.Variables)

datatype Step = Step(impl:ImmutableDiskTreeImpl.Step, disk:TreeDisk.Step)

predicate NextStep(k:Constants, s:Variables, s':Variables, step:Step)
{
    && ImmutableDiskTreeImpl.WFConstants(k.impl)
    && ImmutableDiskTreeImpl.NextStep(k.impl, s.impl, s'.impl, step.disk, step.impl)
    && TreeDisk.NextStep(k.disk, s.disk, s'.disk, step.disk)
    && (step.impl.CrashActionStep? ==> step.disk.IdleStep?)
}

predicate Init(k:Constants, s:Variables)
{
    && TreeDisk.Init(k.disk, s.disk)
    && ImmutableDiskTreeImpl.Init(k.impl, s.impl, s.disk.sectors)
}

predicate {:opaque} Next(k:Constants, s:Variables, s':Variables)
{
    exists step :: NextStep(k, s, s', step)
}

}
