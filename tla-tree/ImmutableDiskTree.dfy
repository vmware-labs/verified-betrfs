include "MissingLibrary.dfy"
include "KVTypes.dfy"
include "Disk.dfy"

module TreeDisk refines Disk {
import opened KVTypes

type TableIndex = int
predicate WFTableIndex(ti:TableIndex)   // There are two tables.
{
    0 <= ti <= 1
}
function OppositeTableIndex(ti:TableIndex) : TableIndex
{
    1 - ti
}

datatype Slot = Value(datum:Datum) | Pointer(idx:int) | Empty
datatype Node = Node(pivots:seq<Key>, slots:seq<Slot>)
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

module CrashSafeTree {
import opened MissingLibrary
import opened KVTypes
import TreeDisk

type LBA = TreeDisk.LBA
type TableIndex = TreeDisk.TableIndex
type Slot = TreeDisk.Slot
type Node = TreeDisk.Node
type Sector = TreeDisk.Sector

type View = map<LBA, Sector>    // A view of the disk, either through a cache or just by looking at the disk.

datatype CacheLineState = Dirty | Clean
datatype CacheLine = CacheLine(sector:Sector, dirty:CacheLineState)
type Cache = map<LBA, CacheLine>
function {:opaque} ViewOfCache(cache:Cache) : View
{
    map lba | lba in cache :: cache[lba].sector
}


datatype NBA = Unused | Used(lba:LBA)  // A Node Block Address gets offset into the node-sectors region of the disk.

datatype Constants = Constants(
    disk:TreeDisk.Constants,
    tableEntries:int,    // How many entries in the table (allocatable data blocks on the disk)
    tableSectors:int     // How many sectors to set aside for each indirection table
    )

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

function LbaForNba(k:Constants, nba:NBA) : LBA
    requires nba.Used?
{
    HeaderSize(k) + nba.lba
}

datatype Variables = Variables(
    disk:TreeDisk.Variables,
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

function ROOT_ADDR() : int { 0 }    // Address of the root node in either table

// We assume marshalling and unmarshalling functions for Tables to sectors.
function UnmarshallTable(k:Constants, sectors:seq<Sector>) : Table
    requires |sectors| == k.tableSectors

function MarshallTable(k:Constants, t:Table) : (sectors:seq<Sector>)
    ensures |sectors| == k.tableSectors

lemma {:axiom} Marshalling(k:Constants)
    ensures forall t :: UnmarshallTable(k, MarshallTable(k, t)) == t
    ensures forall sectors :: UnmarshallTable(k, MarshallTable(k, sectors)) == sectors    // a bit too strong?

///////////////////////////////////////////////////////////////////////////////////////
// The view predicates are usable either on the cache (running case) or against the
// disk image (Init predicate).

predicate SectorInView(view:View, lba:LBA, sector:Sector)
{
    && lba in view
    && view[lba] == sector
}

function TableBegin(k:Constants, ti:TableIndex) : LBA
    requires TreeDisk.WFTableIndex(ti)
{
    1 + k.tableSectors * ti
}

datatype TableLookup = TableLookup(ti:TableIndex, table:Table, sectors:seq<Sector>)

predicate WFTableLookup(k:Constants, tl:TableLookup)
{
    && TreeDisk.WFTableIndex(tl.ti)
    && WFTable(k, tl.table)
}

predicate TableInView(k:Constants, view:View, tl:TableLookup)
    requires TreeDisk.WFTableIndex(tl.ti)
{
    && |tl.sectors| == k.tableSectors
    && (forall off :: 0 <= off < k.tableSectors ==>
        && var lba := off + TableBegin(k, tl.ti);
        && SectorInView(view, lba, tl.sectors[off])
       )
    && tl.table == UnmarshallTable(k, tl.sectors)
}

predicate PersistentTableIndexInView(view:View, ti:TableIndex, super:Sector)
{
    && SectorInView(view, SUPERBLOCK_LBA(), super)
    && super == TreeDisk.Superblock(ti)
}

//////////////////////////////////////////////////////////////////////////////
// These predicates are shorthands useful in the running case.

predicate CachedNodeRead(k:Constants, s:Variables, nba:NBA, node:Node)
    requires nba.Used?
{
    && SectorInView(ViewOfCache(s.cache), LbaForNba(k, nba), TreeDisk.NodeSector(node))
    // We toss WFNode in here to keep other expressions tidy; as with any WF, this can
    // create a liveness problem (can't read that disk sector with a malformed node).
    // Even if we don't prove liveness, we can mitigate that concern by including a
    // WF invariant.
    && WFNode(node)
}

predicate KnowTable(k:Constants, s:Variables, tl:TableLookup)
    requires TreeDisk.WFTableIndex(tl.ti)
{
    TableInView(k, ViewOfCache(s.cache), tl)
}

predicate KnowPersistentTableIndex(k:Constants, s:Variables, ti:TableIndex, super:Sector)
{
    PersistentTableIndexInView(ViewOfCache(s.cache), ti, super)
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
    addr:int,
    node:Node,      // the node at the addr
    slot:int,       // the slot pointing to the next node below
    slotRange:Range     // the range that bounds this slot (and hence the node below)
    )

datatype Lookup = Lookup(layers:seq<Layer>, tl:TableLookup)

predicate WFLookup(k:Constants, lookup:Lookup)
{
    && 0 < |lookup.layers|
    && WFTableLookup(k, lookup.tl)
}

predicate LookupHasValidNodes(lookup:Lookup)
{
    forall i :: 0<=i<|lookup.layers| ==> WFNode(lookup.layers[i].node)
}

predicate LookupHasValidSlotIndices(lookup:Lookup)
{
    forall i :: 0<=i<|lookup.layers| ==>
        && var layer := lookup.layers[i];
        && ValidSlotIndex(layer.node, layer.slot)
}

predicate ValidAddress(k:Constants, addr:int)
{
    0 <= addr < k.tableEntries
}

predicate LookupHasValidAddresses(k:Constants, lookup:Lookup)
{
    forall i :: 0<=i<|lookup.layers| ==> ValidAddress(k, lookup.layers[i].addr)
}

predicate LookupHonorsPointerLinks(lookup:Lookup)
    requires LookupHasValidSlotIndices(lookup)
{
    forall i :: 0<=i<|lookup.layers| ==>
        var layer := lookup.layers[i];
        if i==0
        then layer.addr == ROOT_ADDR()
        else
            var uplayer := lookup.layers[i-1];
            uplayer.node.slots[uplayer.slot] == TreeDisk.Pointer(layer.addr)
}

function NodeRangeAtLayer(lookup:Lookup, i:int) : Range
    requires 0<=i<|lookup.layers|
{
    if i==0 then FULL_RANGE() else lookup.layers[i-1].slotRange
}

predicate LookupHonorsRanges(lookup:Lookup)
    requires LookupHasValidNodes(lookup)
    requires LookupHasValidSlotIndices(lookup)
{
    forall i :: 0<=i<|lookup.layers| ==>
        && var layer := lookup.layers[i];
        && RangeBoundForSlotIdx(layer.node, NodeRangeAtLayer(lookup, i), layer.slot) == layer.slotRange
}

predicate LookupMatchesCache(k:Constants, s:Variables, lookup:Lookup)
    requires WFLookup(k, lookup)
    requires LookupHasValidAddresses(k, lookup)
{
    forall i :: 0<=i<|lookup.layers| ==> (
        && var layer := lookup.layers[i];
        && var nba := lookup.tl.table[layer.addr];
        && nba.Used?
        && CachedNodeRead(k, s, nba, layer.node)
    )
}

predicate ValidLookup(k:Constants, s:Variables, lookup:Lookup)
{
    && WFLookup(k, lookup)
    && LookupHasValidNodes(lookup)
    && LookupHasValidSlotIndices(lookup)
    && LookupHasValidAddresses(k, lookup)
    && LookupHonorsPointerLinks(lookup)
    && LookupHonorsRanges(lookup)
    && KnowTable(k, s, lookup.tl)
    && LookupMatchesCache(k, s, lookup)
}

predicate SlotSatisfiesQuery(slot:Slot, datum:Datum)
{
    || (slot.Value? && slot.datum == datum)
    || (slot.Value? && slot.datum.key != datum.key && datum.value == EmptyValue())
    || (slot.Empty? && datum.value == EmptyValue())
}

// The slot to which this lookup leads.
function TerminalSlot(k:Constants, lookup:Lookup) : Slot
    requires WFLookup(k, lookup)
    requires LookupHasValidSlotIndices(lookup)
{
    var lastLayer := Last(lookup.layers);
    lastLayer.node.slots[lastLayer.slot]
}

predicate LookupSatisfiesQuery(k:Constants, s:Variables, lookup:Lookup, datum:Datum)
{
    && ValidLookup(k, s, lookup)
    && SlotSatisfiesQuery(TerminalSlot(k, lookup), datum)
}

predicate QueryAction(k:Constants, s:Variables, s':Variables, datum:Datum, lookup:Lookup)
{
    && s.ready
    && LookupSatisfiesQuery(k, s, lookup, datum)

    && s' == s
}

//////////////////////////////////////////////////////////////////////////////
// Mutations

function NodeReplaceSlot(node:Node, i:int, slot:Slot) : Node
    requires WFNode(node)
    requires 0<=i<|node.slots|
{
    TreeDisk.Node(node.pivots,
        node.slots[..i] + [slot] + node.slots[i+1..])
}

// Replace slot (which starts at pivots[slot-1]) with newSlots, subdivided by newPivots.
function NodeInsertSlots(node:Node, slot:int, newPivots:seq<Key>, newSlots:seq<Slot>) : Node
    requires WFNode(node)
    requires 0<=slot<|node.slots|
    requires |newSlots| == |newPivots| + 1
{
    TreeDisk.Node(
        node.pivots[..slot] + newPivots + node.pivots[slot..],
        node.slots[..slot] + newSlots + node.slots[slot+1..])
}


function ReplaceSlotForInsert(node:Node, idx:int, newDatum:Datum) : Node
    requires WFNode(node)
    requires ValidSlotIndex(node, idx)
    requires !node.slots[idx].Pointer?
{
    var slot := node.slots[idx];

    if slot.Empty? || newDatum.key == slot.datum.key
        // Replace an empty or same-key datum in place
    then NodeReplaceSlot(node, idx, TreeDisk.Value(newDatum))
    else if KeyLe(newDatum.key, slot.datum.key)
        // New datum goes to the left, so we'll split a pivot to the right with the old key
    then NodeInsertSlots(node, idx, [slot.datum.key], [TreeDisk.Value(newDatum), slot])
        // New datum goes to the right, so we'll split a pivot with the new key
    else NodeInsertSlots(node, idx, [newDatum.key], [slot, TreeDisk.Value(newDatum)])
}

predicate AllocateNBA(k:Constants, s:Variables, nba:NBA)
{
    && nba.Used?
    && true    // TODO
}

predicate AllocateAddr(k:Constants, s:Variables, childAddr:int)
{
    && 0 <= childAddr < k.tableEntries
    && true // TODO
}

function WriteNodeToCache(k:Constants, cache:Cache, nba:NBA, node:Node) : Cache
    requires nba.Used?
{
    cache[LbaForNba(k, nba) := CacheLine(TreeDisk.NodeSector(node), Dirty)]
}

datatype NodeEdit = NodeEdit(   // What you need to know to edit a slot of a node in the tree:
    lookup:Lookup,              // Path to the adjusted node, to prove that it belongs to the tree
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
predicate ApplyEdit(k:Constants, s:Variables, s':Variables, edit:NodeEdit, datum:Datum)
{
    && s.ready
    && LookupSatisfiesQuery(k, s, edit.lookup, datum)
    && AllocateNBA(k, s, edit.replacementNba)
    && WFTable(k, s.ephemeralTable)  // maintained as invariant

    && TreeDisk.Idle(k.disk, s.disk, s'.disk)
    && s'.cache == WriteNodeToCache(k, s.cache, edit.replacementNba, edit.replacementNode)
    // Through the magic of table indirection, lastLayer.node's child is suddenly switched to point to replacementNode.
    && s'.ephemeralTable == s.ephemeralTable[EditLast(edit).addr := edit.replacementNba]
    && s'.ready
}

predicate InsertAction(k:Constants, s:Variables, s':Variables, edit:NodeEdit, datum:Datum)
{
    && ApplyEdit(k, s, s', edit, datum)
    && edit.replacementNode == ReplaceSlotForInsert(EditLast(edit).node, EditLast(edit).slot, datum)
}

// Delete is un-insert.
predicate ReplacesSlotForDelete(oldNode:Node, newNode:Node, idx:int, deletedDatum:Datum)
{
    // Caller is 'existing' a newNode into being; we need to force it to satisfy the preconditions
    // for ChildEquivalentToSlotGroup.
    // (TODO We could just reduce things to this version, and accept the fact
    // that this check will duplicate what the invariant already does.)
    && WFNode(newNode)
    && ValidSlotIndex(newNode, idx)
    && !newNode.slots[idx].Pointer?
    && oldNode == ReplaceSlotForInsert(newNode, idx, deletedDatum)
}

predicate DeleteAction(k:Constants, s:Variables, s':Variables, edit:NodeEdit, datum:Datum)
{
    && ApplyEdit(k, s, s', edit, datum)
    && ReplacesSlotForDelete(EditLast(edit).node, edit.replacementNode, EditLast(edit).slot, datum)
}

predicate ChildEquivalentToSlotGroup(directNode:Node, replacedSlot:int, indirectNode:Node, childAddr:int, childNode:Node)
    requires WFNode(indirectNode)
    requires 0<=replacedSlot<|indirectNode.slots|
    requires |childNode.slots| == |childNode.pivots| + 1
{
    && directNode == NodeInsertSlots(indirectNode, replacedSlot, childNode.pivots, childNode.slots)
    && indirectNode.slots[replacedSlot] == TreeDisk.Pointer(childAddr)
}

predicate ChildEquivalentToSlotGroupForExpand(directNode:Node, replacedSlot:int, indirectNode:Node, childAddr:int, childNode:Node)
{
    // Caller is 'existing' an indirectNode into being; we need to force it to satisfy the preconditions
    // for ChildEquivalentToSlotGroup.
    // (TODO We could just reduce things to this version, and accept the fact
    // that this check will duplicate what the invariant already does.)
    && WFNode(indirectNode)
    && 0<=replacedSlot<|indirectNode.slots|
    && |childNode.slots| == |childNode.pivots| + 1
    && ChildEquivalentToSlotGroup(directNode, replacedSlot, indirectNode, childAddr, childNode)
}

// TODO you know what we need around here? The commit operation!

datatype Janitorial = Janitorial(
    edit:NodeEdit,              // The Lookup and edit info for the parent node being modified
    childAddr:int,              // table index where child is coming from or allocated to
    childNba:NBA,               // node address where child is coming from or allocated to
    childNode:Node,             // child node exchanging places with subrange of parent slots
    childNba':NBA               // the table reference for childAddr after the action
    )

predicate JanitorialAction(k:Constants, s:Variables, s':Variables, j:Janitorial)
    requires j.childNba.Used?
    requires ValidAddress(k, j.childAddr)
{
    && s.ready
    && ValidLookup(k, s, j.edit.lookup)
    && AllocateNBA(k, s, j.edit.replacementNba)
    && WFTable(k, s.ephemeralTable)  // maintained as invariant

    && TreeDisk.Idle(k.disk, s.disk, s'.disk)

    // The second write (j.childNba) "writes" the child to memory in the expand
    // case, and is a no-op in the contract case.
    && s'.cache == WriteNodeToCache(k,
                    WriteNodeToCache(k, s.cache, j.edit.replacementNba, j.edit.replacementNode),
                    j.childNba, j.childNode)

    // Through the magic of table indirection, lastLayer.node's parent is
    // suddenly switched to point to replacementNode.
    && s'.ephemeralTable ==
        s.ephemeralTable[EditLast(j.edit).addr := j.edit.replacementNba][j.childAddr := j.childNba']
    && s'.ready
}

predicate ExpandAction(k:Constants, s:Variables, s':Variables, j:Janitorial)
{
    && AllocateNBA(k, s, j.childNba)
    && AllocateAddr(k, s, j.childAddr)
    && JanitorialAction(k, s, s', j)
    && ChildEquivalentToSlotGroupForExpand(EditLast(j.edit).node, EditLast(j.edit).slot, j.edit.replacementNode, j.childAddr, j.childNode)
    && j.childNba' == j.childNba  // record the allocated reference
}

predicate ContractAction(k:Constants, s:Variables, s':Variables, j:Janitorial)
{
    && ValidAddress(k, j.childAddr)
    && WFTable(k, s.ephemeralTable)  // maintained as invariant
    && s.ephemeralTable[j.childAddr].Used?
    && j.childNba == s.ephemeralTable[j.childAddr]
    && JanitorialAction(k, s, s', j)
    && TreeDisk.Pointer(j.childAddr) == EditLast(j.edit).node.slots[EditLast(j.edit).slot]
    && CachedNodeRead(k, s, j.childNba, j.childNode)
    && ChildEquivalentToSlotGroup(j.edit.replacementNode, EditLast(j.edit).slot, EditLast(j.edit).node, j.childAddr, j.childNode)
    && j.childNba' == Unused  // free the child reference
}


// TODO trusted code
predicate CrashAction(k:Constants, s:Variables, s':Variables)
{
    && s'.disk == s.disk
    && s'.cache.Keys == {}
    // s'.ephemeralTable is unconstrained.
    && s'.ready == false
}

// You can make an ephemeral table ready to write
predicate RecoverAction(k:Constants, s:Variables, s':Variables, super:Sector, persistentTl:TableLookup)
{
    && !s.ready
    && KnowPersistentTableIndex(k, s, persistentTl.ti, super)
    && TreeDisk.WFTableIndex(persistentTl.ti)
    && KnowTable(k, s, persistentTl)

    && TreeDisk.Idle(k.disk, s.disk, s'.disk)
    && s'.cache == s.cache
    // we need to know the whole persistent table: the root ensures the
    // ephemeral tree state matches; the rest of the entries avoid incorrectly
    // marking unused sectors as allocated.
    && s'.ephemeralTable == persistentTl.table
    && s'.ready == true
}

// Bring a sector into the cache
predicate CacheFaultAction(k:Constants, s:Variables, s':Variables, lba:LBA, sector:Sector)
{
    && TreeDisk.Read(k.disk, s.disk, s'.disk, lba, sector)
    && s'.cache == s.cache[lba := CacheLine(sector, Clean)]
    && s'.ephemeralTable == s.ephemeralTable
    && s'.ready == s.ready
}

// It's okay to evict entries from the cache whenever.
predicate CacheEvictAction(k:Constants, s:Variables, s':Variables, lba:LBA)
{
    && TreeDisk.Idle(k.disk, s.disk, s'.disk)
    && s'.cache == MapRemove(s.cache, lba)
    && s'.ephemeralTable == s.ephemeralTable
    && s'.ready == s.ready
}

predicate InitTable(table:Table, rootNba:NBA)
{
    && 0 < |table|
    && table[ROOT_ADDR()] == rootNba
    && (forall addr :: 0 <= addr < |table| && addr != ROOT_ADDR()
        ==> table[addr].Unused?)
}

function {:opaque} EmptyView() : (view:View)
    ensures view.Keys == {}
{
    map l:LBA | l in {} :: TreeDisk.TableSector
}


function {:opaque} ViewOfDiskDef(k:TreeDisk.Constants, s:TreeDisk.Variables, lbaLimit:LBA) : (view:View)
    requires 0 <= lbaLimit <= |s.sectors|
    ensures forall lba :: TreeDisk.ValidLBA(k, lba) && lba < lbaLimit ==> lba in view && view[lba] == s.sectors[lba]
    decreases lbaLimit
{
    if lbaLimit == 0
    then EmptyView()
    else ViewOfDiskDef(k, s, lbaLimit-1)[lbaLimit-1 := s.sectors[lbaLimit-1]]
}

function ViewOfDisk(k:TreeDisk.Constants, s:TreeDisk.Variables) : (view:View)
    requires TreeDisk.WF(k, s)
    ensures forall lba :: TreeDisk.ValidLBA(k, lba) ==> lba in view && view[lba] == s.sectors[lba]
{
    ViewOfDiskDef(k, s, k.size)
}

datatype Mkfs = Mkfs(super:Sector, tl:TableLookup)

predicate DiskInMkfsState(k:Constants, s:Variables, mkfs:Mkfs)
{
    // right-sized disk
    && TreeDisk.Init(k.disk, s.disk)
    && k.disk.size == DiskSize(k)
    && TreeDisk.WF(k.disk, s.disk)
    && 0 < k.tableEntries

    // Empty persistent table
    && TreeDisk.WFTableIndex(mkfs.tl.ti)
    && PersistentTableIndexInView(ViewOfDisk(k.disk, s.disk), mkfs.tl.ti, mkfs.super)
    && TableInView(k, ViewOfDisk(k.disk, s.disk), mkfs.tl)
    // I arbitrarily demand that the root block be stored in node data sector 0.
    && InitTable(mkfs.tl.table, Used(0))
    && s.disk.sectors[LbaForNba(k, Used(0))] == TreeDisk.NodeSector(TreeDisk.Node([], [TreeDisk.Empty]))
}

predicate Init(k:Constants, s:Variables)
{
    && (exists mkfs :: DiskInMkfsState(k, s, mkfs))
    && s.cache.Keys == {}
    // No constraint on ephemeralTable, because we'll use !s.ready to force a RecoveryAction.
    && s.ready == false // We'll simply RecoverAction the initial disk.
}

} // module
