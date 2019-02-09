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

datatype NBA = Unused | Used(lba:LBA)  // A Node Block Address gets offset into the node-sectors region of the disk.

type Table = seq<NBA>   // An indirection table mapping addresses (indices into the table) to NBAs

datatype Constants = Constants(
    disk:TreeDisk.Constants,
    tableEntries:int,    // How many entries in the table (allocatable data blocks on the disk)
    tableSectors:int     // How many sectors to set aside for each indirection table
    )

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
    cache:View,
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
{
    && SectorInView(s.cache, LbaForNba(k, nba), TreeDisk.NodeSector(node))
    // We toss WFNode in here to keep other expressions tidy; as with any WF, this can
    // create a liveness problem (can't read that disk sector with a malformed node).
    // Even if we don't prove liveness, we can mitigate that concern by including a
    // WF invariant.
    && WFNode(node)
}

predicate KnowTable(k:Constants, s:Variables, tl:TableLookup)
    requires TreeDisk.WFTableIndex(tl.ti)
{
    TableInView(k, s.cache, tl)
}

predicate KnowPersistentTableIndex(k:Constants, s:Variables, ti:TableIndex, super:Sector)
{
    PersistentTableIndexInView(s.cache, ti, super)
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

predicate LookupHasValidLayers(k:Constants, lookup:Lookup)
{
    forall i :: 0<=i<|lookup.layers| ==>
        && var layer := lookup.layers[i];
        && 0 <= layer.addr < k.tableEntries
        && ValidSlotIndex(layer.node, layer.slot)
}

predicate LookupHonorsPointerLinks(lookup:Lookup)
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
{
    forall i :: 0<=i<|lookup.layers| ==>
        && var layer := lookup.layers[i];
        && RangeBoundForSlotIdx(layer.node, NodeRangeAtLayer(lookup, i), layer.slot) == layer.slotRange
}

predicate LookupMatchesCache(k:Constants, s:Variables, lookup:Lookup)
    requires LookupHasValidLayers(k, lookup)
{
    forall i :: 0<=i<|lookup.layers| ==>
        && var layer := lookup.layers[i];
        && CachedNodeRead(k, s, lookup.tl.table[layer.addr], layer.node)
}

predicate ValidLookup(k:Constants, s:Variables, lookup:Lookup)
{
    && LookupHasValidLayers(k, lookup)
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
function TerminalSlot(lookup:Lookup) : Slot
{
    var lastLayer := Last(lookup.layers);
    lastLayer.node.slots[lastLayer.slot]
}

predicate LookupSatisfiesQuery(k:Constants, s:Variables, lookup:Lookup, datum:Datum)
{
    && ValidLookup(k, s, lookup)
    && SlotSatisfiesQuery(TerminalSlot(lookup), datum)
}

predicate QueryAction(k:Constants, s:Variables, s':Variables, datum:Datum, lookup:Lookup)
{
    && s.ready
    && LookupSatisfiesQuery(k, s, lookup, datum)

    && s' == s
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
    && s'.cache == s.cache[lba := sector]
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

datatype Mkfs = Mkfs(super:Sector, tl:TableLookup)

predicate InitTable(table:Table, rootNba:NBA)
{
    && table[ROOT_ADDR()] == rootNba
    && (forall addr :: 0 <= addr < |table| && addr != ROOT_ADDR()
        ==> table[addr].Unused?)
}

function {:opaque} EmptyView() : (view:View)
    ensures view.Keys == {}
{
    var view:View :| view.Keys == {}; view
}


function {:opaque} ViewOfDiskDef(k:TreeDisk.Constants, s:TreeDisk.Variables, lbaLimit:LBA) : (view:View)
    ensures forall lba :: TreeDisk.ValidLBA(k, lba) && lba < lbaLimit ==> lba in view && view[lba] == s.sectors[lba]
{
    if lbaLimit == 0
    then EmptyView()
    else ViewOfDiskDef(k, s, lbaLimit-1)[lbaLimit-1 := s.sectors[lbaLimit-1]]
}

function ViewOfDisk(k:TreeDisk.Constants, s:TreeDisk.Variables) : (view:View)
    ensures forall lba :: TreeDisk.ValidLBA(k, lba) ==> lba in view && view[lba] == s.sectors[lba]
{
    ViewOfDiskDef(k, s, k.size)
}

predicate DiskInMkfsState(k:Constants, s:Variables, mkfs:Mkfs)
{
    // right-sized disk
    && TreeDisk.Init(k.disk, s.disk)
    && k.disk.size == DiskSize(k)

    // Empty persistent table
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
