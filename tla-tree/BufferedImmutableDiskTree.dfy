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

datatype Message = Insert(value:Value) | Delete
type Buffer = map<Key, Message>
datatype Slot = Pointer(addr:TableAddress) | Empty
datatype Header = Header(pivots:seq<Key>, slots:seq<Slot>)
datatype Node = Node(header:Header, buffers:seq<Buffer>)

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

module ImmutableDiskTree {
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
    disk:TreeDisk.Constants,
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

function DiskHeaderSize(k:Constants) : int
{
    1                       // one superblock
    + 2*k.tableSectors      // two indirection tables
}

function DiskSize(k:Constants) : int
{
    DiskHeaderSize(k)
    + k.tableEntries        // and a bunch of rewritable data sectors
}

predicate ValidNba(k:Constants, nba:NBA)
{
    && nba.Used?
    && 0 <= nba.nidx < DiskSize(k) - DiskHeaderSize(k)
}

function LbaForNba(k:Constants, nba:NBA) : LBA
    requires ValidNba(k, nba)
{
    DiskHeaderSize(k) + nba.nidx
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
  && |node.header.pivots| == |node.header.slots| - 1
  && |node.buffers| == |node.header.slots|
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
    && TreeDisk.ValidLBA(k.disk, start)
    && TreeDisk.ValidLBA(k.disk, start+count-1)
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

predicate CachedNodeRead(k:Constants, s:Variables, nba:NBA, node:Node)
    requires ValidNba(k, nba)
{
    && SectorInView(ViewOfCache(s.cache), LbaForNba(k, nba), TreeDisk.NodeSector(node))
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
     0 <= idx < |node.header.slots|
}

// If all of node's keys are bounded by nodeRange, then
// the keys in the i'th slot of node are bounded by range.
function RangeBoundForSlotIdx(node:Node, nodeRange:Range, idx:int) : (range:Range)
    requires WFNode(node)
    requires ValidSlotIndex(node, idx)
{
    Range(
        if idx==0 then nodeRange.loinc else node.header.pivots[idx-1],
        if idx==|node.header.slots|-1 then nodeRange.hiexc else node.header.pivots[idx])
}

//////////////////////////////////////////////////////////////////////////////
// Lookup
datatype Layer = Layer(
    addr:TableAddress,
    node:Node,          // the node at the addr
    slot:int,           // the slot pointing to the next node below
    slotRange:Range     // the range that bounds this slot (and hence the node below)
    )

datatype Lookup = Lookup(layers:seq<Layer>)

predicate WFLookup(k:Constants, lookup:Lookup)
{
    0 < |lookup.layers|
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
            uplayer.node.header.slots[uplayer.slot] == Pointer(layer.addr)
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
    requires WFTable(k, s.ephemeralTable)
    requires LookupHasValidAddresses(k, lookup)
{
    forall i :: 0<=i<|lookup.layers| ==> (
        && var layer := lookup.layers[i];
        && var nba := TableAt(k, s.ephemeralTable, layer.addr);
        && ValidNba(k, nba)
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
    && WFTable(k, s.ephemeralTable)
    && LookupMatchesCache(k, s, lookup)
}

predicate BufferSatisfiesQuery(buffer:Buffer, datum:Datum)
{
  datum.key in buffer && 
    match buffer[datum.key] {
      case Delete => datum.value == EmptyValue()
        // XXX we should enforce that you can't have an insert of EmptyValue().
        // Or get rid of EmptyValue() altogether.
      case Insert(v) => v == datum.value
    }
}

predicate BufferDoesNotDefineKey(buffer:Buffer, key:Key)
{
  key !in buffer
}

predicate LookupReachesDeadEnd(k:Constants, lookup:Lookup)
  requires WFLookup(k, lookup)
{
  var lastlevel := Last(lookup.layers);
  && ValidSlotIndex(lastlevel.node, lastlevel.slot)
  && lastlevel.node.header.slots[lastlevel.slot].Empty?
}

// predicate SlotSatisfiesQuery(slot:Slot, datum:Datum)
// {
//     || (slot.Value? && slot.datum == datum)
//     || (slot.Value? && slot.datum.key != datum.key && datum.value == EmptyValue())
//     || (slot.Empty? && datum.value == EmptyValue())
// }

// // The slot to which this lookup leads.
// function TerminalSlot(k:Constants, lookup:Lookup) : Slot
//     requires WFLookup(k, lookup)
//     requires LookupHasValidSlotIndices(lookup)
// {
//     var lastLayer := Last(lookup.layers);
//     lastLayer.node.slots[lastLayer.slot]
// }

predicate LookupFollowsQueryPath(k:Constants, s:Variables, lookup:Lookup, key:Key)
{
    && ValidLookup(k, s, lookup)
      // && SlotSatisfiesQuery(TerminalSlot(k, lookup), datum)
    && RangeContains(Last(lookup.layers).slotRange, key)
}

predicate LookupDoesNotPassKey(k:Constants, s:Variables, lookup:Lookup, key:Key)
{
    && ValidLookup(k, s, lookup)
    && (forall i :: 0 <= i < |lookup.layers| - 1 ==>
       BufferDoesNotDefineKey(lookup.layers[i].node.buffers[lookup.layers[i].slot], key))  
}

predicate LookupSatisfiesQuery(k:Constants, s:Variables, lookup:Lookup, datum:Datum)
{
    && ValidLookup(k, s, lookup)
      // && SlotSatisfiesQuery(TerminalSlot(k, lookup), datum)
    && LookupFollowsQueryPath(k, s, lookup, datum.key)
    && LookupDoesNotPassKey(k, s, lookup, datum.key)
    && (var last := Last(lookup.layers);
       || BufferSatisfiesQuery(last.node.buffers[last.slot], datum)
       || (
          && BufferDoesNotDefineKey(last.node.buffers[last.slot], datum.key)
          && LookupReachesDeadEnd(k, lookup)
          && datum.value == EmptyValue()
         )
      ) 
}

predicate QueryAction(k:Constants, s:Variables, s':Variables, lookup:Lookup, datum:Datum)
{
    && s.ready
    && LookupSatisfiesQuery(k, s, lookup, datum)

    && s' == s
}

//////////////////////////////////////////////////////////////////////////////
// Mutations

function BufferAddMessage(buffer:Buffer, key:Key, msg:Message) : Buffer
{
  buffer[key := msg]
}

function NodeAddMessage(node:Node, slotIndex:int, key:Key, msg:Message) : Node
  requires WFNode(node)
  requires ValidSlotIndex(node, slotIndex)
{
  Node(node.header, node.buffers[slotIndex := BufferAddMessage(node.buffers[slotIndex], key, msg)])
}

function NodeReplaceSlot(node:Node, i:int, slot:Slot) : Node
    requires WFNode(node)
    requires 0<=i<|node.header.slots|
{
  Node(
    Header(
      node.header.pivots,
      node.header.slots[..i] + [slot] + node.header.slots[i+1..]),
    node.buffers)
}

// Replace slot (which starts at pivots[slot-1]) with newSlots, subdivided by newPivots.
function NodeReplaceSlotWithSlotSequence(node:Node, slot:int,
  newPivots:seq<Key>, newSlots:seq<Slot>, newBuffers:seq<Buffer>) : Node
    requires WFNode(node)
    requires 0<=slot<|node.header.slots|
    requires |newSlots| == |newPivots| + 1
    requires |newBuffers| == |newSlots|
{
  Node(
    Header(
      node.header.pivots[..slot] + newPivots + node.header.pivots[slot..],
      node.header.slots[..slot] + newSlots + node.header.slots[slot+1..]),
    node.buffers[..slot] + newBuffers + node.buffers[slot+1..])
}


// function ReplaceSlotForInsert(node:Node, slotIdx:int, newDatum:Datum) : Node
//     requires WFNode(node)
//     requires ValidSlotIndex(node, slotIdx)
//     requires !node.slots[slotIdx].Pointer?
// {
//     var slot := node.slots[slotIdx];

//     if slot.Empty? || newDatum.key == slot.datum.key
//         // Replace an empty or same-key datum in place
//     then NodeReplaceSlot(node, slotIdx, Value(newDatum))
//     else if KeyLe(newDatum.key, slot.datum.key)
//         // New datum goes to the left, so we'll split a pivot to the right with the old key
//     then NodeReplaceSlotWithSlotSequence(node, slotIdx, [slot.datum.key], [Value(newDatum), slot])
//         // New datum goes to the right, so we'll split a pivot with the new key
//     else NodeReplaceSlotWithSlotSequence(node, slotIdx, [newDatum.key], [slot, Value(newDatum)])
// }

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
predicate AddMessage(k:Constants, s:Variables, s':Variables, edit:NodeEdit, key:Key, msg:Message)
    requires WFConstants(k)
{
    && s.ready
    && WFVariables(k, s)
    && LookupFollowsQueryPath(k, s, edit.lookup, key)
    && LookupDoesNotPassKey(k, s, edit.lookup, key)
    && AllocateNBA(k, s, edit.replacementNba, edit.tableLookup)

    && TreeDisk.Idle(k.disk, s.disk, s'.disk)
    && s'.cache == WriteNodeToCache(k, s.cache, edit.replacementNba, edit.replacementNode)
    // Through the magic of table indirection, lastLayer.node's child is suddenly switched to point to replacementNode.
    && s'.ephemeralTable == s.ephemeralTable[EditLast(edit).addr.a := edit.replacementNba]
    && s'.ready
}

predicate InsertAction(k:Constants, s:Variables, s':Variables, edit:NodeEdit, datum:Datum)
    requires WFConstants(k)
{
    && AddMessage(k, s, s', edit, datum.key, Insert(datum.value))
    && edit.replacementNode == NodeAddMessage(EditLast(edit).node, EditLast(edit).slot, datum.key, Insert(datum.value))
    // ReplaceSlotForInsert(EditLast(edit).node, EditLast(edit).slot, datum)
}

// // Delete is un-insert.
// predicate ReplacesSlotForDelete(oldNode:Node, newNode:Node, slotIdx:int, deletedDatum:Datum)
// {
//     // Caller is 'existing' a newNode into being; we need to force it to satisfy the preconditions
//     // for ChildEquivalentToSlotGroup.
//     // (TODO We could just reduce things to this version, and accept the fact
//     // that this check will duplicate what the invariant already does.)
//     && WFNode(newNode)
//     && ValidSlotIndex(newNode, slotIdx)
//     && !newNode.slots[slotIdx].Pointer?
//     // TODO this could make up an "old" value that got inserted-over.
//     && oldNode == ReplaceSlotForInsert(newNode, slotIdx, deletedDatum)
// }

predicate DeleteAction(k:Constants, s:Variables, s':Variables, edit:NodeEdit, datum:Datum)
    requires WFConstants(k)
{
    && AddMessage(k, s, s', edit, datum.key, Delete)
    && edit.replacementNode == NodeAddMessage(EditLast(edit).node, EditLast(edit).slot, datum.key, Delete)
}

datatype Janitorial = Janitorial(
    edit:NodeEdit,              // The Lookup and edit info for the parent node being modified
    childAddr:TableAddress,     // table index where child is coming from or allocated to
    childNba:NBA,               // node address where child is coming from or allocated to
    childNode:Node,             // child node exchanging places with subrange of parent slots
    childEntry':NBA             // what becomes of the table reference for childAddr after the action
    )

predicate ChildEquivalentToSlotGroup(directNode:Node, replacedSlot:int, indirectNode:Node, childAddr:TableAddress, childNode:Node)
    requires WFNode(indirectNode)
    requires 0<=replacedSlot<|indirectNode.header.slots|
    requires |childNode.header.slots| == |childNode.header.pivots| + 1
    requires |childNode.buffers| == |childNode.header.slots|
{
    && directNode == NodeReplaceSlotWithSlotSequence(indirectNode, replacedSlot, childNode.header.pivots, childNode.header.slots, childNode.buffers)
    && indirectNode.header.slots[replacedSlot] == Pointer(childAddr)
}

predicate ChildEquivalentToSlotGroupForExpand(directNode:Node, replacedSlot:int, indirectNode:Node, childAddr:TableAddress, childNode:Node)
{
    // Caller is 'existing' an indirectNode into being; we need to force it to satisfy the preconditions
    // for ChildEquivalentToSlotGroup.
    // (TODO We could just reduce things to this version, and accept the fact
    // that this check will duplicate what the invariant already does.)
    && WFNode(indirectNode)
    && 0<=replacedSlot<|indirectNode.header.slots|
    && WFNode(childNode)
    && ChildEquivalentToSlotGroup(directNode, replacedSlot, indirectNode, childAddr, childNode)
}

// TODO consider breaking these weird abstract action-helpers into
// enabling-condition & update parts to make caller read more imperatively.
predicate JanitorialAction(k:Constants, s:Variables, s':Variables, j:Janitorial)
    requires WFConstants(k)
    requires j.childNba.Used?
    requires ValidAddress(k, j.childAddr)
{
    && s.ready
    && WFVariables(k, s)
    && ValidLookup(k, s, j.edit.lookup)
    && AllocateNBA(k, s, j.edit.replacementNba, j.edit.tableLookup)
    && ValidNba(k, j.childNba)

    && TreeDisk.Idle(k.disk, s.disk, s'.disk)

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

predicate ExpandAction(k:Constants, s:Variables, s':Variables, j:Janitorial)
    requires WFConstants(k)
{
    && WFTable(k, s.ephemeralTable)
    && AllocateNBA(k, s, j.childNba, j.edit.tableLookup)
    && AllocateAddr(k, s, j.childAddr)
    && JanitorialAction(k, s, s', j)
    && ChildEquivalentToSlotGroupForExpand(EditLast(j.edit).node, EditLast(j.edit).slot, j.edit.replacementNode, j.childAddr, j.childNode)
    && j.childEntry' == j.childNba  // record the allocated reference
}

predicate ContractAction(k:Constants, s:Variables, s':Variables, j:Janitorial)
    requires WFConstants(k)
{
    && WFVariables(k, s)
    && ValidAddress(k, j.childAddr)
    && TableAt(k, s.ephemeralTable, j.childAddr).Used?
    && j.childNba == TableAt(k, s.ephemeralTable, j.childAddr)
    && JanitorialAction(k, s, s', j)
    && Pointer(j.childAddr) == EditLast(j.edit).node.header.slots[EditLast(j.edit).slot]
    && CachedNodeRead(k, s, j.childNba, j.childNode)
    && ChildEquivalentToSlotGroup(j.edit.replacementNode, EditLast(j.edit).slot, EditLast(j.edit).node, j.childAddr, j.childNode)
    && j.childEntry' == Unused  // free the child reference
}

predicate WriteCore(k:Constants, s:Variables, s':Variables, lba:LBA, sector:Sector)
{
    && s.ready

    && TreeDisk.Write(k.disk, s.disk, s'.disk, lba, sector)
    && s'.cache == s.cache[lba := CacheLine(sector, Clean)]
    && s'.ephemeralTable == s.ephemeralTable
    && s'.ready == true
}

// It's always okay to write back cached sectors, whenever we feel like it,
// except: we can't write back the superblock pointer; that's a Commit.
predicate WriteBackAction(k:Constants, s:Variables, s':Variables, lba:LBA)
{
    && 1 <= lba < DiskSize(k)
    && lba in s.cache
    && s.cache[lba].state.Dirty?    // performance spec: don't write clean things back. :v)
    && WriteCore(k, s, s', lba, s.cache[lba].sector)
}

// Dirty a sector that stores the ephemeral table.
predicate EmitTableAction(k:Constants, s:Variables, s':Variables, persistentTi:TableIndex, super:Sector, tblSectorIdx:int)
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
    
    && TreeDisk.Idle(k.disk, s.disk, s'.disk)
    && s'.cache == WriteSectorToCache(k, s'.cache, lba, sector)
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
predicate CommitAction(k:Constants, s:Variables, s':Variables, persistentTi:TableIndex, super:Sector)
{
    && s.ready
    && KnowPersistentTableIndex(k, s, persistentTi, super)
    && var ephemeralTi := OppositeTableIndex(persistentTi);
    // TODO and need to Know the Ephemeral Table
    && var newSuper := TreeDisk.Superblock(ephemeralTi);
    && CacheIsClean(s.cache)

    // Write the new superblock THROUGH the cache. Everything in the cache stays clean.
    && WriteCore(k, s, s', SUPERBLOCK_LBA(), newSuper)
    // TODO unchanged everything else
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
    requires WFConstants(k)
{
    && !s.ready
    && KnowPersistentTableIndex(k, s, persistentTl.ti, super)
    && WFTableIndex(persistentTl.ti)
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

predicate InitTable(k:Constants, table:Table, rootNba:NBA)
{
    && 0 < |table|
    && WFTable(k, table)
    && TableAt(k, table, ROOT_ADDR()) == rootNba
    && (forall addr:TableAddress :: 0 <= addr.a < |table| && addr != ROOT_ADDR()
        ==> TableAt(k, table, addr).Unused?)
}

function {:opaque} EmptyView() : (view:View)
    ensures view.Keys == {}
{
    map l:LBA | l in {} :: TreeDisk.TableSector
}


function {:opaque} ViewOfDiskDef(k:TreeDisk.Constants, s:TreeDisk.Variables, lbaLimit:LBA) : (view:View)
    requires TreeDisk.WF(k, s)  // to bind |s.sectors| to k.size
    requires 0 <= lbaLimit <= |s.sectors|
    ensures forall lba :: lba in view <==> (0 <= lba < lbaLimit && TreeDisk.ValidLBA(k, lba))
    ensures forall lba :: TreeDisk.ValidLBA(k, lba) && 0 <= lba < lbaLimit ==> view[lba] == s.sectors[lba]
    decreases lbaLimit
{
    if lbaLimit == 0
    then EmptyView()
    else ViewOfDiskDef(k, s, lbaLimit-1)[lbaLimit-1 := s.sectors[lbaLimit-1]]
}

function ViewLbaThroughCache(k:Constants, s:Variables, lba:LBA) : Sector
    requires TreeDisk.WF(k.disk, s.disk)
    requires TreeDisk.ValidLBA(k.disk, lba)
{
    if lba in s.cache
    then s.cache[lba].sector
    else s.disk.sectors[lba]
}

function {:opaque} ViewThroughCacheDef(k:Constants, s:Variables, lbaLimit:LBA) : (view:View)
    requires TreeDisk.WF(k.disk, s.disk)  // to bind |s.disk.sectors| to k.size
    requires 0 <= lbaLimit <= |s.disk.sectors|
    ensures forall lba :: lba in view <==> (0 <= lba < lbaLimit && TreeDisk.ValidLBA(k.disk, lba))
    ensures forall lba :: TreeDisk.ValidLBA(k.disk, lba) && 0 <= lba < lbaLimit ==> view[lba] == ViewLbaThroughCache(k, s, lba)
    decreases lbaLimit
{
    if lbaLimit == 0
    then EmptyView()
    else ViewThroughCacheDef(k, s, lbaLimit-1)[lbaLimit-1 := ViewLbaThroughCache(k, s, lbaLimit-1)]
}

predicate FullViewDisk(k:TreeDisk.Constants, view:View)
{
    forall lba :: TreeDisk.ValidLBA(k, lba) <==> lba in view
}

predicate FullView(k:Constants, view:View) // more usable by adding DiskSize
{
    && k.disk.size == DiskSize(k)
    && FullViewDisk(k.disk, view)
}

function ViewOfDisk(k:TreeDisk.Constants, s:TreeDisk.Variables) : (view:View)
    requires TreeDisk.WF(k, s)
    ensures FullViewDisk(k, view)
    ensures forall lba :: TreeDisk.ValidLBA(k, lba) ==> view[lba] == s.sectors[lba]
{
    ViewOfDiskDef(k, s, k.size)
}

function ViewThroughCache(k:Constants, s:Variables) : (view:View)
    requires TreeDisk.WF(k.disk, s.disk)
    ensures FullViewDisk(k.disk, view)
    ensures forall lba :: TreeDisk.ValidLBA(k.disk, lba) ==> view[lba] == ViewLbaThroughCache(k, s, lba)
{
    ViewThroughCacheDef(k, s, k.disk.size)
}

datatype Mkfs = Mkfs(super:Sector, tl:TableLookup)

// Constraints on just the configuration (Constants)
predicate PlausibleDiskSize(k:Constants)
{
    && k.disk.size == DiskSize(k)
    && 0 < k.tableSectors
    && 0 < k.tableEntries
}

// Plausible, and the sectors map is correctly sized.
predicate ValidDiskSize(k:Constants, s:Variables)
{
    && PlausibleDiskSize(k)
    && TreeDisk.WF(k.disk, s.disk)
}

predicate DiskInMkfsState(k:Constants, s:Variables, mkfs:Mkfs)
{
    // right-sized disk
    && TreeDisk.Init(k.disk, s.disk)
    && ValidDiskSize(k, s)
    && 0 < k.tableEntries

    // Empty persistent table
    && WFTableIndex(mkfs.tl.ti)
    && PersistentTableIndexInView(ViewOfDisk(k.disk, s.disk), mkfs.tl.ti, mkfs.super)
    && TableInView(k, ViewOfDisk(k.disk, s.disk), mkfs.tl)
    // I arbitrarily demand that the root block be stored in node data sector 0.
    && InitTable(k, mkfs.tl.table, Used(0))
    && s.disk.sectors[LbaForNba(k, Used(0))] == TreeDisk.NodeSector(Node(Header([], [Empty]), [map[]]))
}

predicate Init(k:Constants, s:Variables)
{
    && (exists mkfs :: DiskInMkfsState(k, s, mkfs))
    && s.cache.Keys == {}
    // No constraint on ephemeralTable, because we'll use !s.ready to force a RecoveryAction.
    && s.ready == false // We'll simply RecoverAction the initial disk.
}

datatype Step =
    | QueryActionStep(lookup:Lookup, datum:Datum)
    | InsertActionStep(edit:NodeEdit, datum:Datum)
    | DeleteActionStep(edit:NodeEdit, datum:Datum)
    | ExpandActionStep(j:Janitorial)
    | ContractActionStep(j:Janitorial)
    | WriteBackActionStep(lba:LBA)
    | EmitTableActionStep(persistentTi:TableIndex, super:Sector, tblSectorIdx:int)
    | CommitActionStep(persistentTi:TableIndex, super:Sector)
    | CrashActionStep
    | RecoverActionStep(super:Sector, persistentTl:TableLookup)
    | CacheFaultActionStep(lba:LBA, sector:Sector)
    | CacheEvictActionStep(lba:LBA)

predicate NextStep(k:Constants, s:Variables, s':Variables, step:Step)
    requires WFConstants(k)
{
    match step {
        case  QueryActionStep(lookup, datum) => QueryAction(k, s, s', lookup, datum)
        case  InsertActionStep(edit, datum) => InsertAction(k, s, s', edit, datum)
        case  DeleteActionStep(edit, datum) => DeleteAction(k, s, s', edit, datum)
        case  ExpandActionStep(j) => ExpandAction(k, s, s', j)
        case  ContractActionStep(j) => ContractAction(k, s, s', j)
        case  WriteBackActionStep(lba) => WriteBackAction(k, s, s', lba)
        case  EmitTableActionStep(persistentTi, super, tblSectorIdx)
                => EmitTableAction(k, s, s', persistentTi, super, tblSectorIdx)
        case  CommitActionStep(persistentTi, super) => CommitAction(k, s, s', persistentTi, super)
        case  CrashActionStep => CrashAction(k, s, s')
        case  RecoverActionStep(super, persistentTl) => RecoverAction(k, s, s', super, persistentTl)
        case  CacheFaultActionStep(lba, sector) => CacheFaultAction(k, s, s', lba, sector)
        case  CacheEvictActionStep(lba) => CacheEvictAction(k, s, s', lba)
    }
}
    
predicate {:opaque} Next(k:Constants, s:Variables, s':Variables)
    requires WFConstants(k)
{
    exists step :: NextStep(k, s, s', step)
}

} // module
