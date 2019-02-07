include "KVTypes.dfy"
include "Disk.dfy"

module TreeDisk refines Disk {
//export reveals Child, Node, Sector
import opened KVTypes

// Every sector is either
// * Hot (in-use),
// * Warm (in an open set of warm sectors known to the superblock; allocated status
// subject to owner agreement; visited on fsck), or 
// * Cold (in a persistent free list of cold sectors).
datatype Child = Value(datum:Datum) | Pointer(lba:LBA) | Empty
datatype Node = Node(parent:LBA, pivots:seq<Key>, children:seq<Child>)
datatype Sector =
      Superblock(firstCold:LBA, warm:set<LBA>, virgin:LBA)
    | ColdFreeList(next:LBA)
    | NodeSector(node:Node)

} // module TreeDisk

module CrashSafeTree {
import opened KVTypes
import TreeDisk

function Last<T>(s:seq<T>) : T  // TODO move to library
    requires 0<|s|
{
    s[|s|-1]
}

type LBA = TreeDisk.LBA
type Child = TreeDisk.Child
type Sector = TreeDisk.Sector
type Node = TreeDisk.Node

// NRead == a "cached read" of a node
datatype NRead = NRead(lba:LBA, node:Node)

datatype Constants = Constants(disk:TreeDisk.Constants)
datatype Variables = Variables(
    disk:TreeDisk.Variables,
    cache:map<LBA, Sector>,

    // We don't REALLY need to track uncommittedFreeListHead in the spec; we COULD
    // exists a cache-observable chain into existence whenever we need it.
    uncommittedFreeListHead:LBA
    )

// The superblock lives at the beginning of the disk
function SUPERBLOCK_LBA() : LBA { 0 }

function ROOT_LBA() : LBA { 1 }

// 0 is a fine null LBA pointer, since we never need to point at the superblock.
function NULLPTR() : LBA { 0 }

predicate WFNode(node:Node) {
    |node.pivots| == |node.children| - 1
}

predicate Init(k:Constants, s:Variables)
{
    && TreeDisk.Init(k.disk, s.disk)
    && 2 <= k.disk.size // Disk has room for at least superblock and root
    && TreeDisk.Peek(k.disk, s.disk, SUPERBLOCK_LBA(), TreeDisk.Superblock(NULLPTR(), {}, 2))
    && TreeDisk.Peek(k.disk, s.disk, ROOT_LBA(),
        TreeDisk.NodeSector(TreeDisk.Node(NULLPTR(), [], [TreeDisk.Empty])))
    && s.cache.Keys == {}
}

// State predicate: we can read lba->sector out of the in-memory cache
predicate CachedSectorRead(k:Constants, s:Variables, lba:LBA, sector:Sector)
{
    && lba in s.cache
    && s.cache[lba] == sector
}

predicate CachedNodeRead(k:Constants, s:Variables, nread:NRead)
{
    && CachedSectorRead(k, s, nread.lba, TreeDisk.NodeSector(nread.node))
    // We toss WFNode in here to keep other expressions tidy; as with any WF, this can
    // create a liveness problem (can't read that disk sector with a malformed node).
    // Even if we don't prove liveness, we can mitigate that concern by including a
    // WF invariant.
    && WFNode(nread.node)
}

// Partial action: Write a sector out, through the cache
predicate WriteThroughSector(k:Constants, s:Variables, s':Variables, lba:LBA, sector:Sector)
{
    && TreeDisk.Write(k.disk, s.disk, s'.disk, lba, sector)
    && s'.cache == s.cache[lba := sector]
}

predicate WriteThroughNode(k:Constants, s:Variables, s':Variables, lba:LBA, node:Node)
{
    WriteThroughSector(k, s, s', lba, TreeDisk.NodeSector(node))
}

// Bring a sector into the cache
predicate CacheFaultAction(k:Constants, s:Variables, s':Variables, lba:LBA, sector:Sector)
{
    && TreeDisk.Read(k.disk, s.disk, s'.disk, lba, sector)
    && s'.cache == s.cache[lba := sector]
}

function {:opaque} MapRemove<K,V>(m:map<K,V>, k:K) : (m':map<K,V>)
    ensures m'.Keys == m.Keys - {k}
    ensures forall j :: j in m' ==> m'[j] == m[j]
{
    map j | j in m && j != k :: m[j]
}

// It's okay to evict entries from the cache whenever.
predicate CacheEvictAction(k:Constants, s:Variables, s':Variables, lba:LBA)
{
    && TreeDisk.Idle(k.disk, s.disk, s'.disk)
    && s'.cache == MapRemove(s.cache, lba)
}

predicate NodeDisownsChild(parent:Node, childLba:LBA)
{
    forall idx :: 0<=idx<|parent.children| ==> parent.children[idx] != TreeDisk.Pointer(childLba)
}

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

datatype PathElt = PathElt(
    nread:NRead, // this node
    idx:int,     // index of path[i+1].nread.lba in children[] 
    range:Range  // bounds for keys at this node
    )    

predicate ValidChildIndex(node:Node, idx:int)
{
     0 <= idx < |node.children|
}

// If all of node's keys are bounded by nodeRange, then
// the keys in the i'th children of node are bounded by range.
function RangeBoundForChildIdx(node:Node, nodeRange:Range, i:int) : (range:Range)
    requires WFNode(node)
    requires ValidChildIndex(node, i)
{
    Range(
        if i==0 then nodeRange.loinc else node.pivots[i-1],
        if i==|node.children|-1 then nodeRange.hiexc else node.pivots[i])
}

// All of the nodes in the path are as read out of the cache (we didn't just make them up).
predicate PathIsCached(k:Constants, s:Variables, path:seq<PathElt>)
{
    forall i :: 0<=i<|path| ==> CachedNodeRead(k, s, path[i].nread)
}

predicate PathHasValidChildIndices(k:Constants, s:Variables, path:seq<PathElt>)
{
    forall i :: 0<=i<|path| ==> (
        var pElt := path[i];
        && ValidChildIndex(pElt.nread.node, pElt.idx)
    )
}

// All of the node pairs in the path reflect a parent-child link given at the
// path element's index in the parent.
predicate PathLinksChildren(k:Constants, s:Variables, path:seq<PathElt>)
    requires PathHasValidChildIndices(k, s, path)
{
    forall i :: 0<=i<|path|-1 ==> (
        var pElt := path[i];
        && pElt.nread.node.children[pElt.idx] == TreeDisk.Pointer(path[i+1].nread.lba)
    )
}

// The ranges noted in the pathElts reflect the ranges imposed by the parent's
// range and pivots
predicate PathNestsRanges(k:Constants, s:Variables, path:seq<PathElt>)
    requires PathIsCached(k, s, path)
    requires PathHasValidChildIndices(k, s, path)
{
    forall i :: 0<=i<|path|-1 ==> (
        var pElt := path[i];
        assert ValidChildIndex(pElt.nread.node, pElt.idx);
        && RangeBoundForChildIdx(pElt.nread.node, pElt.range, pElt.idx) == path[i+1].range)
}

// True if every Node in path is live (committed) tree data.
// The caller cares about the last element.
predicate CachedPathRead(k:Constants, s:Variables, path:seq<PathElt>)
{
    && 0<|path|
    && path[0].nread.lba == ROOT_LBA()
    && PathIsCached(k, s, path)
    && PathHasValidChildIndices(k, s, path)
    && PathLinksChildren(k, s, path)
    && PathNestsRanges(k, s, path)
}

predicate NodeIsLive(k:Constants, s:Variables, node:NRead)
{
    exists path:seq<PathElt> :: (
        && CachedPathRead(k, s, path)
        && Last(path).nread == node
    )
}

predicate NodeIsCold(k:Constants, s:Variables, lba:LBA, sector:Sector)
{
    && CachedSectorRead(k, s, lba, sector)
    && !sector.NodeSector?
}

// childLba is a Node that's not connected to the live tree.
// (This test isn't complete; a node connected to a disconnected ancestor will not satisfy
// this predicate. But it lets us always reuse a frontier of nodes.)
predicate NodeDisconnected(k:Constants, s:Variables, childRead:NRead)
{
    exists parentRead:NRead :: (
        // Child thinks it belongs to parent
        && CachedNodeRead(k, s, childRead)
        && childRead.node.parent == parentRead.lba
        && (
            || (NodeIsLive(k, s, parentRead) && NodeDisownsChild(parentRead.node, childRead.lba))
            || NodeIsCold(k, s, parentRead.lba, TreeDisk.NodeSector(parentRead.node))
           )
    )
}


predicate CanAllocate(k:Constants, s:Variables, childRead:NRead)
{
    || NodeDisconnected(k, s, childRead)
    || NodeIsCold(k, s, childRead.lba, TreeDisk.NodeSector(childRead.node))
}

function ChildNodeForParentIdx(parentRead:NRead, i:int) : Node
    requires 0<=i<|parentRead.node.children|
{
    TreeDisk.Node(parentRead.lba, [], [parentRead.node.children[i]])
}

// Create a new uncommitted child that thinks it belongs to parent, ready to replace children[i].
// We should check that this ensures KnowPrepared(s', ...)
// (Or we could WRITE this as KnowPrepared(k, s', ...) -- but that's harder to
// see as an implementation?)
predicate PrepareGrowAction(k:Constants, s:Variables, s':Variables, parentRead:NRead, i:int, childRead:NRead)
{
    && CachedNodeRead(k, s, parentRead)
    && 0<=i<|parentRead.node.children|
    && CanAllocate(k, s, childRead)
    && WriteThroughNode(k, s, s', childRead.lba, ChildNodeForParentIdx(parentRead, i))
}

predicate KnowPrepared(k:Constants, s:Variables, parentRead:NRead, i:int, childRead:NRead)
{
    && CachedNodeRead(k, s, parentRead)
    && 0<=i<|parentRead.node.children|
    && CachedNodeRead(k, s, childRead)
    // Do we need to ensure child isn't hot? Well, obviously not if its parent pointer points
    // to parent, and there's a parent-child consistency invariant.
    && childRead.node == ChildNodeForParentIdx(parentRead, i)
}

function SectorUpdateChild(parent:Node, i:int, child:Child) : Node
    requires 0<=i<|parent.children|
{
    TreeDisk.Node(parent.parent, parent.pivots,
        parent.children[..i] + [child] + parent.children[i+1..])
}

predicate CommitGrowAction(k:Constants, s:Variables, s':Variables, parentRead:NRead, i:int, childRead:NRead)
{
    && KnowPrepared(k, s, parentRead, i, childRead)
    && WriteThroughNode(k, s, s', parentRead.lba, SectorUpdateChild(parentRead.node, i,
        TreeDisk.Pointer(childRead.lba)))
}

predicate ContractNodeAction(k:Constants, s:Variables, s':Variables, parentRead:NRead, i:int, childRead:NRead)
{
    && NodeIsLive(k, s, parentRead)
    && CachedNodeRead(k, s, childRead)
    && childRead.node.pivots == []    // child has one child, which can take its place in parent.
    && 0<=i<|parentRead.node.children|
    && WriteThroughNode(k, s, s', parentRead.lba,
        SectorUpdateChild(parentRead.node, i, childRead.node.children[0]))
    // This write causes child to become free-by-unreachable. So child must be in committed warm set.
}

// The witnesses to a path lookup
datatype PathLookup = PathLookup(node:Node, idx:int, range:Range, path:seq<PathElt>)

function LastElt(lookup:PathLookup) : PathElt
    requires 0<|lookup.path|
{
    Last(lookup.path)
}


// There's a live path leading to node, and it supports range as a bound for node.
predicate LivePathBoundsChild(k:Constants, s:Variables, lookup:PathLookup)
{
    && CachedPathRead(k, s, lookup.path)
    && LastElt(lookup).nread.node == lookup.node
    && LastElt(lookup).idx == lookup.idx
    && PathHasValidChildIndices(k, s, lookup.path)
    && RangeBoundForChildIdx(LastElt(lookup).nread.node, LastElt(lookup).range, LastElt(lookup).idx) == lookup.range
}

// Assuming the child covers the range of datum...
predicate ChildSatisfiesQuery(child:Child, datum:Datum)
{
    || (child.Value? && child.datum == datum)
    || (child.Value? && child.datum.key != datum.key && datum.value == EmptyValue())
    || (child.Empty? && datum.value == EmptyValue())
}

predicate QueryAction(k:Constants, s:Variables, s':Variables, datum:Datum, lookup:PathLookup)
{
    && WFNode(lookup.node)
    && ValidChildIndex(lookup.node, lookup.idx)
    && var childRange := RangeBoundForChildIdx(lookup.node, lookup.range, lookup.idx);
    && LivePathBoundsChild(k, s, lookup)
    && RangeContains(lookup.range, datum.key)
    && ChildSatisfiesQuery(lookup.node.children[lookup.idx], datum)

    && TreeDisk.Idle(k.disk, s.disk, s'.disk)
    && s'.cache == s.cache
    && s'.uncommittedFreeListHead == s.uncommittedFreeListHead
}

// Insert newPivot at idx (shifting old pivot[idx] to the right).
// Replace child[idx] with newChildren.
// In practice, |newChildren|=2, and one of its elements is the old child[idx].
function SectorInsertChild(parent:Node, idx:int, newPivot:Key, newChildren:seq<Child>) : Node
    requires WFNode(parent)
    requires 0<=idx<|parent.children|
{
    TreeDisk.Node(parent.parent,
        parent.pivots[..idx] + [newPivot] + parent.pivots[idx..],
        parent.children[..idx] + newChildren + parent.children[idx+1..])
}
// newDatum.key is absent from the tree; insert it near a neighboring pivot
predicate InsertAction(k:Constants, s:Variables, s':Variables, newDatum:Datum, lookup:PathLookup)
{
    // Find a leaf that we can split.
    && WFNode(lookup.node)
    && ValidChildIndex(lookup.node, lookup.idx)
    && var childRange := RangeBoundForChildIdx(lookup.node, lookup.range, lookup.idx);
    && var extantChild := lookup.node.children[lookup.idx];
    && LivePathBoundsChild(k, s, lookup)
    && RangeContains(lookup.range, newDatum.key)
    && !extantChild.Pointer?
    && var nodeLba := LastElt(lookup).nread.lba;
    // This is an insert, not a replace
    && if extantChild.Empty? || newDatum.key == extantChild.datum.key
            // Replace an empty or same-key datum in place
        then WriteThroughNode(k, s, s', nodeLba,
            SectorUpdateChild(lookup.node, lookup.idx, TreeDisk.Value(newDatum)))
        else if KeyLe(newDatum.key, extantChild.datum.key)
            // New datum goes to the left, so we'll split a pivot to the right with the old key
        then WriteThroughNode(k, s, s', nodeLba,
            SectorInsertChild(lookup.node, lookup.idx, extantChild.datum.key, [TreeDisk.Value(newDatum), extantChild]))
            // New datum goes to the right, so we'll split a pivot with the new key
        else WriteThroughNode(k, s, s', nodeLba,
            SectorInsertChild(lookup.node, lookup.idx, newDatum.key, [extantChild, TreeDisk.Value(newDatum)]))
}

predicate DeleteAction(k:Constants, s:Variables, s':Variables, newDatum:Datum, lookup:PathLookup)
{
    && LivePathBoundsChild(k, s, lookup)
    && lookup.node.children[lookup.idx] == TreeDisk.Value(newDatum)
    // Replace child with Empty.
    // TODO background clean up of empty children within a node where feasible.
    // (Contract action already cleans up small children.)
    && WriteThroughNode(k, s, s', LastElt(lookup).nread.lba,
        SectorUpdateChild(lookup.node, lookup.idx, TreeDisk.Empty))
}

// Move an unreachable node onto an uncommitted free list
predicate MoveToFreeListAction(k:Constants, s:Variables, s':Variables, lba:LBA, childRead:NRead)
{
    && CachedNodeRead(k, s, childRead)
    && NodeDisconnected(k, s, childRead)
    && WriteThroughSector(k, s, s', lba, TreeDisk.ColdFreeList(s.uncommittedFreeListHead))
    && s'.uncommittedFreeListHead == lba
}

predicate CommitFreeListAction(k:Constants, s:Variables, s':Variables, super:Sector)
{
    && CachedSectorRead(k, s, SUPERBLOCK_LBA(), super)
    && super.Superblock?
    && WriteThroughSector(k, s, s', SUPERBLOCK_LBA(),
        TreeDisk.Superblock(s.uncommittedFreeListHead, super.warm, super.virgin))
}

datatype Step =
      CacheFaultActionStep(lba:LBA, sector:Sector)
    | CacheEvictActionStep(lba:LBA)
    | PrepareGrowActionStep(parentRead:NRead, i:int, childRead:NRead)
    | CommitGrowActionStep(parentRead:NRead, i:int, childRead:NRead)
    | ContractNodeActionStep(parentRead:NRead, i:int, childRead:NRead)
    | QueryActionStep(datum:Datum, lookup:PathLookup)
    | InsertActionStep(datum:Datum, lookup:PathLookup)
    | DeleteActionStep(datum:Datum, lookup:PathLookup)
    | MoveToFreeListActionStep(lba:LBA, childRead:NRead)
    | CommitFreeListActionStep(super:Sector)

predicate NextStep(k:Constants, s:Variables, s':Variables, step:Step)
{
    match step {
        case CacheFaultActionStep(lba, sector) => CacheFaultAction(k, s, s', lba, sector)
        case CacheEvictActionStep(lba) => CacheEvictAction(k, s, s', lba)
        case PrepareGrowActionStep(parentRead, i, childRead) => PrepareGrowAction(k, s, s', parentRead, i, childRead)
        case CommitGrowActionStep(parentRead, i, childRead) => CommitGrowAction(k, s, s', parentRead, i, childRead)
        case ContractNodeActionStep(parentRead, i, childRead) => ContractNodeAction(k, s, s', parentRead, i, childRead)
        case QueryActionStep(datum, lookup) => QueryAction(k, s, s', datum, lookup)
        case InsertActionStep(datum, lookup) => InsertAction(k, s, s', datum, lookup)
        case DeleteActionStep(datum, lookup) => DeleteAction(k, s, s', datum, lookup)
        case MoveToFreeListActionStep(lba, childRead) => MoveToFreeListAction(k, s, s', lba, childRead)
        case CommitFreeListActionStep(super) => CommitFreeListAction(k, s, s', super)
    }
}

predicate Next(k:Constants, s:Variables, s':Variables)
{
    exists step:Step :: NextStep(k, s, s', step)
}


} // module GrowableBlockStore
