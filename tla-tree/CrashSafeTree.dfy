include "KVTypes.dfy"
include "Disk.dfy"

module TreeDisk refines Disk {
import opened KVTypes

// Every sector is either
// * Hot (in-use),
// * Warm (in an open set of warm sectors known to the superblock; allocated status
// subject to owner agreement; visited on fsck), or 
// * Cold (in a persistent free list of cold sectors).
datatype Child = Value(datum:Datum) | Pointer(lba:LBA) | Empty
// TODO consider breaking Node into a separate datatype so that path manipulations,
// which never talk about non-Nodes, can skip the .Node? tests.
datatype Sector =
      Superblock(firstCold:LBA, warm:set<LBA>, virgin:LBA)
    | ColdFreeList(next:LBA)
    | Node(parent:LBA, pivots:seq<Key>, children:seq<Child>)

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
type Sector = TreeDisk.Sector

// CRead == a "cached read"
datatype CRead = CRead(lba:LBA, sector:Sector)

datatype Constants = Constants(disk:TreeDisk.Constants)
datatype Variables = Variables(
    disk:TreeDisk.Variables,
    cache:map<LBA, TreeDisk.Sector>,

    // We don't REALLY need to track uncommittedFreeListHead in the spec; we COULD
    // exists a cache-observable chain into existence whenever we need it.
    uncommittedFreeListHead:LBA
    )

// The superblock lives at the beginning of the disk
function SUPERBLOCK_LBA() : LBA { 0 }

function ROOT_LBA() : LBA { 1 }

// 0 is a fine null LBA pointer, since we never need to point at the superblock.
function NULLPTR() : LBA { 0 }

predicate Init(k:Constants, s:Variables)
{
    && TreeDisk.Init(k.disk, s.disk)
    && TreeDisk.Peek(k.disk, s.disk, SUPERBLOCK_LBA(), TreeDisk.Superblock(NULLPTR(), {}, 2))
    && TreeDisk.Peek(k.disk, s.disk, ROOT_LBA(), TreeDisk.Node(NULLPTR(), [], [TreeDisk.Empty]))
    && s.cache.Keys == {}
}

// State predicate: we can read lba->sector out of the in-memory cache
predicate CachedRead(k:Constants, s:Variables, cread:CRead)
{
    && cread.lba in s.cache
    && s.cache[cread.lba] == cread.sector
}

// Partial action: Write a sector out, through the cache
predicate WriteThrough(k:Constants, s:Variables, s':Variables, lba:LBA, sector:Sector)
{
    && TreeDisk.Write(k.disk, s.disk, s'.disk, lba, sector)
    && s'.cache == s.cache[lba := sector]
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

predicate NodeDisownsChild(parent:Sector, childLba:LBA)
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
    cread:CRead, // this node
    idx:int,     // index of path[i+1].cread.lba in children[] 
    range:Range  // bounds for keys at this node
    )    

// If all of node's keys are bounded by nodeRange, then
// the keys in the i'th children of node are bounded by range.
function RangeBoundForChildIdx(node:Sector, nodeRange:Range, i:int) : (range:Range)
    requires node.Node?
    requires 0<=i<|node.children|
{
    Range(
        if i==0 then nodeRange.loinc else node.pivots[i-1],
        if i==|node.children|-1 then nodeRange.hiexc else node.pivots[i])
}

// True if every Node in path is live (committed) tree data.
// The caller cares about the last element.
predicate CachedPathRead(k:Constants, s:Variables, path:seq<PathElt>)
{
    && 0<|path|
    && path[0].cread.lba == ROOT_LBA()
    && forall i :: 0<=i<|path| ==> (
        var pElt := path[i];
        && CachedRead(k, s, pElt.cread)
        && i<|path|-1 ==> (
            && pElt.cread.sector.Node?   // TODO factor Node out of Sector
            && 0 <= pElt.idx < |pElt.cread.sector.children|
            && pElt.cread.sector.children[i] == TreeDisk.Pointer(path[i+1].cread.lba)
            )
        // Ranges next correctly
        && RangeBoundForChildIdx(pElt.cread.sector, pElt.range, pElt.idx) == path[i+1].range
        )

    && (forall i :: 0<=i<|path|-1 ==> !NodeDisownsChild(path[i].cread.sector, path[i+1].cread.lba))
}

predicate NodeIsLive(k:Constants, s:Variables, node:CRead)
{
    exists path:seq<PathElt> :: (
        && CachedPathRead(k, s, path)
        && Last(path).cread == node
    )
}

predicate NodeIsCold(k:Constants, s:Variables, nodeRead:CRead)
{
    && CachedRead(k, s, nodeRead)
    && !nodeRead.sector.Node?
}

// childLba is a Node that's not connected to the live tree.
// (This test isn't complete; a node connected to a disconnected ancestor will not satisfy
// this predicate. But it lets us always reuse a frontier of nodes.)
predicate NodeDisconnected(k:Constants, s:Variables, childRead:CRead)
{
    exists parentRead:CRead :: (
        // Child thinks it belongs to parent
        && CachedRead(k, s, childRead)
        && childRead.sector.Node?
        && childRead.sector.parent == parentRead.lba
        && (
            || (NodeIsLive(k, s, parentRead) && NodeDisownsChild(parentRead.sector, childRead.lba))
            || NodeIsCold(k, s, parentRead)
           )
    )
}


predicate CanAllocate(k:Constants, s:Variables, childRead:CRead)
{
    || NodeDisconnected(k, s, childRead)
    || NodeIsCold(k, s, childRead)
}

function ChildNodeForParentIdx(parentRead:CRead, i:int) : Sector
    requires 0<=i<|parentRead.sector.children|
{
    TreeDisk.Node(parentRead.lba, [], [parentRead.sector.children[i]])
}

// Create a new uncommitted child that thinks it belongs to parent, ready to replace children[i].
// We should check that this ensures KnowPrepared(s', ...)
// (Or we could WRITE this as KnowPrepared(k, s', ...) -- but that's harder to
// see as an implementation?)
predicate PrepareGrowAction(k:Constants, s:Variables, s':Variables, parentRead:CRead, i:int, childRead:CRead)
{
    && CachedRead(k, s, parentRead)
    && 0<=i<|parentRead.sector.children|
    && CanAllocate(k, s, childRead)
    && WriteThrough(k, s, s', childRead.lba, ChildNodeForParentIdx(parentRead, i))
}

predicate KnowPrepared(k:Constants, s:Variables, parentRead:CRead, i:int, childRead:CRead)
{
    && CachedRead(k, s, parentRead)
    && 0<=i<|parentRead.sector.children|
    && CachedRead(k, s, childRead)
    // Do we need to ensure child isn't hot? Well, obviously not if its parent pointer points
    // to parent, and there's a parent-child consistency invariant.
    && childRead.sector == ChildNodeForParentIdx(parentRead, i)
}

function SectorUpdateChild(parent:Sector, i:int, child:TreeDisk.Child) : Sector
    requires parent.Node?
{
    TreeDisk.Node(parent.parent, parent.pivots,
        parent.children[..i] + [child] + parent.children[i+1..])
}

predicate CommitGrowAction(k:Constants, s:Variables, s':Variables, parentRead:CRead, i:int, childRead:CRead)
{
    && KnowPrepared(k, s, parentRead, i, childRead)
    && WriteThrough(k, s, s', parentRead.lba, SectorUpdateChild(parentRead.sector, i,
        TreeDisk.Pointer(childRead.lba)))
}

predicate ContractNodeAction(k:Constants, s:Variables, s':Variables, parentRead:CRead, i:int, childRead:CRead)
{
    && NodeIsLive(k, s, parentRead)
    && CachedRead(k, s, childRead)
    && childRead.sector.Node?
    && childRead.sector.pivots == []    // child has one child, which can take its place in parent.
    && WriteThrough(k, s, s', parentRead.lba,
        SectorUpdateChild(parentRead.sector, i, childRead.sector.children[0]))
    // This write causes child to become free-by-unreachable. So child must be in committed warm set.
}

// There's a live path leading to node, and it supports range as a bound for node.
predicate LivePathBoundsChild(k:Constants, s:Variables, node:CRead, idx:int, range:Range)
{
    exists path : seq<PathElt> :: (
        && CachedPathRead(k, s, path)
        && Last(path).cread == node
        && Last(path).idx == idx
        && RangeBoundForChildIdx(Last(path).cread.sector, Last(path).range, Last(path).idx) == range
    )
}

predicate QueryAction(k:Constants, s:Variables, s':Variables, nodeRead:CRead, idx:int, range:Range, datum:Datum)
{
    var childRange := RangeBoundForChildIdx(nodeRead.sector, range, idx);
    && LivePathBoundsChild(k, s, nodeRead, idx, range)
    && RangeContains(range, datum.key)
    && var child := nodeRead.sector.children[idx]; (
        || (child.Value? && child.datum == datum)
        || (child.Value? && child.datum.key != datum.key && datum.value == EmptyValue())
        || (child.Empty? && datum.value == EmptyValue())
        )
}

// Insert newPivot at idx (shifting old pivot[idx] to the right).
// Replace child[idx] with newChildren.
// In practice, |newChildren|=2, and one of its elements is the old child[idx].
function SectorInsertChild(parent:Sector, idx:int, newPivot:Key, newChildren:seq<TreeDisk.Child>) : Sector
    requires parent.Node?
{
    TreeDisk.Node(parent.parent,
        parent.pivots[..idx] + [newPivot] + parent.pivots[idx..],
        parent.children[..idx] + newChildren + parent.children[idx+1..])
}
// newDatum.key is absent from the tree; insert it near a neighboring pivot
predicate InsertAction(k:Constants, s:Variables, s':Variables, newDatum:Datum)
{
    exists nodeRead:CRead, range:Range, idx:int :: (
        // Find a leaf that we can split.
        var childRange := RangeBoundForChildIdx(nodeRead.sector, range, idx);
        var extantChild := nodeRead.sector.children[idx];
        && LivePathBoundsChild(k, s, nodeRead, idx, range)
        && RangeContains(range, newDatum.key)
        && !extantChild.Pointer?
        // This is an insert, not a replace
        && if extantChild.Empty? || newDatum.key == extantChild.datum.key
                // Replace an empty or same-key datum in place
            then WriteThrough(k, s, s', nodeRead.lba,
                SectorUpdateChild(nodeRead.sector, idx, TreeDisk.Value(newDatum)))
            else if KeyLe(newDatum.key, extantChild.datum.key)
                // New datum goes to the left, so we'll split a pivot to the right with the old key
            then WriteThrough(k, s, s', nodeRead.lba,
                SectorInsertChild(nodeRead.sector, idx, extantChild.datum.key, [TreeDisk.Value(newDatum), extantChild]))
                // New datum goes to the right, so we'll split a pivot with the new key
            else WriteThrough(k, s, s', nodeRead.lba,
                SectorInsertChild(nodeRead.sector, idx, newDatum.key, [extantChild, TreeDisk.Value(newDatum)]))
    )
}

predicate DeleteAction(k:Constants, s:Variables, s':Variables, newDatum:Datum, nodeRead:CRead, idx:int, range:Range)
{
    && LivePathBoundsChild(k, s, nodeRead, idx, range)  // don't actually care about range
    && nodeRead.sector.children[idx] == TreeDisk.Value(newDatum)
    // Replace child with Empty. TODO background clean up of empty children where feasible.
    // (Contract cleans up small children.)
    && WriteThrough(k, s, s', nodeRead.lba,
        SectorUpdateChild(nodeRead.sector, idx, TreeDisk.Empty))
}

// Move an unreachable node onto an uncommitted free list
predicate MoveToFreeListAction(k:Constants, s:Variables, s':Variables, lba:LBA, childRead:CRead)
{
    && CachedRead(k, s, childRead)
    && NodeDisconnected(k, s, childRead)
    && WriteThrough(k, s, s', lba, TreeDisk.ColdFreeList(s.uncommittedFreeListHead))
    && s'.uncommittedFreeListHead == lba
}

predicate CommitFreeListAction(k:Constants, s:Variables, s':Variables, lba:LBA, super:CRead)
{
    && super.lba == SUPERBLOCK_LBA()
    && CachedRead(k, s, super)
    && WriteThrough(k, s, s', super.lba,
        TreeDisk.Superblock(s.uncommittedFreeListHead, super.sector.warm, super.sector.virgin))
}


} // module GrowableBlockStore
