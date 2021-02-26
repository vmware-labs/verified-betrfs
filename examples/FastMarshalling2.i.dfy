include "../lib/Lang/NativeTypes.s.dfy"
include "../lib/Lang/LinearSequence.i.dfy"

import opened NativeTypes
import opened LinearSequence_s
import opened LinearSequence_i

function interp_word(bs:seq<byte>) : (v:uint32)
    requires |bs| == 4

function as_word(bs:seq<byte>, offset:nat) : (v:uint32)
    requires 0 <= offset <= |bs|-4
    ensures v == interp_word(bs[offset..offset+4])

method extract_word(shared bs:seq<byte>, offset:nat) returns (v:uint32)
    requires 0 <= offset <= |bs|-4
    ensures v == as_word(bs, offset)

method replace_word(linear inout bs:seq<byte>, offset:nat, v:uint32) returns ()
    requires 0 <= offset <= |old_bs|-4
    ensures |bs| == |old_bs|
    ensures forall i | 0<=i<offset || offset+4<=i<|old_bs| :: bs[i]==old_bs[i]
    ensures as_word(bs, offset) == v;

/*
Given a seq of given length, you can extract a record from it.
A datatype is a sum record. First byte(?) tells size of the rest.
A constructor is a product record. Size may be variable, yes?

datatype Point = Point(x:uint32, y:uint32)
datatype Color = Red | Blue
datatype Path = Path(id:uint32, pts:seq<Point>, color:Color)

// I'd like to be able to say:
// var offset,length := pointerMath(
method extractPoint() returns (point: Point)

No this is all nonsense. To use partial-reads of big datatypes,
we really have to plan carefully what granularity of I/O we want to do,
not bake it into the marshalling framework.
*/

/*
So let's try to do something concrete.
We should really have a Node "interface":
    - one implemented by datatype Node
    - another implemented by a NodeView object that contains
        a NodeHeader
        and some pointers to buffers
        and has requireses that explain which methods you can call
            based on which buffers are available.
methods, then:
    getPivotTable() -- accessor
    getChildren() -- accessor. Maybe roll these together into getting a header object?
    getBucketHeader(i)
    getBucketMessageLocation(i, key)
    getBucketMessage(i, key)
...oh, we want to pull the indices for the buckets into the header block,
too.
    
datatype NodeHeader = NodeHeader(
    pivotTable:Pivots.PivotTable,
    children:Option<seq<BT.G.Reference>>,   // why option, vs empty list?
    bucketOffsets:seq<uint32>)
method size(o:NodeHeader) returns (size:uint32)

Should probably begin this conversation with just a Bucket for now.

VBucket.getNumPairs() : int
VBucket.getMessage(key: Key) : Option<Message>
    requires VBucket.offsetAvailable(VBucket.offsetForKey(key: Key))
VBucket.offsetForKey(key: Key)

*/

Okay, what would we do in C?

Space-optimal, preserving nesting:
struct Node {
    struct Index {
        // populated at load time by walking structures and counting up lengths
        PivotTable *pivotTable;
        ChildTable *childTable;
        BucketIndexTable *bucketIndexTable;
        BucketContentsTable *bucketContentsTable;
    } index[0];
    struct PivotTable {
        uint32 pivotCount;
        struct Pivot { Key key } pivots[];
    }
    struct ChildTable {
        uint32 childCount;
        struct Child { Reference ref } children[];
    }
    // We pretty much have to split the bucket data structure in half,
    // to keep the keys all together at the beginning.
    struct BucketIndexTable {
        uint32 bucketCount;
        struct BucketIndex {
            uint32 keyCount;
            Key keys[];
        } buckets[];
    }
    struct BucketContentsTable {
        uint32 bucketCount; // duplicates index info
        struct BucketContents {
            uint32 messageCount;  // duplicates index info
            Message messages[];
        } buckets[];
    }
}
and then we'd have a function that computes the (offset==0,size) of the first
load (everything except the bucket contents table), and another that computes
same for messages in BucketContentsTable.

Unmarshalling-optimal would marshall the offsets into the data structure so
they don't need to be computed after the read by summing lengths.
struct Node {
    struct Offsets {
        uint32 pivotTable;
        uint32 childTable;
        uint32 bucketIndexTable;
        uint32 bucketContentsTable;
    }
    struct PivotTable {
        uint32 pivotCount;  // could be computed from offsets, but why?
        struct Pivot { Key key } pivots[];
    }
    struct ChildTable {
        uint32 childCount;  // could be computed from offsets, but why?
        struct Child { Reference ref } children[];
    }
    // We pretty much have to split the bucket data structure in half,
    // to keep the keys all together at the beginning.
    struct BucketIndexTable {
        uint32 bucketCount;
        struct BucketIndex {
            uint32 keyCount;
            uint32 bucketContentsOffset;    // offset from Node* to struct BucketContents
            Key keys[];
        } buckets[];
    }
    struct BucketContentsTable {
        uint32 bucketCount; // duplicates index info, and not actually used.
        struct BucketContents {
            uint32 messageCount;  // duplicates index info, and not actually used.
            Message messages[];
        } buckets[];
    }
}

findMessage(Node* node, Key* key) {
    // All this stuff can be looked up if the Node "header" section is
    // all available.
    PivotTable* pivotTable = (((void*) node) + node.offsets.pivotIndexTable);
    BucketIndexTable* bucketIndexTable =
        (BucketIndexTable*) (((void*) node) + node.offsets.bucketIndexTable);
    BucketContentsTable* bucketContentsTable =
        (BucketContentsTable*) (((void*) node) + node.offsets.bucketContentsTable);

    bucketNum = pivotTable.findBucket(key);
    // ignore child lookup for now; it can be done from the header.

    BucketIndex* bi = bucketIndexTable.buckets[bucketNum];
    // This thing does a binary search using keys[],
    // then uses bucketContentsOffset to pointer-math (offset, size)
    // of desired Message*.
    DataAddress messageAddress = bi->getMessagePointer(key);

    // May span multiple pages. This function checks if the pages we need
    // are cached; if not, it does an IO to fetch them.
    cache->pageIn(messageAddress);

    // NOTE: What's the cache architecture for the Node index sections?
    // If they're bigger than a page, we have a contiguity problem.
    // One possibly-simple strategy: allocate node indices as a different
    // page size at disk-allocation-time. Eww.
    // Splinter strategy (everything fits in 4k) starting to look pretty sweet.

    // Copy the message out, to deal with possible crossing of a noncontiguous
    // page boundary.
    Message message = messageAddress.extract(cache);
    return message;
}

Can we let the cache just fault stuff in? OS cache probably does clever
prefetching if we're scanning, whereas we'd turn a scan into seek-synchronous
IO party. Or have a heuristic for when to fault the whole Node in?

something more ultra-integrated: A node is:
    {
        structured stuff that's guaranteed to fit in a page
        bucket counts
        pivot range
        offset to key array
        offset to message array
    }
    { key array } indexed into by pivot table, bucket tables
    { message array } indexed into by bucket tables

So a PivotView would know how to peek into one of these clever backing store
thingies, as would a BucketView.

So we'd do:
findMessage(Node* integ, Key* key) {
    Ans<uint32> bucketIdxAns = PivotView(cache, integ).findBucket(key);
    // tries to bin-search the pivot table
    if bucketIdxAns.fault? {
        cache.fault(bucketIdxAns.faultReq);
        return;
    }

    Ans<Message> msgAns = BucketView(cache, integ, bucketIdxAns.value).findMessage(key);
    // Tries to bin-search the bucket keys, which get sorted near the
    // beginning to maximize chance of colocating with other searches.
    // Then tries to retrieve the message.
    if msgAns.fault? {
        cache.fault(msgAns.faultReq);
        return;
    }
    // if it works, it copies out the Message (to deal with contiguity).
    return msgAns.value;
}

Ans<Message> BucketView.findMessage()
{
    // binsearch proceeds with Ans<Key> key
    produces message idnex
}
