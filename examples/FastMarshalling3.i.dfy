include "../lib/Lang/NativeTypes.s.dfy"
include "../lib/Lang/LinearSequence.i.dfy"
include "../lib/MarshalledAccessors.i.dfy"

method findPivotIdx(mnode: MarshalledNode, key:Key) returns (idx:nat)
{
    return binarySearch(mnode.pivots(), key);
}

method findChildRef(mnode: MarshalledNode, key:Key)
{
    var idx := findPivotIndex(mnode, key);
    var mChildTable := mnode.childTable();
    var childRef := mChildTable.Element(idx);
    return childRef;
}

method findMessage(mnode: MarshalledNode, key:Key) returns Option<Message>
{
    var idx := findPivotIndex(mnode, key);
    var mKeyTable := mnode.keyTable();
    var keyIdx := binarySearch(mnode.pivots(), key);
    if mKeyTable.Element(keyIdx) != key {
        return None
    }
    var mValueTable := mnode.valueTable();
    var ...now we're back to trying to assemble pieces. I like Rob's idea
    of going with the Splinter tables.
    var childRef := mChildTable.Element(idx);
}

method LookupExample()
{
    // TODO we need a way for a MarshalledNode to work even if it can
    // only see a subset of the data!
    var nodePrefixData := Read(nodeStartAddress, 4096);
    var mnode := MarshalledNode(nodePrefixData, 0);
}
