include "../lib/Lang/NativeTypes.s.dfy"
include "../lib/Lang/LinearSequence.i.dfy"
include "../lib/MarshalledAccessors.i.dfy"

// Can we rely on a global invariant that LBAs contain the type of
// block expected of them by references to them?

// Also, references are accounted at allocation-unit granularity,
// not IO/unit granularity. Are we changing how we do the indirection
// table, now that it's got 64X the number of entries? I guess not yet;
// we'll leave the allocation unit big for now.

datatype TrunkNode {
  pivots: seq<Key>,
  children: seq<LBA>,
  branches: seq<LBA>
}

predicate WFTrunkNode(n:TrunkNode) {
  |n.pivots| + 1 == |n.children| == |n.branches|
}

datatype BranchIndexNode {
  pivots: seq<Key>,
  children: seq<LBA>
}

predicate WFBranchIndexNode(n:BranchIndexNode) {
  |n.pivots| + 1 == |n.children|
}

datatype BranchLeafNode {
  pivots: seq<Key>,
  messages: seq<Message>
}

predicate WFBranchLeafNode(n:BranchLeafNode) {
  |n.pivots| + 1 == |n.messageschildren|
}

datatype Block = TrunkNodeBlock(t:TrunkNode) | BranchIndexNodeBlock(b:BranchIndexNode) | BranchLeafNodeBlock(l:BranchLeafNode)

datatype ReadOp = ReadOp(ref:LBA, block:Block)

type BtreeLayer = ReadOp
type BtreeLookup = seq<BtreeLayer>
datatype Layer = Layer(trunk: ReadOp, btree: BtreeLookup)
type Lookup = seq<Layer>

predicate WFBtreeLookup(bl: BtreeLookup) {
    && |bl| > 0
    && Last(bl).block.BranchLeafNodeBlock?
    && (forall i | 0<=i<|bl|-1 :: bl[i].block.BranchIndexNodeBlock?)
    // the triggery part we gotta hide
    && (forall i | 0<=i<|bl|-1 ::
        var slot := FindSlot(bl[i].block.b.pivots);
        && bl[i].block.b.children[slot] == bl[i+1].ref)
}

predicate WFLookup(l: Lookup) {
    && |l|>0
    && Last(l)
}

// And then I guess the impl is the first place where we use Marshalled*
// versions of these data structures. We argue that we have a Lookup by
// defending the Blocks they support.
