datatype Color = Red | Black
datatype Node = Nil | Node(left: Node, value: int, right: Node, color: Color)

// This function encodes "all leaves (NIL) are black"
function method ColorOf(node: Node) : Color {
    if node.Nil?
    then
        Black
    else
        node.color
}

predicate RedNodesHaveBlackChildren(tree: Node) {
    tree.Node? ==> (
        (tree.color.Red? ==>
            ColorOf(tree.left).Black?  && ColorOf(tree.right).Black?)
        && RedNodesHaveBlackChildren(tree.left)
        && RedNodesHaveBlackChildren(tree.right)
    )
}

function SubtreeBlackCount(tree: Node, k: int) : int {
    if ColorOf(tree).Black? then k - 1 else k
}


// There is some k such that all paths from tree root to leaves have k
// blacks.
predicate BlackCountOnAllPaths(tree: Node, k: int) {
    if tree.Nil?
    then
        k == 1
    else
        var expected := SubtreeBlackCount(tree, k);
           BlackCountOnAllPaths(tree.left, expected)
        && BlackCountOnAllPaths(tree.right, expected)
}

// This exists is going to eventually cause trouble and need to be opaqued
// kc is "black count" -- the number of blacks on any root-leaf path.
predicate RedBlackInv(tree: Node, kc: int) {
       RedNodesHaveBlackChildren(tree)
    && BlackCountOnAllPaths(tree, kc)
}

function method Contents(tree: Node) : multiset<int>
{
    if tree.Nil?
    then multiset{}
    else
        Contents(tree.left) + Contents(tree.right) + multiset{tree.value}
}

predicate ValueIsOrdered(value: int, side: Side, pivot: int)
{
    if side.Left? then value <= pivot else value >= pivot
}

// The not-recursive that the set of elements on the left (resp) is on
// the correct side of the pivot.
predicate SideIsOrdered(subtree: Node, side: Side, pivot: int)
{
    forall x :: x in Contents(subtree) ==> ValueIsOrdered(x, side, pivot)
}

// The recursive promise that the ordering structure re-appears at each
// layer below.
predicate OrderedTree(tree: Node) {
    tree.Nil?
    || (
           SideIsOrdered(tree.left, Left, tree.value)
        && SideIsOrdered(tree.right, Right, tree.value)
        && OrderedTree(tree.left)
        && OrderedTree(tree.right)
        )
}

predicate RBTree(tree: Node, kc: int) {
    OrderedTree(tree) && RedBlackInv(tree, kc)
}

lemma RBTreeNil(tree: Node)
    requires tree.Nil?;
    ensures RBTree(tree, 1);
{
    assert BlackCountOnAllPaths(tree, 1);
}

lemma RBTreeRecursion(tree: Node, kc: int)
    requires RBTree(tree, kc);
    requires tree.Node?;
    ensures RBTree(tree.left, SubtreeBlackCount(tree, kc));
    ensures RBTree(tree.right, SubtreeBlackCount(tree, kc));
{
    //assert BlackCountOnAllPaths(tree.left, SubtreeBlackCount(tree, kc));
    //assert BlackCountOnAllPaths(tree.right, SubtreeBlackCount(tree, kc));
    // TODO: Not sure this lemma is needed any longer.
}

datatype Side = Left | Right

function method child(tree: Node, side: Side) : Node
    requires tree.Node?;
{
    if side.Left? then tree.left else tree.right
}

function method opposite(side: Side) : Side
{
    if side.Left? then Right else Left
}

datatype Option<T> = None | Some(t: T)

method RotateRight(a: Node, ghost kc: int) returns (b: Node)
    requires RBTree(a, kc);
    requires !a.Nil? && !a.left.Nil?;
    ensures !b.Nil?;
    ensures Contents(a) == Contents(b);
{
    var l := a.left;
    var r := Node(l.right, a.value, a.right, Black);

    // Dafny needs help realizing why everything in r is right of l.value;
    // it needs me to point out that l.value < a.value.
    forall x | x in Contents(r) 
        ensures l.value <= x;
    {
        assert OrderedTree(l);
        assert l.value in Contents(a.left);
        // Think about the cases, Dafny! (In particular, expand Contents).
        if x in Contents(r.left) {
        } else if x in Contents(r.right) {
        } else if x in multiset{r.value} {
        }
    }
    // A similar property that r.left (l.right) is left of r.value, because
    // it was left of a.value in the precondition.
    forall x | x in Contents(r.left)
        ensures x <= r.value;
    {
        assert x in Contents(a.left);
    }

    b := Node(l.left, l.value, r, Black);
}

method RotateLeft(a: Node, ghost kc: int) returns (b: Node)
    requires RBTree(a, kc);
    requires !a.Nil? && !a.right.Nil?;
    ensures !b.Nil?;
    ensures Contents(a) == Contents(b);
{
    assume false;
}


// Rotation without color change.
method WologRotate(direction: Side, a: Node, ghost kc: int) returns (b: Node)
    requires RBTree(a, kc);
    requires !a.Nil? && !child(a, opposite(direction)).Nil?;
    ensures Contents(a) == Contents(b);
{
    if direction.Left? {
        b := RotateLeft(a, kc);
    } else {
        b := RotateRight(a, kc);
    }
}

function method redOnRedViolation(tree: Node) : Option<Side>
{
    if !ColorOf(tree).Red? then
        None
    else if ColorOf(tree.left).Red? then
        Some(Left)
    else if ColorOf(tree.right).Red? then
        Some(Right)
    else
        None
}

function method WologNode(side: Side, t1: Node, t2: Node, value: int, color: Color) : Node
{
    if side.Left?
    then Node(t1, value, t2, color)
    else Node(t2, value, t1, color)
}

predicate BlackDepthGrowsInCase3(b:Node, kc: int, kcbchild: int) {
    kcbchild == if ColorOf(b).Red? && b.left.Node? && ColorOf(b.left).Black? then kc + 1 else kc
}

predicate MostlyRBTree(tree:Node, kc: int, value: int, b: Node)
    // The properties provided by 'inner' invocations of Insert -- *almost*
    // a red-black tree, except we allow a single red-red violation at
    // the root.
{
       OrderedTree(b)
    && !b.Nil?
    && RedNodesHaveBlackChildren(b.left)
    && RedNodesHaveBlackChildren(b.right)
    && Contents(b) == Contents(tree) + multiset{value}
    && BlackCountOnAllPaths(b, kc)
    && (redOnRedViolation(b).Some? ==> ColorOf(tree).Red?)
       // Allow at most one red-on-red violation (a black uncle)
    && (ColorOf(b).Red? ==> ColorOf(b.left).Black? || ColorOf(b.right).Black?)
}

method RepairCase3Recolor(tree: Node, ghost kc: int, value: int, changedSide: Side, changedSubtree: Node) returns (b: Node)
    requires tree.Node?;
    requires tree.color.Black?;
    requires RBTree(tree, kc);
    requires changedSubtree.Node?;
    requires ColorOf(changedSubtree).Red?;
    requires ColorOf(child(tree, opposite(changedSide))).Red?;  // uncle is red
    requires ValueIsOrdered(value, changedSide, tree.value);
    requires MostlyRBTree(child(tree, changedSide), SubtreeBlackCount(tree, kc), value, changedSubtree);
    ensures MostlyRBTree(tree, kc, value, b);
{
    var stableSide := opposite(changedSide);
    var stableSubtree := child(tree, stableSide);

    var recoloredChanged := Node(changedSubtree.left,
        changedSubtree.value, changedSubtree.right, Black);
    var newStable := Node(stableSubtree.left,
        stableSubtree.value, stableSubtree.right, Black);
    b := WologNode(changedSide, recoloredChanged, newStable, tree.value, Red);
    assert RedNodesHaveBlackChildren(child(tree, stableSide));  //observe
    ghost var ekc := SubtreeBlackCount(tree, kc);
    assert BlackCountOnAllPaths(stableSubtree, ekc);    // observe
    assert OrderedTree(stableSubtree);  // observe
}

method RepairCase4pt1RotateOutside(childTree: Node, ghost kcc: int, value: int, changedTree: Node, changedSide: Side) returns (rotated: Node)
    requires RBTree(childTree, kcc);
    requires MostlyRBTree(childTree, kcc, value, changedTree);
    requires ColorOf(childTree).Red?;
    requires ColorOf(child(childTree, changedSide)).Red?;
    ensures MostlyRBTree(childTree, kcc, value, rotated);
{
    assert ColorOf(childTree).Red?;
    var stableSide := opposite(changedSide);
    var sub1 := child(childTree, stableSide);
    var inner := child(childTree, changedSide);
    assert ColorOf(inner).Red?;
    var sub2 := child(inner, stableSide);
    var sub3 := child(inner, changedSide);

    var outer := WologNode(changedSide, sub1, sub2, changedTree.value, Red);
    rotated := WologNode(changedSide, outer, sub3, inner.value, Red);
}

lemma BlackCountInheritance(t: Node, kcc: int)
    requires ColorOf(t).Red?;
    requires BlackCountOnAllPaths(child(t, Left), kcc);
    requires BlackCountOnAllPaths(child(t, Right), kcc);
    ensures BlackCountOnAllPaths(t, kcc);
{
}

method RepairCase4pt2RotateUp(tree: Node, ghost kc: int, value:int, changedSide: Side,
    changedSubtree: Node) returns (b: Node)
    requires RBTree(tree, kc);
    requires tree.Node?;
    requires ColorOf(changedSubtree).Red?;
    requires ColorOf(child(tree, opposite(changedSide))).Black?;
    requires ColorOf(child(changedSubtree, changedSide)).Red?;
    // Stable grandchild didn't change.
    requires child(tree, changedSide).Node?;
    requires child(changedSubtree, opposite(changedSide))
        == child(child(tree, changedSide), opposite(changedSide));
    requires MostlyRBTree(child(tree, changedSide), kc, value, changedSubtree);
    ensures MostlyRBTree(tree, kc, value, b);
{
    ghost var origSubtree := child(tree, changedSide);
    var stableSide := opposite(changedSide);
    var uncle := child(tree, stableSide);
    assert tree.color.Black?;
    var newNode := child(changedSubtree, changedSide);
    var sub3 := child(changedSubtree, stableSide);

    var rotatedGrandparent := WologNode(
        stableSide, uncle, sub3, tree.value, Red);

    assert Contents(rotatedGrandparent) == Contents(sub3) + multiset{tree.value} + Contents(uncle);
    b := WologNode(changedSide, newNode, rotatedGrandparent,
        changedSubtree.value, Black);
    calc {
        Contents(b);
//        == Contents(newNode) + Contents(rotatedGrandparent) + multiset{changedSubtree.value};
//        == Contents(newNode) + Contents(sub3) + Contents(uncle) + multiset{tree.value} + multiset{changedSubtree.value};
        == Contents(changedSubtree) + Contents(uncle) + multiset{tree.value};   // OBSERVE
//        == Contents(origSubtree) + multiset{value} + Contents(uncle) + multiset{tree.value};
//        == Contents(tree) + multiset{value};
    }
    assert Contents(b) == Contents(tree) + multiset{value};
    assert BlackCountOnAllPaths(uncle, kc-1);
    assert BlackCountOnAllPaths(origSubtree, kc-1);
    assert sub3 == child(origSubtree, stableSide);
    assert BlackCountOnAllPaths(sub3, kc-1);
    BlackCountInheritance(rotatedGrandparent, kc - 1);
    assert BlackCountOnAllPaths(rotatedGrandparent, kc-1);
    assert BlackCountOnAllPaths(changedSubtree, kc-1);
    assert BlackCountOnAllPaths(newNode, kc-1);
    assert BlackCountOnAllPaths(b, kc);
    assert redOnRedViolation(b).Some? ==> ColorOf(tree).Red?;
    assert OrderedTree(b);
}

method RepairCase2Terminate(tree: Node, ghost kc: int, value: int, changedSide: Side, changedSubtree: Node) returns (b: Node)
    requires MostlyRBTree(child(tree, changedSide), kc, value, changedSubtree);
    ensures MostlyRBTree(tree, kc, value, b);
{
    var stableSide := opposite(changedSide);
    var stableSubtree := child(tree, stableSide);
    b := WologNode(changedSide, changedSubtree, stableSubtree,
        tree.value, tree.color);
    assert RedNodesHaveBlackChildren(b.left);
    assert RedNodesHaveBlackChildren(b.right);
    assert Contents(b) == Contents(tree) + multiset{value};
    assert BlackCountOnAllPaths(b, kc);
    assert redOnRedViolation(b).Some? ==> ColorOf(tree).Red?;
}

// May violate red-has-black-children rule at top level.
// This implementation will continue checking as it recurses back up
// the tree, but that's okay because we have to rebuild the tree pointers
// anyway.
method InnerInsert(tree: Node, ghost kc: int, value: int) returns (b: Node)
    requires RBTree(tree, kc);
    ensures MostlyRBTree(tree, kc, value, b);
{
    if tree.Nil? {
        b := Node(Nil, value, Nil, Red);
        assert MostlyRBTree(tree, kc, value, b);
    } else {
        var changedSide := if (value < tree.value) then Left else Right;
        var stableSide := opposite(changedSide);
        ghost var kcc := SubtreeBlackCount(tree, kc);
        var stableSubtree := child(tree, stableSide);
        var changedSubtree := InnerInsert(child(tree, changedSide), kcc, value);
        assert MostlyRBTree(child(tree, changedSide), kcc, value, changedSubtree);

        var violation := redOnRedViolation(changedSubtree);
        if (violation.Some?) {
            assert ColorOf(changedSubtree).Red?;
            if ColorOf(changedSubtree) == ColorOf(stableSubtree) {
                b := RepairCase3Recolor(tree, kc, value,
                    changedSide, changedSubtree);
            }

            var grandchildSide := violation.t;
            if (grandchildSide != changedSide) {
                changedSubtree := RepairCase4pt1RotateOutside(child(tree, changedSide), kcc, value, changedSubtree, changedSide);
                grandchildSide := changedSide;
            }

            b := RepairCase4pt2RotateUp(tree, kc, value, changedSide, changedSubtree);
        } else {
            b := RepairCase2Terminate(tree, kc, value, changedSide, changedSubtree);
        }
    }
}

method Insert(tree: Node, ghost kc: int, value: int) returns (updated: Node, ghost ukc: int)
    requires RBTree(tree, kc);
    ensures RBTree(updated, ukc);
    ensures Contents(updated) == Contents(tree) + multiset{value};
{
    updated := InnerInsert(tree, kc, value);
    assert RBTree(updated, ukc);
    assert Contents(updated) == Contents(tree) + multiset{value};
}


/*
method Contains(tree: Node, value: int) returns (present: bool)
    requires RBTree(tree);
    ensures present == (value in Contents(tree));
{
    if tree.Nil? {
        present := false;
        return;
    }
    if value == tree.value {
        present := true;
        return;
    }
    if value < tree.value {
        present := Contains(tree.left, value);
        return;
    }
    present := Contains(tree.right, value);
}

*/

method spaces(indent: int) {
    var i := 0;
    while (i < indent) {
        print " ";
        i := i + 1;
    }
}

method printTree(t: Node, indent: int) {
    if (t.Nil?) {
        return;
    }
    printTree(t.left, indent+2);
    spaces(indent);
    print t.value;
    print "\n";
    printTree(t.right, indent+2);
}

predicate eRBTree(tree: Node) {
    exists kc :: RBTree(tree, kc)
}

method eInsert(tree: Node, value: int) returns (updated: Node)
    requires eRBTree(tree);
    ensures eRBTree(updated);
{
    ghost var kc :| RBTree(tree, kc);
    ghost var ekc : int;
    updated, ekc := Insert(tree, kc, value);
}

method Main() {
    var t := Nil;
    RBTreeNil(t);
    t := eInsert(t, 6);
    t := eInsert(t, 3);
    t := eInsert(t, 8);
    t := eInsert(t, 4);
    t := eInsert(t, 1);
    t := eInsert(t, 7);
    t := eInsert(t, 9);
    printTree(t, 0);
    print Contents(t);
    print "\n";

    t := Nil;
    t := eInsert(t, 1);
    t := eInsert(t, 3);
    t := eInsert(t, 4);
    t := eInsert(t, 6);
    t := eInsert(t, 7);
    t := eInsert(t, 8);
    t := eInsert(t, 9);
    printTree(t, 0);
    print Contents(t);
    print "\n";
}
