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

// The not-recursive property that the set of elements on the left (resp) is on
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

//method RotateRight(a: Node, ghost kc: int) returns (b: Node)
//    requires RBTree(a, kc);
//    requires !a.Nil? && !a.left.Nil?;
//    ensures !b.Nil?;
//    ensures Contents(a) == Contents(b);
//{
//    var l := a.left;
//    var r := Node(l.right, a.value, a.right, Black);
//
//    // Dafny needs help realizing why everything in r is right of l.value;
//    // it needs me to point out that l.value < a.value.
//    forall x | x in Contents(r) 
//        ensures l.value <= x;
//    {
//        assert OrderedTree(l);
//        assert l.value in Contents(a.left);
//        // Think about the cases, Dafny! (In particular, expand Contents).
//        if x in Contents(r.left) {
//        } else if x in Contents(r.right) {
//        } else if x in multiset{r.value} {
//        }
//    }
//    // A similar property that r.left (l.right) is left of r.value, because
//    // it was left of a.value in the precondition.
//    forall x | x in Contents(r.left)
//        ensures x <= r.value;
//    {
//        assert x in Contents(a.left);
//    }
//
//    b := Node(l.left, l.value, r, Black);
//}

function method redOnRedViolation(tree: Node) : Option<Side>
{
    if ColorOf(tree).Black? then
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
    // b is tree + value
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
    ensures Contents(child(b, opposite(changedSide))) == Contents(child(tree, opposite(changedSide)));
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
    // changedSide is the side of childTree that changed -- the red-on-red
    // violation child.
    requires RBTree(childTree, kcc);
    requires MostlyRBTree(childTree, kcc, value, changedTree);
    //requires ColorOf(childTree).Red?;
    requires ColorOf(changedTree).Red?;
    requires ColorOf(child(changedTree, changedSide)).Red?;
    ensures MostlyRBTree(childTree, kcc, value, rotated);
    ensures ColorOf(rotated).Red?;
    ensures ColorOf(child(rotated, opposite(changedSide))).Red?;
{
/*
    assert ColorOf(childTree).Red?;
    var stableSide := opposite(changedSide);
    var sub1 := child(childTree, stableSide);
    var inner := child(childTree, changedSide);
    assert ColorOf(inner).Red?;
    var sub2 := child(inner, stableSide);
    var sub3 := child(inner, changedSide);
*/
    var stableSide := opposite(changedSide);
    var sub1 := child(changedTree, stableSide);
    var inner := child(changedTree, changedSide);
    assert ColorOf(inner).Red?;
    var sub2 := child(inner, stableSide);
    var sub3 := child(inner, changedSide);

    var outer := WologNode(stableSide, sub1, sub2, changedTree.value, Red);
    rotated := WologNode(changedSide, sub3, outer, inner.value, Red);

    // Whoah. Somehow this whole calculation is required to get OrderedTree,
    // which is bizarre. These spooky actions-at-a-distance make me suspect I'm
    // bumping into unrolling limits from having recursive definitions opened.
    // Instant regret.
    assert Contents(rotated) == Contents(changedTree);  // observe
    assert Contents(rotated) == Contents(childTree) + multiset{value}; // goal

    assert OrderedTree(inner);  // observe to unpack recursion for sub2
    assert ValueIsOrdered(inner.value, changedSide, changedTree.value); // observe
    assert OrderedTree(rotated);  // goal

    assert BlackCountOnAllPaths(inner, kcc);    // observe (recursive unpack)
//    assert BlackCountOnAllPaths(rotated, kcc);    // goal
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
    // insert obeyed tree.value pivot.
    requires SideIsOrdered(changedSubtree, changedSide, tree.value);
    // Stable grandchild didn't change.
    requires child(tree, changedSide).Node?;
    requires MostlyRBTree(child(tree, changedSide), kc - 1, value, changedSubtree);
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
    // Show by case analysis that rotatedGrandparent ends up on the correct
    // side of changedSubtree.value.
    forall x | x in Contents(rotatedGrandparent)
        ensures ValueIsOrdered(x, stableSide, changedSubtree.value);
    {
        assert ValueIsOrdered(changedSubtree.value, changedSide, tree.value);
        if x in Contents(uncle) {
        } else if x in Contents(sub3) {
        } else {
            assert x == tree.value;
        }
    }

    b := WologNode(changedSide, newNode, rotatedGrandparent,
        changedSubtree.value, Black);
    assert Contents(b) == Contents(changedSubtree) + Contents(uncle) + multiset{tree.value};   // OBSERVE
}


method RepairCase2Terminate(tree: Node, ghost kc: int, value: int, changedSide: Side, changedSubtree: Node) returns (b: Node)
    requires tree.Node?;
    requires RBTree(tree, kc);
    requires ColorOf(tree).Black?;
    requires redOnRedViolation(changedSubtree).None?;
    requires SideIsOrdered(changedSubtree, changedSide, tree.value);
    requires MostlyRBTree(child(tree, changedSide), kc - 1, value, changedSubtree);
    ensures MostlyRBTree(tree, kc, value, b);
{
    var stableSide := opposite(changedSide);
    var stableSubtree := child(tree, stableSide);
    b := WologNode(changedSide, changedSubtree, stableSubtree,
        tree.value, Black);
}

method RepairCase2Passthrough(tree: Node, ghost kc: int, value: int, changedSide: Side, changedSubtree: Node) returns (b: Node)
    requires tree.Node?;
    requires RBTree(tree, kc);
    requires redOnRedViolation(changedSubtree).None?;
    requires SideIsOrdered(changedSubtree, changedSide, tree.value);
    requires MostlyRBTree(child(tree, changedSide), SubtreeBlackCount(tree, kc), value, changedSubtree);
    ensures MostlyRBTree(tree, kc, value, b);
    //ensures redOnRedViolation(b).Some? ==> ColorOf(child(tree, changedSide)).Red?;
{
    var stableSide := opposite(changedSide);
    var stableSubtree := child(tree, stableSide);
    b := WologNode(changedSide, changedSubtree, stableSubtree,
        tree.value, tree.color);
}

// May violate red-has-black-children rule at top level.
// This implementation will continue checking as it recurses back up
// the tree, but that's okay because we have to rebuild the tree pointers
// anyway.
method InnerInsert(tree: Node, ghost kc: int, value: int)
    returns (b: Node, ghost changedSideOut: Side)
    requires RBTree(tree, kc);
    ensures MostlyRBTree(tree, kc, value, b);
    //ensures redOnRedViolation(b).Some? ==> ColorOf(child(tree, changedSideOut)).Red?;
{
    if tree.Nil? {
        b := Node(Nil, value, Nil, Red);
        assert MostlyRBTree(tree, kc, value, b);
    } else {
        var changedSide := if (value < tree.value) then Left else Right;
        var stableSide := opposite(changedSide);
        ghost var kcc := SubtreeBlackCount(tree, kc);
        var stableSubtree := child(tree, stableSide);
        var changedSubtree, insertChanged :=
            InnerInsert(child(tree, changedSide), kcc, value);
        assert MostlyRBTree(child(tree, changedSide), kcc, value, changedSubtree);

        var violation := redOnRedViolation(changedSubtree);
        if (violation.Some?) {
//            assert ColorOf(changedSubtree).Red?;
            if ColorOf(changedSubtree) == ColorOf(stableSubtree) {
                b := RepairCase3Recolor(tree, kc, value,
                    changedSide, changedSubtree);
            } else {
//                assert ColorOf(tree).Black?;
                    // or else we couldn't have got a red-on-red violation
//                assert ColorOf(changedSubtree).Red?;

                var grandchildSide := violation.t;
                if (grandchildSide != changedSide) {
                    var origChild := child(tree, changedSide);
                    changedSubtree := RepairCase4pt1RotateOutside(origChild, kcc, value, changedSubtree, grandchildSide);
                    grandchildSide := changedSide;
                }
                b := RepairCase4pt2RotateUp(tree, kc, value, changedSide, changedSubtree);
            }
        } else {
            // No red-on-red violation to fix from the kid. Might have made
            // one here, though.
            b := RepairCase2Passthrough(tree, kc, value, changedSide, changedSubtree);
        }
        changedSideOut := changedSide;
    }
}

method RepairCase1Root(tree: Node, ghost kc: int, value: int, b: Node) returns (c: Node, ghost nkc: int)
    requires MostlyRBTree(tree, kc, value, b);
    ensures RBTree(c, nkc);
    ensures Contents(c) == Contents(tree) + multiset{value};
{
    if ColorOf(b).Black? {
        c := b;
        nkc := kc;
    } else {
        c := Node(b.left, b.value, b.right, Black);
        nkc := kc + 1;
    }
}

method Insert(tree: Node, ghost kc: int, value: int) returns (updated: Node, ghost ukc: int)
    requires RBTree(tree, kc);
    ensures RBTree(updated, ukc);
    ensures Contents(updated) == Contents(tree) + multiset{value};
{
    ghost var innerChanged: Side;
    var mostlyUpdated: Node;
    mostlyUpdated, innerChanged := InnerInsert(tree, kc, value);
    updated, ukc := RepairCase1Root(tree, kc, value, mostlyUpdated);
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
