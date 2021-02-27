// Copyright 2018-2021 VMware, Inc.
// SPDX-License-Identifier: MIT

predicate method Less<Value>(a:Value, b:Value)
    // How do we insist that Value is a functional (non heap) type?
// assumed

lemma LessTransitive<Value>()
    ensures forall a, b, c: Value :: Less(a, b) && Less(b, c) ==> Less(a, c);
// assumed

predicate LessOrEqual<Value>(a:Value, b:Value)
{
    Less(a, b) || a==b
}

lemma LessOrEqualTransitive<Value>()
    ensures forall a, b, c: Value :: LessOrEqual(a, b) && LessOrEqual(b, c) ==> LessOrEqual(a, c);
{
    LessTransitive<Value>();
}

lemma LessAntisymmetry<Value>()
    ensures forall a, b: Value :: !Less(a, b) ==> LessOrEqual(b, a);
    ensures forall a, b: Value :: Less(a, b) ==> !LessOrEqual(b, a);

datatype Color = Red | Black
datatype Node<Value> = Nil | Node(
    left: Node,
    value: Value,
    right: Node,
    color: Color,
    ghost kc: int // the count of black nodes on any root-leaf path.
    )

// This function encodes "all leaves (NIL) are black"
function method ColorOf(node: Node) : Color {
    if node.Nil?
    then
        Black
    else
        node.color
}

function BlackCount(node: Node) : int {
    if node.Nil?
    then
        1
    else
        node.kc
}

predicate RedNodesHaveBlackChildren(tree: Node) {
    tree.Node? ==> (
        (tree.color.Red? ==>
            ColorOf(tree.left).Black?  && ColorOf(tree.right).Black?)
        && RedNodesHaveBlackChildren(tree.left)
        && RedNodesHaveBlackChildren(tree.right)
    )
}

function SubtreeBlackCount(tree: Node) : int {
    if ColorOf(tree).Black? then BlackCount(tree) - 1 else BlackCount(tree)
}

// The kc field of tree accurately measures the count of black nodes on each
// root-leaf path.
predicate BlackCountOnAllPaths(tree: Node) {
    if tree.Nil?
    then
        true
    else
           (SubtreeBlackCount(tree)
               == BlackCount(tree.left) == BlackCount(tree.right))
        && BlackCountOnAllPaths(tree.left)
        && BlackCountOnAllPaths(tree.right)
}

predicate RedBlackInv(tree: Node) {
       RedNodesHaveBlackChildren(tree)
    && BlackCountOnAllPaths(tree)
}

function method Contents<Value>(tree: Node) : multiset<Value>
{
    if tree.Nil?
    then multiset{}
    else
        Contents(tree.left) + Contents(tree.right) + multiset{tree.value}
}

predicate ValueIsOrdered<Value>(value: Value, side: Side, pivot: Value)
{
    if side.Left? then LessOrEqual(value, pivot) else LessOrEqual(pivot, value)
}

lemma ValueIsOrderedTransitivity<Value>()
    ensures forall a, b, c: Value, side: Side :: ValueIsOrdered(a, side, b) && ValueIsOrdered(b, side, c) ==> ValueIsOrdered(a, side, c);
{
    LessOrEqualTransitive<Value>();
}

// The not-recursive property that the set of elements on the left (resp) is on
// the correct side of the pivot.
predicate SideIsOrdered<Value>(subtree: Node, side: Side, pivot: Value)
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

predicate RBTree(tree: Node) {
    OrderedTree(tree) && RedBlackInv(tree)
}

// Tools to work manipulate trees without loss of generality over symmetry.

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

function method NodeBySide<Value>(side: Side, t1: Node, t2: Node, value: Value, color: Color, ghost kc: int) : Node
{
    if side.Left?
    then Node(t1, value, t2, color, kc)
    else Node(t2, value, t1, color, kc)
}

predicate MostlyRBTree<Value>(tree:Node, value: Value, b: Node)
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
    && BlackCountOnAllPaths(b)
    && (redOnRedViolation(b).Some? ==> ColorOf(tree).Red?)
       // Allow at most one red-on-red violation (a black uncle)
    && (ColorOf(b).Red? ==> ColorOf(b.left).Black? || ColorOf(b.right).Black?)
}

method RepairCase3Recolor<Value>(tree: Node, value: Value, changedSide: Side, changedSubtree: Node) returns (b: Node)
    requires tree.Node?;
    requires tree.color.Black?;
    requires RBTree(tree);
    requires changedSubtree.Node?;
    requires ColorOf(changedSubtree).Red?;
    requires ColorOf(child(tree, opposite(changedSide))).Red?;  // uncle is red
    requires ValueIsOrdered(value, changedSide, tree.value);
    requires MostlyRBTree(child(tree, changedSide), value, changedSubtree);
    requires BlackCount(changedSubtree) == SubtreeBlackCount(tree);
    ensures BlackCount(b) == BlackCount(tree);
    ensures MostlyRBTree(tree, value, b);
    ensures Contents(child(b, opposite(changedSide))) == Contents(child(tree, opposite(changedSide)));
{
    var stableSide := opposite(changedSide);
    var stableSubtree := child(tree, stableSide);

    var recoloredChanged := Node(changedSubtree.left,
        changedSubtree.value, changedSubtree.right, Black, tree.kc);

    var newStable := Node(stableSubtree.left,
        stableSubtree.value, stableSubtree.right, Black, tree.kc);
    assert BlackCountOnAllPaths(stableSubtree); // observe (recursion)

    b := NodeBySide(changedSide, recoloredChanged, newStable, tree.value, Red, tree.kc);
    assert RedNodesHaveBlackChildren(child(tree, stableSide));  //observe
    assert stableSubtree.kc == SubtreeBlackCount(tree); // observe
    assert OrderedTree(stableSubtree);  // observe
}

method RepairCase4pt1RotateOutside<Value>(childTree: Node, value: Value, changedTree: Node, changedSide: Side) returns (rotated: Node)
    // changedSide is the side of childTree that changed -- the red-on-red
    // violation child.
    requires RBTree(childTree);
    requires MostlyRBTree(childTree, value, changedTree);
    requires ColorOf(changedTree).Red?;
    requires ColorOf(child(changedTree, changedSide)).Red?;
    ensures BlackCount(rotated) == BlackCount(changedTree);
    ensures MostlyRBTree(childTree, value, rotated);
    ensures ColorOf(rotated).Red?;
    ensures ColorOf(child(rotated, opposite(changedSide))).Red?;
{
    var stableSide := opposite(changedSide);
    var sub1 := child(changedTree, stableSide);
    var inner := child(changedTree, changedSide);

    assert ColorOf(inner).Red?;
    var sub2 := child(inner, stableSide);
    var sub3 := child(inner, changedSide);

    var outer := NodeBySide(stableSide, sub1, sub2, changedTree.value, Red, changedTree.kc);
    rotated := NodeBySide(changedSide, sub3, outer, inner.value, Red, changedTree.kc);

    // Whoah. Somehow this whole calculation is required to get OrderedTree,
    // which is bizarre. These spooky actions-at-a-distance make me suspect I'm
    // bumping into unrolling limits from having recursive definitions opened.
    // Instant regret.
    assert Contents(rotated) == Contents(changedTree);  // observe
//    assert Contents(rotated) == Contents(childTree) + multiset{value}; // goal

    assert OrderedTree(inner);  // observe to unpack recursion for sub2
    assert ValueIsOrdered(inner.value, changedSide, changedTree.value); // observe

    forall x | x in Contents(outer)
        ensures ValueIsOrdered(x, stableSide, inner.value) {
        if x in Contents(sub1) {
            assert ValueIsOrdered(x, stableSide, changedTree.value);
            assert ValueIsOrdered(changedTree.value, stableSide, inner.value);
            ValueIsOrderedTransitivity<Value>();
        }
    }
    assert OrderedTree(rotated);  // goal

    assert BlackCountOnAllPaths(inner);    // observe (recursive unpack)
//    assert BlackCountOnAllPaths(rotated);    // goal
}

method RepairCase4pt2RotateUp<Value>(tree: Node, value: Value, changedSide: Side,
    changedSubtree: Node) returns (b: Node)
    requires RBTree(tree);
    requires tree.Node?;
    requires ColorOf(changedSubtree).Red?;
    requires ColorOf(child(tree, opposite(changedSide))).Black?;
    requires ColorOf(child(changedSubtree, changedSide)).Red?;
    // insert obeyed tree.value pivot.
    requires SideIsOrdered(changedSubtree, changedSide, tree.value);
    // Stable grandchild didn't change.
    requires child(tree, changedSide).Node?;
    requires changedSubtree.kc == tree.kc - 1;
    requires MostlyRBTree(child(tree, changedSide), value, changedSubtree);
    ensures BlackCount(b) ==BlackCount(tree);
    ensures MostlyRBTree(tree, value, b);
{
    ghost var origSubtree := child(tree, changedSide);
    var stableSide := opposite(changedSide);
    var uncle := child(tree, stableSide);
    var newNode := child(changedSubtree, changedSide);
    var sub3 := child(changedSubtree, stableSide);

    var rotatedGrandparent := NodeBySide(
        stableSide, uncle, sub3, tree.value, Red, tree.kc - 1);
    // Show by case analysis that rotatedGrandparent ends up on the correct
    // side of changedSubtree.value.
    forall x | x in Contents(rotatedGrandparent)
        ensures ValueIsOrdered(x, stableSide, changedSubtree.value);
    {
        assert ValueIsOrdered(changedSubtree.value, changedSide, tree.value);   // OBSERVE
        if x in Contents(uncle) {
            assert ValueIsOrdered(x, stableSide, tree.value);
            assert ValueIsOrdered(tree.value, stableSide, changedSubtree.value);
            ValueIsOrderedTransitivity<Value>();
        }
    }

    b := NodeBySide(changedSide, newNode, rotatedGrandparent,
        changedSubtree.value, Black, tree.kc);
    assert Contents(b) == Contents(changedSubtree) + Contents(uncle) + multiset{tree.value};   // OBSERVE
}

// The changedSubtree has no violation. If the root is black, then b has no
// violation; if it's red, we pass through a single violation (as the recursion
// rule allows) for the next layer to fix.
method RepairCase2Passthrough<Value>(tree: Node, value: Value, changedSide: Side, changedSubtree: Node) returns (b: Node)
    requires tree.Node?;
    requires RBTree(tree);
    requires redOnRedViolation(changedSubtree).None?;
    requires SideIsOrdered(changedSubtree, changedSide, tree.value);
    requires MostlyRBTree(child(tree, changedSide), value, changedSubtree);
    requires changedSubtree.kc == SubtreeBlackCount(tree);
    ensures BlackCount(b) == BlackCount(tree);
    ensures MostlyRBTree(tree, value, b);
{
    var stableSide := opposite(changedSide);
    var stableSubtree := child(tree, stableSide);
    b := NodeBySide(changedSide, changedSubtree, stableSubtree,
        tree.value, tree.color, tree.kc);
}

// May violate red-has-black-children rule at top level.
// This implementation will continue checking as it recurses back up
// the tree, but that's okay because we have to rebuild the tree pointers
// anyway.
method InnerInsert<Value>(tree: Node, value: Value)
    returns (b: Node, ghost changedSideOut: Side)
    requires RBTree(tree);
    ensures MostlyRBTree(tree, value, b);
    ensures BlackCount(b) == BlackCount(tree);
{
    if tree.Nil? {
        b := Node(Nil, value, Nil, Red, 1);
    } else {
        var changedSide := if Less(value, tree.value) then Left else Right;
        LessAntisymmetry<Value>();
        var stableSide := opposite(changedSide);
        var stableSubtree := child(tree, stableSide);
        var changedSubtree, insertChanged :=
            InnerInsert(child(tree, changedSide), value);

        var violation := redOnRedViolation(changedSubtree);
        if (violation.Some?) {
            if ColorOf(changedSubtree) == ColorOf(stableSubtree) {
                assert BlackCount(changedSubtree) == SubtreeBlackCount(tree);
                b := RepairCase3Recolor(tree, value,
                    changedSide, changedSubtree);
            } else {
                var grandchildSide := violation.t;
                if (grandchildSide != changedSide) {
                    var origChild := child(tree, changedSide);
                    changedSubtree := RepairCase4pt1RotateOutside(
                        origChild, value, changedSubtree, grandchildSide);
                    grandchildSide := changedSide;
                }
                b := RepairCase4pt2RotateUp(tree, value, changedSide, changedSubtree);
            }
        } else {
            // No red-on-red violation to fix from the kid. Might have made
            // one here, though.
            b := RepairCase2Passthrough(
                tree, value, changedSide, changedSubtree);
        }
        changedSideOut := changedSide;
    }
    assert BlackCountOnAllPaths(b);
}

method RepairCase1Root<Value>(tree: Node, value: Value, b: Node) returns (c: Node)
    requires MostlyRBTree(tree, value, b);
    ensures RBTree(c);
    ensures Contents(c) == Contents(tree) + multiset{value};
{
    if ColorOf(b).Black? {
        c := b;
    } else {
        c := Node(b.left, b.value, b.right, Black, b.kc + 1);
    }
}

method Insert<Value>(tree: Node, value: Value) returns (updated: Node)
    requires RBTree(tree);
    ensures RBTree(updated);
    ensures Contents(updated) == Contents(tree) + multiset{value};
{
    ghost var innerChanged: Side;
    var mostlyUpdated: Node;
    mostlyUpdated, innerChanged := InnerInsert(tree, value);
    updated := RepairCase1Root(tree, value, mostlyUpdated);
}


method Contains<Value(==)>(tree: Node, value: Value) returns (present: bool)
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
    if Less(value, tree.value) {
        present := Contains(tree.left, value);
        LessAntisymmetry<Value>();
        return;
    }
    present := Contains(tree.right, value);
}

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

method Main() {
    var t := Nil;
    t := Insert(t, 6);
    t := Insert(t, 3);
    t := Insert(t, 8);
    t := Insert(t, 4);
    t := Insert(t, 1);
    t := Insert(t, 7);
    t := Insert(t, 9);
    printTree(t, 0);
    print Contents(t);
    print "\n";

    t := Nil;
    t := Insert(t, 1);
    t := Insert(t, 3);
    t := Insert(t, 4);
    t := Insert(t, 6);
    t := Insert(t, 7);
    t := Insert(t, 8);
    t := Insert(t, 9);
    printTree(t, 0);
    print Contents(t);
    print "\n";
}
