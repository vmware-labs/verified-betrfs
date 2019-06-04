datatype Node = Nil | Node(left: Node, value: int, right: Node)

function method Contents(tree: Node) : multiset<int>
{
    if tree.Nil?
    then multiset{}
    else
        Contents(tree.left) + Contents(tree.right) + multiset{tree.value}
}

predicate OrderedTree(tree: Node) {
    tree.Nil?
    || (
           (forall lv :: lv in Contents(tree.left) ==> lv <= tree.value)
        && (forall rv :: rv in Contents(tree.right) ==> tree.value <= rv)
        && OrderedTree(tree.left)
        && OrderedTree(tree.right)
        )
}

method Insert(tree: Node, value: int) returns (updated: Node)
    requires OrderedTree(tree);
    ensures OrderedTree(updated);
    ensures Contents(updated) == Contents(tree) + multiset{value};
{
    if tree.Nil? {
        updated := Node(Nil, value, Nil);
    } else {
        if (value < tree.value) {
            var leftSubtree := Insert(tree.left, value);
            updated := Node(leftSubtree, tree.value, tree.right);
        } else {
            var rightSubtree := Insert(tree.right, value);
            updated := Node(tree.left, tree.value, rightSubtree);
        }
    }
}

method Contains(tree: Node, value: int) returns (present: bool)
    requires OrderedTree(tree);
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

method RotateRight(a: Node) returns (b: Node)
    requires OrderedTree(a);
    requires !a.Nil? && !a.left.Nil?;
    ensures OrderedTree(b);
    ensures Contents(a) == Contents(b);
{
    var l := a.left;
    var r := Node(l.right, a.value, a.right);

    // Dafny needs help realizing why everything in r is right of l.value;
    // it needs me to point out that l.value < a.value.
    forall x | x in Contents(r) 
        ensures l.value <= x;
    {
        assert l.value in Contents(a.left);
    }
    // A similar property that r.left (l.right) is left of r.value, because
    // it was left of a.value in the precondition.
    forall x | x in Contents(r.left)
        ensures x <= r.value;
    {
        assert x in Contents(a.left);
    }

    b := Node(l.left, l.value, r);
}

method RotateLeft(a: Node) returns (b: Node)
    requires OrderedTree(a);
    requires !a.Nil? && !a.right.Nil?;
    ensures OrderedTree(b);
    ensures Contents(a) == Contents(b);
{
    var r := a.right;
    var l := Node(a.left, a.value, r.left);

    forall x | x in Contents(l) 
        ensures x <= r.value;
    {
        assert r.value in Contents(a.right);
        // For some reason we need the case analysis this time!?
        if (x in Contents(l.left)) {
            //assert r.value in Contents(a.right);
        }
    }
    forall x | x in Contents(l.right)
        ensures l.value <= x;
    {
        assert x in Contents(a.right);
    }

    b := Node(l, r.value, r.right);
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
