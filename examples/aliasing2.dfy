datatype Option<V> = Some(value: V) | None

class Node {
  var left: Option<Node>;
  var right: Option<Node>;
  var value: int;

  ghost var Repr: set<object>;

  constructor (value_: int)
  ensures value == value_
  ensures NodeInv(this)
  {
    value := value_;
    assume false;
  }
}

predicate NodeInv(node: Node)
reads node, node.Repr
decreases node.Repr
{
  && { node } +
      (if node.left.Some? then {node.left.value} else {}) +
      (if node.right.Some? then {node.right.value} else {}) <= node.Repr
  && node.Repr == { node } +
      (if node.left.Some? then node.left.value.Repr else {}) +
      (if node.right.Some? then node.right.value.Repr else {})
}

method Insert(root: Node, value: int)
requires NodeInv(root)
ensures NodeInv(root)
ensures Contains(root, value)
ensures forall r | r in root.Repr :: r in old(root.Repr) || fresh(r)
modifies root, root.Repr

predicate Contains(root: Node, value: int)
// requires NodeInv(root)
reads root, root.Repr

class HeapState {
  var widgetTree: Node;
  var processTree: Node;

  constructor()
  {
    widgetTree := new Node(15);
    processTree := new Node(20);
  }
}

predicate Inv(heap: HeapState)
reads heap
reads heap.widgetTree, heap.widgetTree.Repr
reads heap.processTree, heap.processTree.Repr
{
  && NodeInv(heap.widgetTree)
  && NodeInv(heap.processTree)
  // && {heap.widgetTree} !! {heap.processTree} !! { heap }
  && heap.widgetTree.Repr !! heap.processTree.Repr !! { heap }
}

method Operate(heap: HeapState)
requires Inv(heap)
requires Contains(heap.processTree, 20)
modifies heap.widgetTree.Repr
{
  assert Contains(heap.processTree, 20);
  Insert(heap.widgetTree, 12);
  assert Contains(heap.widgetTree, 12);
  Insert(heap.widgetTree, 13);
  assert Contains(heap.processTree, 20);
}

// == More of NodeInv ==
  // && (if node.left.Some? then node.left.value.Repr else {}) < node.Repr
  // && (if node.right.Some? then node.right.value.Repr else {}) < node.Repr
  // && (if node.left.Some? then {node.left} else {}) !! (if node.right.Some? then {node.right} else {})
  // && (node.left.Some? ==> NodeInv(node.left.value))
  // && (node.right.Some? ==> NodeInv(node.right.value))
