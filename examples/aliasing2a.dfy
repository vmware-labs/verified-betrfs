class Node {
  var left: Node?;
  var right: Node?;
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
      (if node.left != null then {node.left} else {}) +
      (if node.right != null then {node.right} else {}) <= node.Repr
  && node.Repr == { node } +
      (if node.left != null then node.left.Repr else {}) +
      (if node.right != null then node.right.Repr else {})
}

method Insert(root: Node, value: int)
requires NodeInv(root)
ensures NodeInv(root)
ensures Contains(root, value)
modifies root, root.Repr

predicate Contains(root: Node, value: int)
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
  && heap.widgetTree.Repr !! heap.processTree.Repr !! {heap}
}

method Operate(heap: HeapState)
requires Inv(heap)
requires Contains(heap.processTree, 20)
modifies heap.widgetTree.Repr
{
  assert Contains(heap.processTree, 20);
  Insert(heap.widgetTree, 12);
  assert Contains(heap.processTree, 20);
}

