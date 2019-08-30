class Node {
  var left: Node?;
  var right: Node?;
  var value: int;

  ghost var Repr: set<object>;

  constructor (value_: int)
  ensures value == value_
  ensures fresh(this.Repr)
  ensures this.ReprInv()
  {
    value := value_;
    left := null;
    right := null;

    new;

    Repr := { this };
  }

  predicate ReprInv()
  reads this, this.Repr
  decreases this.Repr
  {
    && { this } +
        (if this.left != null then {this.left} else {}) +
        (if this.right != null then {this.right} else {}) <= this.Repr
    && this.Repr == { this } +
        (if this.left != null then this.left.Repr else {}) +
        (if this.right != null then this.right.Repr else {})
    && (if this.left != null then this.left.Repr else {}) !! (if this.right != null then this.right.Repr else {}) !! {this}

    && (if this.left != null then this.left.Repr else {}) < this.Repr
    && (if this.right != null then this.right.Repr else {}) < this.Repr
    && (this.left != null ==> this.left.ReprInv())
    && (this.right != null ==> this.right.ReprInv())
  }

  method Insert(value: int)
  requires this.ReprInv()
  ensures this.ReprInv() 
  ensures Contains(this, value)
  ensures fresh(this.Repr - old(this.Repr))
  modifies this, this.Repr
  decreases this.Repr
  {
    assert this.left != null ==> this.left.ReprInv();
    assert this.right != null ==> this.right.ReprInv();

    if value == this.value {
    } else if value < this.value {
      if this.left == null {
        var newNode := new Node(value);
        this.left := newNode;
      } else {
        this.left.Insert(value);
      }
    } else { // value > this.this
      if this.right == null {
        var newNode := new Node(value);
        this.right := newNode;
      } else {
        this.right.Insert(value);
      }
    }

    this.Repr := { this } +
        (if this.left != null then this.left.Repr else {}) +
        (if this.right != null then this.right.Repr else {});

    assume Contains(this, value);
  }
}

predicate Contains(node: Node, value: int)
requires node.ReprInv()
reads node, node.Repr

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
  && heap.widgetTree.ReprInv()
  && heap.processTree.ReprInv()
  && heap.widgetTree.Repr !! heap.processTree.Repr !! { heap }
}

method Operate(heap: HeapState)
requires Inv(heap)
requires Contains(heap.processTree, 20)
modifies heap.widgetTree.Repr
{
  assert Contains(heap.processTree, 20);
  heap.widgetTree.Insert(12);
  assert Contains(heap.widgetTree, 12);
  heap.widgetTree.Insert(13);
  assert Contains(heap.processTree, 20);
}

// == More of NodeInv ==
  // && (node.left.Some? ==> NodeInv(node.left.value))
  // && (node.right.Some? ==> NodeInv(node.right.value))
