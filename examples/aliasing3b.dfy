/* owned */ class Node {
  var left: Node?;
  var right: Node?;
  var value: int;

  ghost var Repr: set<object>;

  /*[auto]*/ predicate unaliased()
  /*[auto]*/ reads this, this.Repr
  /*[auto]*/ {
  /*[auto]*/   owned_Ownership();
  /*[auto]*/   && {this} !!
  /*[auto]*/       (if this.left != null then this.left.Repr else {}) !!
  /*[auto]*/       (if this.right != null then this.right.Repr else {})
  /*[auto]*/   && (if this.left != null then this.left.unaliased() else true)
  /*[auto]*/   && (if this.right != null then this.right.unaliased() else true)
  /*[auto]*/ }

  /*[auto]*/ predicate {:axiom} this_Ownership()
  /*[auto]*/ reads this, this.Repr
  /*[auto]*/ ensures this in this.Repr
  /*[auto]*/ ensures this.left != null ==> this.left in this.left.Repr
  /*[auto]*/ ensures this.right != null ==> this.right in this.right.Repr
  /*[auto]*/ ensures this.left != null ==> this.left.Repr < this.Repr
  /*[auto]*/ ensures this.right != null ==> this.right.Repr < this.Repr
  /*[auto]*/ ensures this.left != null ==> this.left.this_Ownership()
  /*[auto]*/ ensures this.right != null ==> this.right.this_Ownership()
  /*[auto]*/ decreases this.Repr

  /*[auto]*/ predicate {:axiom} this_Unaliased()
  /*[auto]*/ requires this_Ownership()
  /*[auto]*/ reads this, this.Repr
  /*[auto]*/ ensures this.unaliased()
  /*[auto]*/ decreases this.Repr

  /*[auto]*/ predicate {:axiom} Ownership()
  /*[auto]*/ reads this, this.Repr
  /*[auto]*/ ensures this in this.Repr

  /*[auto]*/ lemma {:axiom} owned_Ownership()
  /*[auto]*/ ensures this_Ownership()
  /*[auto]*/ ensures Ownership()

  /*[auto]*/ lemma {:axiom} owned_Unaliased()
  /*[auto]*/ requires this_Ownership()
  /*[auto]*/ ensures this_Unaliased()

  /*[auto]*/ lemma {:axiom} owned_Ctor()
  /*[auto]*/ ensures fresh(this.Repr)

  /*[auto]*/ lemma {:axiom} owned_ReprGrowsFresh(old_: set<object>, minus: set<object>)
  /*[auto]*/ ensures fresh(this.Repr - old_ - minus)

  constructor (value_: int)
  ensures value == value_
  /*[auto]*/ ensures fresh(this.Repr)
  /*[auto]*/ ensures this.Ownership()
  {
    value := value_;
    left := null;
    right := null;

    new;

    this.owned_Ctor();
  }

  predicate Contains(value: int)
  /*[auto]*/ reads this, this.Repr
  /*[auto]*/ decreases this.Repr
  {
    /*[auto]*/ owned_Ownership();

    || this.value == value
    || (this.left != null && this.left.Contains(value))
    || (this.right != null && this.right.Contains(value))
  }

  method Insert(value: int)
  ensures Contains(value)
  /*[auto]*/ ensures fresh(this.Repr - old(this.Repr))
  /*[auto]*/ ensures this.Ownership()
  /*[auto]*/ modifies this, this.Repr
  /*[auto]*/ decreases this.Repr
  {
    /*[auto]*/ this.owned_Ownership();
    /*[auto]*/ this.owned_Unaliased();

    assume this.left != null;
    assume this.left.right != null;
    assume this.right != null;

    // var thing := this.left.right;

    // thing.left := this.right;
    // /*[auto]*/ thing.Repr := *;
    // /*[auto]*/ thing.left.Repr := *;
    // /*[auto]*/ assert thing.unaliased();

    // this.left.right := thing;
    // /*[auto]*/ this.Repr := *;
    // /*[auto]*/ this.left.Repr := *;
    // /*[auto]*/ assert this.unaliased();

    if value == this.value {
    } else if value < this.value {
      if this.left == null {
        var newNode := new Node(value);
        /*[auto]*/ newNode.owned_Ownership();
        /*[auto]*/ newNode.owned_Unaliased();
        this.left := newNode;
        /*[auto]*/ this.Repr := *;
        /*[auto]*/ this.owned_Ownership();
        /*[auto]*/ assert this.unaliased();
      } else {
        this.left.Insert(value);
        /*[auto]*/ this.owned_Ownership();
        /*[auto]*/ this.owned_Unaliased();
      }
    } else { // value > this.this
      if this.right == null {
        var newNode := new Node(value);
        /*[auto]*/ newNode.owned_Ownership();
        /*[auto]*/ newNode.owned_Unaliased();
        this.right := newNode;
        /*[auto]*/ this.Repr := *;
        /*[auto]*/ this.owned_Ownership();
        /*[auto]*/ assert this.unaliased();
      } else {
        this.right.Insert(value);
        /*[auto]*/ this.owned_Ownership();
        /*[auto]*/ this.owned_Unaliased();
      }
    }

    assert this.Contains(value);

    if this.right != null && this.left != null {
      /* parallel */ {
        var tmp := this.left;
        this.left := this.right;
        this.right := tmp;
      }
      /*[auto]*/ this.Repr := *;
      /*[auto]*/ this.owned_Ownership();
      /*[auto]*/ assert this.unaliased();
    }

    // if this.right != null && this.left == null {
    //   this.left := this.right;
    //   /*[auto]*/ this.Repr := *;
    //   /*[auto]*/ this.owned_Ownership();
    //   /*[auto]*/ assert this.unaliased();
    // }

    assert Contains(value);

    // if this.right != null && this.right.left != null && this.right.left.right == null && this.left != null && this.left.left != null {

    //   assume this.unaliased();

    //   this.right.left.right := this.left.left;

    //   /*[auto]*/ this.right.left.Repr := *;
    //   /*[auto]*/ this.right.Repr := *;
    //   /*[auto]*/ this.Repr := *;
    //   this.owned_Ownership();

    //   this.left.left := null;

    //   /*[auto]*/ this.left.Repr := *;
    //   /*[auto]*/ this.Repr := *;
    //   this.owned_Ownership();

    //   /*[auto]*/ assert this.unaliased();

    //   assert Contains(value);
    // }

    /*[auto]*/ this.owned_Ownership();
    /*[auto]*/ this.owned_ReprGrowsFresh(old(this.Repr), {});
  }
}

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
  && heap.widgetTree.Ownership()
  && heap.processTree.Ownership()
  && heap.widgetTree.Repr !! heap.processTree.Repr !! { heap }
}

method Operate(heap: HeapState)
requires Inv(heap)
requires heap.processTree.Contains(20)
modifies heap.widgetTree.Repr
{
  assert heap.processTree.Contains(20);
  heap.widgetTree.Insert(12);
  assert heap.widgetTree.Contains(12);
  heap.widgetTree.Insert(13);
  assert heap.processTree.Contains(20);
}

// == More of NodeInv ==
  // && (node.left.Some? ==> NodeInv(node.left.value))
  // && (node.right.Some? ==> NodeInv(node.right.value))
