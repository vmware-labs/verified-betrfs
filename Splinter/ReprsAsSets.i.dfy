include "../lib/Base/Option.s.dfy"

// When Jon first drafted Journal.i.dfy, he computed IReads as a function,
// at the same time as recursively walking the DiskView. Travis points out
// that we had an analogous challenge in mem-heap reasoning, and we often
// found it was better to inductively maintain a ghosty repr state.
// This file shows what that might look like. Jon has a TODO to try porting
// the journal over to this style once there's an inductive proof to try
// it on.
// Why Jon is contractually obligated to prefer this style: it is more
// Lookup-y: the IReads-function style keeps the repr set as a recursive
// definition; this style exposes the read set as a quantified representation.

module Example {
  import opened Options

  // AllocationTable is block 0
  // Root of linked list is block 1
  datatype Block =
    | AllocationTable(alloc: set<int>)
    | Link(value: int, next: Option<int>)

  type DiskView = map<int, Block>

  datatype Variables = Variables(
      repr: set<int>,
      disk: DiskView)

  datatype Interpretation = Interpretation(
      allocation: set<int>,
      list: seq<int>)

  function view_of_repr(repr: set<int>, disk: DiskView): DiskView {
    map disk_idx | disk_idx in disk && disk_idx in repr :: disk[disk_idx]
  }

  predicate InvView(view: DiskView) {
    && 0 in view
    && view[0].AllocationTable?
    && 1 in view // root of linked list
    && (forall disk_idx :: disk_idx in view && disk_idx != 0 ==>
        && view[disk_idx].Link?
        && (view[disk_idx].next.Some? ==>
          && view[disk_idx].next.value in view
          && view[disk_idx].next.value != 0))
  }

  function Interp(view: DiskView) : Interpretation
  requires InvView(view)
  {
    Interpretation(view[0].alloc, InterpLinkedList(view, 1, 100))
  }

  function InterpLinkedList(view: DiskView, i: int, max_size: nat) : seq<int>
  requires InvView(view)
  requires i in view
  requires view[i].Link?
  decreases max_size
  {
    if max_size == 0 then []
    else if view[i].next.Some? then
      [view[i].value] + InterpLinkedList(view, view[i].next.value, max_size - 1)
    else
      [view[i].value]
  }

  predicate Inv(s: Variables) {
    // Take a view of the disk from the repr
    var view := view_of_repr(s.repr, s.disk);
    // This view is well-formed
    && InvView(view)
    // The interpretation's allocation table matches our 'ghost' repr
    && Interp(view).allocation == s.repr
  }

  // really dumb operation
  // set the list to the value [19]

  predicate set_to_19(s: Variables, s': Variables) {
    s'.repr == {0, 1} // set the repr to the new allocation
    && s'.disk == s.disk
      [0 := AllocationTable(s'.repr)]  // update allocation table the same way
      [1 := Link(19, None)]
  }
}
