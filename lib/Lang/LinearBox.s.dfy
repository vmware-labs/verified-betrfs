
module {:extern "LinearBox_s"} LinearBox_s {

  // Heap object that contains a linear value.
  // Prevents linear value from being duplicated (because heap objects can't be duplicated,
  // only references to heap objects can be duplicated).
  // Warning: does not necessarily ensure that linear value is deallocated properly.
  // (use SwapLinear, below, to guarantee deallocation)
  class {:extern} SwapAffine<A>
  {
    function {:axiom} Read():A
      reads this

    constructor {:extern "LinearBox_s", "SwapAffine"} (linear a:A)
      ensures Read() == a

    method {:extern} Swap(linear a1:A) returns(linear a2:A)
      modifies this
      ensures a2 == old(Read())
      ensures Read() == a1

    function method{:caller_must_be_pure}{:extern} Borrow():(shared a:A)
      reads this
      ensures a == Read()
  }

  // Same as SwapAffine, but with a destructor
  class {:extern} SwapLinear<A>
  {
    function {:axiom} Inv():(A)->bool
      reads this

    function {:axiom} Read():(a:A)
      reads this
      ensures Inv()(a)

    constructor {:extern "LinearBox_s", "SwapLinear"} (linear a:A, d:DestructorFunction<A>)
      requires OfDestructor(d).requires(a)
      ensures Inv() == OfDestructor(d).requires
      ensures Read() == a

    method {:extern} Swap(linear a1:A) returns(linear a2:A)
      requires Inv()(a1)
      modifies this
      ensures Inv() == old(Inv())
      ensures a2 == old(Read())
      ensures Read() == a1

    function method{:caller_must_be_pure}{:extern} Borrow():(shared a:A)
      reads this
      ensures a == Read()
  }

  type {:extern "struct"} DestructorFunction<A>

  function {:axiom} OfDestructor<A>(d:DestructorFunction<A>) : (linear A)-->()

  function method {:extern} ToDestructor<A>(f:(linear A)-->()) : (d:DestructorFunction<A>)
    ensures OfDestructor(d) == f

} // module

module Test_LinearBox_s {
  import opened LinearBox_s
  linear datatype q = Q(b:bool)
  function method D(linear x:q):() {linear var Q(_) := x; ()}
  function method D2(shared x:q):() {()}
  method M()
  {
    var s := new SwapLinear<q>(Q(true), ToDestructor<q>(D));
  }
}
