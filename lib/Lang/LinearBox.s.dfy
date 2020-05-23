
module LinearBox_s {

  // Heap object that contains a linear value.
  // Prevents linear value from being duplicated (because heap objects can't be duplicated,
  // only references to heap objects can be duplicated).
  // Warning: does not necessarily ensure that linear value is deallocated properly.
  class SwapLinear<A>
  {
    function Read():A
      reads this

    constructor(linear a:A)
      ensures Read() == a

    method Swap(linear a1:A) returns(linear a2:A)
      modifies this
      ensures a2 == old(Read())
      ensures Read() == a1

    function method{:caller_must_be_pure} Borrow():(shared a:A)
      reads this
      ensures a == Read()
  }

} // module
