// Copyright 2018-2021 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, and University of Washington
// SPDX-License-Identifier: BSD-2-Clause

module FloatingSeqMod {
  // A contiguous sequence of T whose first index can be greater than zero.

  // One surprising thing about this datatype is that there are infinitely many
  // FloatingSeqs that have no Get-able entries. Put differently, a FloatingSeq
  // "remembers" the length of its empty prefix even if there are no nonempty
  // indices following it. (We actually *want* this behavior in the use case
  // this datatype was designed for: a log whose prefix is truncated. The log
  // might be empty, but wants to remember how many entries have gone before even
  // though their values are forgotten now.)
  datatype FloatingSeq<T> = FloatingSeq(
    // Users of this datatype should not peek at these internal fields.  The
    // index math is confusing! That's what this datatype is here to do; hide
    // that offset math.
    start: nat,
    entries: seq<T>)
  {
    // Len() is the number of indices "occupied", *including* the empty space at
    // the beginning of the index space.
    function Len() : nat { start + |entries| }

    predicate ActiveRange(i: nat)
    {
      && start <= i < Len()
    }

    // You can only Get values after the empty space.
    function Get(i: nat) : T
      requires ActiveRange(i)
    {
      entries[i - start]
    }

    // You can chop off the right end of a FloatingSeq without shifting the
    // indices of elements.
    function GetPrefix(end: nat) : FloatingSeq<T>
      requires end <= Len()
    {
      if end <= start
      then FloatingSeq(end, [])
      else FloatingSeq(start, entries[..end-start])
    }

    // This datatype doesn't have a "RightSlice" operator because the intent is
    // that object indices don't move; the origin stays put. The closest analog
    // is this GetSuffix operation, which forgets some of the `entries`,
    // remembering only how many there used to be (in `start`), so that the
    // offsets of the surviving entries don't change.
    function GetSuffix(newStart: nat) : FloatingSeq<T>
      requires ActiveRange(newStart) || newStart == Len()
    {
      FloatingSeq(newStart, entries[newStart - start..])
    }

    function Append(elts: seq<T>) : FloatingSeq<T>
    {
      FloatingSeq(start, entries+elts)
    }

    function Last() : T
      requires Len() > 0
      requires ActiveRange(Len()-1)
    {
      Get(Len()-1)
    }
  
    function DropLast() : FloatingSeq<T>
      requires Len() > 0
    {
      GetPrefix(Len()-1)
    }
  }
}
