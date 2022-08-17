#![allow(unused_imports)]

use builtin_macros::*;
use builtin::*;
mod pervasive;
use pervasive::*;
// TODO Why doesn't pervasive::* let us see Map, Set?
use pervasive::seq::*;

verus!{

// A contiguous sequence of T whose first index can be greater than zero.

// One surprising thing about this datatype is that there are infinitely many
// FloatingSeqs that have no Get-able entries. Put differently, a FloatingSeq
// "remembers" the length of its empty prefix even if there are no nonempty
// indices following it. (We actually *want* this behavior in the use case
// this datatype was designed for: a log whose prefix is truncated. The log
// might be empty, but wants to remember how many entries have gone before even
// though their values are forgotten now.)

pub struct FloatingSeq<T> {
    start: nat,
    entries: Seq<T>,
}

impl<T> FloatingSeq<T> {
    // TODO if I omit "open" adjective, this file fails to compile!? (Followed, however, by a helpful message
    // about needing 'open' or 'closed')
    // Len() is the number of indices "occupied", *including* the empty space at
    // the beginning of the index space.
    pub open spec fn len(self) -> nat
    {
        self.start + self.entries.len()
    }

    pub open spec fn first_active_index(self) -> nat
    {
      self.start
    }

    // TODO omitting 'self' here gives a really confusing error message (but with a reasonable
    // suggestion about how to fix it)
    pub open spec fn is_active(self, i: nat) -> bool
    {
        self.start <= i < self.len()
    }

//    pub open spec fn get(self, i: nat) -> T
//      requires self.is_active(i)
//    {
//      self.entries[i - self.start]
//    }

    // You can only index values after the empty space.
    pub open spec fn spec_index(self, i: nat) -> T
        recommends self.is_active(i)
    {
        self.entries[i - self.start]
    }

    // You can chop off the right end of a FloatingSeq without shifting the
    // indices of elements.
    // TODO geez I hate writing self a billion places. Is this really the Rust way? That's dumb.
    pub open spec fn get_prefix(self, count: nat) -> FloatingSeq<T>
        recommends count <= self.len()
    {
        if count <= self.start { FloatingSeq{start: count, entries: Seq::empty()} }
        // TODO is there a slice syntax I could use instead of subrange?
        else { FloatingSeq{start: self.start, entries: self.entries.subrange(0, count-self.start)} }
    }

    // This datatype doesn't have a "RightSlice" operator because the intent is
    // that object indices don't move; the origin stays put. The closest analog
    // is this GetSuffix operation, which forgets some of the `entries`,
    // remembering only how many there used to be (in `start`), so that the
    // offsets of the surviving entries don't change.
    pub open spec fn get_suffix(self, newStart: nat) -> FloatingSeq<T>
        recommends self.is_active(newStart) || newStart == self.len()
    {
        FloatingSeq{start: newStart, entries: self.entries.subrange(newStart - self.start, self.entries.len())}
    }

    pub open spec fn append(self, elts: Seq<T>) -> FloatingSeq<T>
    {
            // TODO is there a + syntax for appending Seqs?
      FloatingSeq{start: self.start, entries: self.entries.add(elts)}
    }

    pub open spec fn last(self) -> T
        recommends
            self.len() > 0,
            // TODO These as-nats suck
            self.is_active((self.len()-1) as nat),
            // TODO Geez that's ugly. Please let me have my repeated requires keyword. Please.
            // Now a single requires is always written differently than two or three requires. Barf.
    {
        self[(self.len()-1) as nat]
    }

    pub open spec fn drop_last(self) -> FloatingSeq<T>
        recommends self.len() > 0
    {
        self.get_prefix((self.len()-1) as nat)
    }

    proof fn extensionality(self, b: FloatingSeq<T>)
        requires
            self.start == b.start,
            self.len() === b.len(),
            forall |i| self.is_active(i) ==> self[i] === b[i],
        ensures self === b
    {
        assert forall |i| 0<=i<self.entries.len() ==> self.entries[i] === b.entries[i] by {
        // TODO it's pretty bizarre that 'assert forall' has no parens but assert() is required to?
            assert(self[(self.start+i) as nat]===self.entries[i]);
            assert(b[(self.start+i) as nat]===b.entries[i]);
      }
    }
}

// TODO how to implement index operators in rust? Some trait?
//// Operator overloads
//function operator(| |)<T>(fs: FloatingSeq<T>) : nat
//{
//fs.Len()
//}
//
//function{:inline true} operator([])<T>(fs: FloatingSeq<T>, i:nat): T
//requires fs.is_active(i)
//{
//fs.Get(i)
//}

// Comprehension for FloatingSeq
// TODO thread 'rustc' panicked at 'The verifier does not yet support the following Rust feature: type fn(builtin::int) -> T', rust_verify/src/rust_to_vir_base.rs:301:13
//pub open spec fn floating_seq<T>(start: nat, length: nat, f: fn(int) -> T) -> FloatingSeq<T>
//    requires start <= length
//{
//    FloatingSeq{start: start, entries: Seq::new((length-start) as nat, |i: int| f(i+start))}
//}

}   //verus!

// TODO how to remove this main requirement?
fn main() { }
