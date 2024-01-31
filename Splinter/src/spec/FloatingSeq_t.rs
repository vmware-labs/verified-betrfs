// Copyright 2018-2023 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, University of Washington
// SPDX-License-Identifier: BSD-2-Clause
use crate::spec::MapSpec_t::Version;
use builtin::*;
use builtin_macros::*;
use vstd::{seq::*, *};

verus! {

// A contiguous sequence of T whose first index can be greater than zero.
// One surprising thing about this datatype is that there are infinitely many
// FloatingSeqs that have no Get-able entries. Put differently, a FloatingSeq
// "remembers" the length of its empty prefix even if there are no nonempty
// indices following it. (We actually *want* this behavior in the use case
// this datatype was designed for: a log whose prefix is truncated. The log
// might be empty, but wants to remember how many entries have gone before even
// though their values are forgotten now.)
#[verifier::ext_equal]
pub struct FloatingSeq<T> {
    // TODO: Want to make these private, which entails making most specs in here closed,
    // but that would kill all automation. Waiting for some way to "broadcast-forall"
    // some lemmas that export properties of the closed specs.
    // Proposed temporary workaround: write a single lemma with all the foralls in ensures,
    // and then users call that everywhere.
    // (waiting on new automation-control features.)
    pub start: nat,
    pub entries: Seq<T>,
}

impl<T> FloatingSeq<T> {
    /// Returns a new FloatingSeq with active indices in the range [start, length). The entries
    /// in the active indices are populated using a caller-provided lambda, which should map
    /// active indices to the element that should populate that index.
    pub open spec(checked) fn new(start: nat, length: nat, f: FnSpec(int) -> T) -> FloatingSeq<T>
        recommends
            start <= length,
    {
        FloatingSeq {
            start: start,
            entries: Seq::new((length - start) as nat, |i: int| f(i + start)),
        }
    }

    // TODO if I omit "open" adjective, this file fails to compile!? (Followed, however, by a helpful message
    // about needing 'open' or 'closed'). Tony: As per the guide, spec(checked) funcs must be marked either open or closed
    // Returns the number of indices "occupied", *including* the empty space at
    // the beginning of the index space (i.e.: indices [0,start)).
    pub open spec(checked) fn len(self) -> int {
        self.start as int + self.entries.len()
    }

    pub open spec(checked) fn first_active_index(self) -> int {
        self.start as int
    }

    pub open spec(checked) fn is_active(self, i: int) -> bool {
        self.start <= i < self.len()
    }

    pub open spec(checked) fn get(self, i: int) -> T
        recommends
            self.is_active(i),
    {
        self.entries[i - self.start as int]
    }

    // You can only index values after the empty space.
    // Overrides the `[]` operator
    pub open spec(checked) fn spec_index(self, i: int) -> T
        recommends
            self.is_active(i),
    {
        self.entries[i - self.start]
    }

    /// Return a FloatingSeq containing the elements of this seq in the range
    /// [start, end_idx). (Note however for all FloatingSeq's we interpret all the
    /// empty indices [0, start) as "occupied"; they just represent forgotten
    /// values).
    /// i.e.: chop off all elements at index end_idx and beyond. (end_idx is
    /// in the "absolute space", FloatingSeq handles translation).
    pub open spec(checked) fn get_prefix(self, end_idx: int) -> FloatingSeq<T>
        recommends
            0 <= end_idx <= self.len(),
    {
        if end_idx <= self.start {
            FloatingSeq { start: end_idx as nat, entries: seq![] }
        }// TODO(chris): is there a slice syntax I could use instead of subrange? Chris says: should
        // be, just isn't done yet.
         else {
            FloatingSeq {
                start: self.start,
                entries: self.entries.subrange(0, end_idx - self.start),
            }
        }
    }

    /// Return a FloatingSeq containing the elements of this FloatingSeq in the range
    /// [newStart, self.len()).
    pub open spec(checked) fn get_suffix(self, newStart: int) -> FloatingSeq<T>
        recommends
            self.is_active(newStart) || newStart == self.len(),
    {
        // This datatype doesn't have a "RightSlice" operator because the intent is
        // that object indices don't move; the origin stays put. The closest analog
        // is this GetSuffix operation, which forgets some of the `entries`,
        // remembering only how many there used to be (in `start`), so that the
        // offsets of the surviving entries don't change.
        FloatingSeq {
            start: newStart as nat,
            entries: self.entries.subrange(newStart - self.start, self.entries.len() as int),
        }
    }

    pub open spec(checked) fn append(self, elts: Seq<T>) -> FloatingSeq<T> {
        FloatingSeq { start: self.start, entries: self.entries + elts }
    }

    pub open spec(checked) fn last(self) -> T
        recommends
            self.len() > 0,
            self.is_active(self.len() - 1),
    {
        self[self.len() - 1]
    }

    pub open spec(checked) fn drop_last(self) -> FloatingSeq<T>
        recommends
            self.len() > 0,
    {
        self.get_prefix(self.len() - 1)
    }

    // ext_equal not implemented here since the generic version can't
    // call ext_equal on T (since trait bounds aren't supported?)
    // pub open spec(checked) fn ext_equal(self, other: FloatingSeq<T>) -> bool
    // {
    //     &&& self.start == other.start
    //     &&& self.len() == other.len()
    //     &&& forall |i| self.is_active(i) ==> self[i] == other[i]
    // }
    pub proof fn extensionality(self, b: FloatingSeq<T>)
        requires
            self.start == b.start,
            self.len() == b.len(),
            forall|i| self.is_active(i) ==> self[i] == b[i],
        ensures
            self == b,
    {
        // TODO(jonh): post on slack
        /*
        assert forall foo by {
        }
        assert forall foo opening {
        }

        assert(thing-i-want-to-assert) strategy

        assert(thing-i-want-to-assert);
        assert(thing-i-want-to-assert) by {
            terms
        }
        assert(thing-i-want-to-assert) by opening {
            introduces skolem, lhs of implication
        }

        assert a ==> b open {
            assert a;
        }
        assert a ==> b ==> c open {
            assert a;
        }
        // (that's "intros" in coq)
        assert(forall |i| P(i) ==> forall |j| Q(j) ==> R(i,j)) by opening {
            // you now have
            i,
            P(i),
            j,
            Q(j)
        }


        assert(forall |i: int| i < i+1) by {};

        assert forall ... by {
        }


        forall foo ensures bar {
        }
        */
        assert forall|i| 0 <= i < self.entries.len() implies self.entries[i] === b.entries[i] by {
            // "implies" introduces the assumption explicitly inside the assert context
            assert(b[(self.start + i)] === b.entries[i]);  // by math
        }
        assert(self.entries =~= (b.entries));  // tickle seq extn
    }
}

impl FloatingSeq<Version> {
    pub open spec(checked) fn ext_equal(self, other: FloatingSeq<Version>) -> bool {
        &&& self.start == other.start
        &&& self.len() == other.len()
        &&& forall|i|
            self.is_active(i) ==> #[trigger]
            self[i].ext_equal(other[i])
    }

    // Sanity check that extensional equality is correctly defined + need
    // this lemma for when "==" equality is needed
    pub proof fn ext_equal_is_equality()
        ensures
            forall|a: FloatingSeq<Version>, b: FloatingSeq<Version>| a.ext_equal(b) == (a == b),
    {
        Version::ext_equal_is_equality();
        assert forall|s1: FloatingSeq<Version>, s2: FloatingSeq<Version>| s1.ext_equal(s2) implies (
        s1 == s2) by {
            // Necessary trigger for it to believe that s1[i] == s2[i] for
            // all active indices
            assert(forall|i| #[trigger] s1.is_active(i) ==> s1[i].ext_equal(s2[i]));
            s1.extensionality(s2);
        }
    }
}

} // verus!
