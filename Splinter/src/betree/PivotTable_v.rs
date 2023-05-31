#![allow(unused_imports)]
use builtin::*;
use builtin_macros::*;

use vstd::{*,map::*,seq::*,set::*};
use crate::spec::KeyType_t::*;
use crate::betree::Domain_v::*;

verus! {

// Provides definitions and libraries for pivot tables. A pivot
// table is a sorted list of *pivot* keys that divides the keyspace into
// contiguous ranges.

// A PivotTable of length n breaks the keyspace into n-1 "buckets"
// For 0 <= i < n-1 then the buckets are [a_i, a_i+1) ... 
// Each bucket must be nonempty.

// Elements are used for providing an upperbound for the keys
// Everything besides the last node cannot be maximum

pub struct PivotTable {
    pub pivots: Seq<Element>
}

pub open spec fn domain_to_pivots(domain: Domain) -> PivotTable
{
    PivotTable{pivots: Seq::empty().push(domain.get_Domain_start()).push(domain.get_Domain_end())}
}

impl PivotTable {
    // equivalent to dafny boundedpivots's numbuckets
    pub open spec fn num_ranges(self) -> int 
    {
        self.pivots.len() - 1
    }

    pub open spec fn wf(self) -> bool
    {
        &&& self.num_ranges() > 0
        &&& Element::is_strictly_sorted(self.pivots)
        &&& (forall |i: int| 0 <= i < self.num_ranges() ==> self.pivots[i].is_Elem())
    }

    pub open spec fn len(self) -> nat
    {
        self.pivots.len()
    }

    pub open spec fn update(self, i: int, element: Element) -> PivotTable
    {
        PivotTable{pivots: self.pivots.update(i, element)}
    }

    pub open spec fn subrange(self, start: int, end: int) -> PivotTable
    {
        PivotTable{pivots: self.pivots.subrange(start, end)}
    }

    pub open spec fn insert(self, i: int, element: Element) -> PivotTable
    {
        PivotTable{pivots: self.pivots.insert(i, element)}
    }

    pub open spec fn bounded_key(self, key: Key) -> bool
    {
        &&& Element::lte(self.pivots[0], to_element(key))
        &&& Element::lt(to_element(key), self.pivots.last())
    }

    pub open spec fn route(self, key: Key) -> int
        recommends self.bounded_key(key)
    {
        Element::largest_lte(self.pivots, to_element(key))
    }

    pub proof fn route_lemma(self, key: Key)
        requires self.wf(), self.bounded_key(key)
        ensures 0 <= self.route(key) < self.num_ranges()
    {
        Element::lte_transitive_forall();
        Element::strictly_sorted_implies_sorted(self.pivots);
        Element::largest_lte_lemma(self.pivots, to_element(key), self.route(key));
    }
} // end impl PivotTable
}  // end verus!