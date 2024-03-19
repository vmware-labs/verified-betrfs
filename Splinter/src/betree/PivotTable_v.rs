// Copyright 2018-2023 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, University of Washington
// SPDX-License-Identifier: BSD-2-Clause
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
// Only the last node can be Element::Max.

pub struct PivotTable {
    pub pivots: Seq<Element>
}

pub open spec(checked) fn domain_to_pivots(domain: Domain) -> PivotTable
{
    PivotTable{pivots: seq![domain->start, domain->end]}
}

impl PivotTable {
    // equivalent to dafny boundedpivots's numbuckets
    pub open spec(checked) fn num_ranges(self) -> int 
    {
        self.pivots.len() - 1
    }

    pub open spec(checked) fn wf(self) -> bool
    {
        &&& self.num_ranges() > 0
        &&& Element::is_strictly_sorted(self.pivots)
        &&& (forall |i: int| 0 <= i < self.num_ranges() ==> (#[trigger] self.pivots[i] is Elem))
    }

    pub open spec(checked) fn len(self) -> nat
    {
        self.pivots.len()
    }

    #[verifier(inline)]
    pub open spec(checked) fn spec_index(self, i: int) -> Element
        recommends 0 <= i < self.len()
    {
        self.pivots[i]
    }

    pub open spec(checked) fn update(self, i: int, element: Element) -> PivotTable
        recommends 0 <= i < self.len()
    {
        PivotTable{pivots: self.pivots.update(i, element)}
    }

    pub open spec(checked) fn subrange(self, start: int, end: int) -> PivotTable
        recommends 0 <= start <= end <= self.len()
    {
        PivotTable{pivots: self.pivots.subrange(start, end)}
    }

    pub open spec(checked) fn can_insert(self, i: int, element: Element) -> bool
    {
        &&& self.wf()
        &&& element is Elem
        &&& 0 <= i <= self.len()
        &&& (i == 0 ==> Element::lt(element, self.pivots[0]))
        &&& (i == self.len() ==> Element::lt(self.pivots.last(), element))
        &&& (0 < i && i < self.len() ==> Element::lt(self.pivots[i-1], element) && Element::lt(element, self.pivots[i]))
    }

    pub open spec(checked) fn insert(self, i: int, element: Element) -> PivotTable
        recommends self.can_insert(i, element)
    {
        PivotTable{pivots: self.pivots.insert(i, element)}
    }

    pub proof fn insert_wf(self, idx: int, element: Element) 
        requires self.wf(), self.can_insert(idx, element)
        ensures self.insert(idx, element).wf()
    {
        let result = self.insert(idx, element).pivots;
        Element::lte_transitive_forall();

        assert forall |i: int, j: int| 0 <= i < j < result.len() 
        implies Element::lt(result[i], result[j])
        by {
            if i == idx && j > i + 1 {
                assert(Element::lt(result[i+1], result[j])); // trigger
            } else if i < idx-1 && j == idx {
                assert(Element::lt(result[i], result[j-1])); // trigger
            }
        }
    }
  
    pub open spec(checked) fn bounded_key(self, key: Key) -> bool
    recommends
        self.wf(),
    {
        &&& Element::lte(self.pivots[0], to_element(key))
        &&& Element::lt(to_element(key), self.pivots.last())
    }

    pub open spec(checked) fn route(self, key: Key) -> int
    recommends
        self.wf(),
        self.bounded_key(key),
    {
        Element::largest_lte(self.pivots, to_element(key))
    }

    pub proof fn route_lemma(self, key: Key)
        requires self.wf(), self.bounded_key(key)
        ensures 0 <= self.route(key) < self.num_ranges(),
            Element::lte(self.pivots[self.route(key)], to_element(key)),
            Element::lt(to_element(key), self.pivots[self.route(key)+1])
    {
        Element::strictly_sorted_implies_sorted(self.pivots);
        Element::largest_lte_lemma(self.pivots, to_element(key), self.route(key));
    }

    pub proof fn route_lemma_auto()
        ensures forall |pt: PivotTable, key: Key| pt.wf() && pt.bounded_key(key)
        ==> {
            &&& 0 <= #[trigger] pt.route(key) < pt.num_ranges()
            &&& Element::lte(pt.pivots[pt.route(key)], to_element(key))
            &&& Element::lt(to_element(key), pt.pivots[pt.route(key)+1])
        }
    {
        assert forall |pt: PivotTable, key: Key| pt.wf() && pt.bounded_key(key)
        implies {
            &&& 0 <= #[trigger] pt.route(key) < pt.num_ranges()
            &&& Element::lte(pt.pivots[pt.route(key)], to_element(key))
            &&& Element::lt(to_element(key), pt.pivots[pt.route(key)+1])
        } by {
            pt.route_lemma(key);
        }
    } 

    pub proof fn route_is_lemma(self, key: Key, r: int)
        requires self.wf(), 0 <= r < self.num_ranges(),
            Element::lte(self.pivots[r], to_element(key)),
            Element::lt(to_element(key), self.pivots[r+1])
        ensures self.bounded_key(key), self.route(key) == r
    {
        Element::strictly_sorted_implies_sorted(self.pivots);
        Element::largest_lte_lemma(self.pivots, to_element(key), self.route(key));
    }

    pub proof fn route_is_lemma_auto()
        ensures forall |pt: PivotTable, key: Key, r: int| 
        {
            &&& pt.wf() && 0 <= r < pt.num_ranges()
            &&& Element::lte(pt.pivots[r], to_element(key))
            &&& Element::lt(to_element(key), pt.pivots[r+1])
        }
        ==> {
            &&& pt.bounded_key(key)
            &&& pt.route(key) == r
        }
    {
        assert forall |pt: PivotTable, key: Key, r: int| 
        {
            &&& pt.wf() && 0 <= r < pt.num_ranges()
            &&& Element::lte(pt.pivots[r], to_element(key))
            &&& Element::lt(to_element(key), pt.pivots[r+1])
        } implies {
            &&& pt.bounded_key(key) 
            &&& pt.route(key) == r
        } by { pt.route_is_lemma(key, r); }
    } 

    pub open spec(checked) fn pivot_range_keyset(self, i: int) -> Set<Key>
        recommends self.wf(), 0 <= i < self.num_ranges()
    {
        Set::new(|k: Key| self.bounded_key(k) && self.route(k) == i)
    }
} // end impl PivotTable
}  // end verus!
