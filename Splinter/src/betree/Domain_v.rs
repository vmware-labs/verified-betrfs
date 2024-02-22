// Copyright 2018-2023 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, University of Washington
// SPDX-License-Identifier: BSD-2-Clause
use builtin_macros::*;
use vstd::set::*;
use crate::spec::KeyType_t::*;

verus! {

pub enum Domain {
    EmptyDomain,
    Domain{ 
        start: Element, 
        end: Element},
}

pub open spec(checked) fn total_domain() -> Domain
{
    Domain::Domain{start: Element::min_elem(), end: Element::Max}
}

impl Domain {
    pub open spec(checked) fn wf(self) -> bool
    {
        &&& self is Domain ==> {
            &&& Element::lt(self->start, self->end)
            &&& self->start.is_Elem()  // Note(Jialin): skipping elementIsKey since we are integrating element to contain key sized elements
        }
    }

    pub open spec(checked) fn contains(self, key: Key) -> bool
    {
        &&& self is Domain
        &&& Element::lte(self->start, to_element(key))
        &&& Element::lt(to_element(key), self->end)
    }

    pub open spec(checked) fn includes(self, other: Self) -> bool
    {
        &&& self is Domain
        &&& other is Domain
        &&& Element::lte(self->start, other->start)
        &&& Element::lte(other->end, self->end)
    }

    pub open spec(checked) fn key_set(self) -> Set<Key>
    {
        Set::new( |k| self.contains(k) )
    }
} // end impl Domain
}  // end verus!