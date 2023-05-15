#![allow(unused_imports)]
use builtin::*;

use builtin_macros::*;

use vstd::{*,map::*,seq::*,set::*};
use crate::spec::KeyType_t::*;

verus! {

#[is_variant]
pub enum Domain {
    EmptyDomain,
    Domain{ 
        start: Element, 
        end: Element},
}

impl Domain {
    pub open spec fn wf(self) -> bool
    {
        &&& self.is_Domain() ==> {
            &&& Element::lt(self.get_Domain_start(), self.get_Domain_end())
            &&& self.get_Domain_start().is_Elem()
            // Note(Jialin): skipping elementIsKey since we are integrating element to contain key sized elements
        }
    }

    pub open spec fn contains(self, key: Key) -> bool
    {
        &&& self.is_Domain()
        &&& Element::lte(self.get_Domain_start(), to_element(key))
        &&& Element::lt(to_element(key), self.get_Domain_end())
    }

    pub open spec fn key_set(self) -> Set<Key>
    {
        Set::new( |k| self.contains(k) )
    }

    pub open spec fn total_domain() -> Domain
    {
        Domain::Domain{start: Element::min_elem(), end: Element::Max}
    }
} // end impl Domain
}  // end verus!