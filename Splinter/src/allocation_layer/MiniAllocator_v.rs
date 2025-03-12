// Copyright 2018-2024 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, University of Washington
// SPDX-License-Identifier: BSD-2-Clause
//
#![allow(unused_imports)]
use builtin::*;
use builtin_macros::*;
use vstd::prelude::*;
use crate::disk::GenericDisk_v::*;

verus! {

pub struct PageAllocator {
    pub observed: Set<Address>, // pages reachable from superblock Repr 
    pub reserved: Set<Address>, // pages reachable from stack ref
    pub au: AU,
}

// TODO: observed <= reserved

impl PageAllocator {
    pub open spec(checked) fn new(au: AU) -> Self {
        Self{observed: Set::empty(), reserved: Set::empty(), au}
    }

    pub open spec(checked) fn wf(self) -> bool {
        // && observed !! reserved // does not have to be disjoint, cow case
        // && |observed + reserved| <= PageCount()
// This is a nasty trigger choice that demands some manual triggerin'
//         &&& (forall |addr| (#[trigger] (self.observed + self.reserved).contains(addr)) ==> addr.wf())
//         &&& (forall |addr| #[trigger] (self.observed + self.reserved).contains(addr) ==> addr.au == self.au)
        &&& (forall |addr| #![auto] self.observed.contains(addr) ==> addr.wf())
        &&& (forall |addr| #![auto] self.reserved.contains(addr) ==> addr.wf())
        &&& (forall |addr| #![auto] self.observed.contains(addr) ==> addr.au == self.au)
        &&& (forall |addr| #![auto] self.reserved.contains(addr) ==> addr.au == self.au)
    }

    pub open spec(checked) fn is_free_addr(self, addr: Address) -> bool {
        &&& addr.wf()
        &&& addr.au == self.au
        &&& !(self.observed + self.reserved).contains(addr)
    }

    /// get a stack reference
    pub open spec(checked) fn reserve(self, addrs: Set<Address>) -> (out: Self)
    recommends
        self.wf(),
        forall |addr| addrs.contains(addr) ==> self.is_free_addr(addr),
    // ensures out.wf()
    {
        Self{reserved: self.reserved + addrs, ..self}
    }

    /// done with / returns a stack reference 
    pub open spec(checked) fn unreserve(self, addrs: Set<Address>) -> (out: Self)
    recommends
        self.wf(),
        addrs.subset_of(self.reserved),  // ensures out.wf()

    {
        Self{reserved: self.reserved.difference(addrs), ..self}
    }

    pub open spec(checked) fn observe(self, addrs: Set<Address>) -> (out: Self)
    recommends
        self.wf(),
        forall |addr| #[trigger] addrs.contains(addr) ==> addr.wf() && addr.au == self.au,
    // ensures out.wf()
    {
        Self{observed: self.observed+addrs, ..self}
    }

    //     pub proof fn observe_wf(self, addrs: Set<Address>)
    //     requires
    //             self.wf(),
    //             forall |addr| #[trigger] addrs.contains(addr) ==> addr.wf() && addr.au == self.au,
    //     ensures self.observe(addrs).wf(),
    //     {
    // //         let out = self.observe(addrs);
    // //         assert forall |ax| (#[trigger] (out.observed + out.reserved).contains(ax))
    // //             implies ax.wf() by {
    // //             if addrs.contains(ax) {
    // //                 assert( ax.wf() );
    // //             } else {
    // //                 assert( (self.observed + self.reserved).contains(ax) );
    // //                 assert( ax.wf() );
    // //             }
    // //         }
    // //         assert forall |ax| #[trigger] (out.observed + out.reserved).contains(ax)
    // //             implies ax.au == out.au by {
    // //         }
    //     }

    pub open spec(checked) fn unobserve(self, addrs: Set<Address>) -> (out: Self)
    recommends
            self.wf(),
            addrs.subset_of(self.observed),
    // ensures out.wf()
    {
        Self{observed: self.observed.difference(addrs), ..self}
    }

    pub open spec(checked) fn unobserve_all(self) -> (out: Self)
    recommends
            self.wf(),
    // ensures out.wf()
    {
        self.unobserve(self.observed)
    }

    pub open spec(checked) fn free(self, addrs: Set<Address>) -> (out: Self)
    recommends
            self.wf(),
            addrs.subset_of(self.observed + self.reserved),  // ensures out.wf()
    {
        Self{observed: self.observed.difference(addrs), reserved: self.reserved.difference(addrs), au: self.au}
    }

    pub open spec(checked) fn has_no_observed_pages(self) -> bool {
        &&& self.observed == Set::<Address>::empty()    // type inference failure
    }

    pub open spec(checked) fn has_no_outstanding_refs(self) -> bool {
        &&& self.reserved == Set::<Address>::empty()    // type inference failure
    }

    pub open spec(checked) fn all_pages_allocated(self) -> bool {
        forall |addr: Address| #![auto] addr.wf() && addr.au == self.au 
            ==> ( self.reserved.contains(addr) || self.observed.contains(addr) )
        // &&& (self.reserved + self.observed).len() == page_count()
    }

    pub open spec(checked) fn all_pages_free(self) -> bool {
        &&& self.has_no_observed_pages()
        &&& self.has_no_outstanding_refs()
    }
}

pub struct MiniAllocator {
    pub allocs: Map<AU, PageAllocator>,
    pub curr: Option<AU>,
}

impl MiniAllocator {
    pub open spec(checked) fn empty() -> Self {
        Self{allocs: Map::empty(), curr: None}
    }

    pub open spec(checked) fn wf(self) -> bool {
        &&& forall |au| #[trigger] self.allocs.contains_key(au) ==> self.allocs[au].wf() && self.allocs[au].au == au
        &&& self.curr is Some ==> self.allocs.contains_key(self.curr.unwrap())
    }

    pub open spec(checked) fn add_aus(self, aus: Set<AU>) -> Self
        recommends
            self.wf(),  // ensures out.wf()
    {
        let new_allocs = Map::new(
            |au| (aus+self.allocs.dom()).contains(au),
            |au| if self.allocs.contains_key(au) { self.allocs[au] }
                else { PageAllocator::new(au) });
        Self{allocs: new_allocs, ..self}
    }

    // mini allocator's job is to allocate freespace and manage reserved pages
    // as long as there are no reserved pages, it can be safely removed from the mini allocator
    pub open spec(checked) fn can_remove(self, au: AU) -> bool {
        &&& self.allocs.contains_key(au)
        &&& self.allocs[au].has_no_outstanding_refs()
    }

    // a set of AUs that belongs to the frozen freeset
    pub open spec(checked) fn not_observed_aus(self) -> Set<AU>
    {
        Set::new(|au| self.allocs.contains_key(au) && self.allocs[au].has_no_observed_pages())
    }

    pub open spec(checked) fn can_allocate(self, addr: Address) -> bool
    {
        &&& self.allocs.contains_key(addr.au)
        &&& self.allocs[addr.au].is_free_addr(addr)
    }

    pub open spec(checked) fn allocate(self, addr: Address) -> Self
        recommends
            self.wf(),
            self.can_allocate(addr),  // ensures out.wf()
    {
        let result = self.allocs[addr.au].reserve(set![addr]);
        let new_curr = if result.all_pages_allocated() { None } else { Some(addr.au) };
        Self{ allocs: self.allocs.insert(addr.au, result), curr: new_curr }
    }

    pub open spec(checked) fn observe(self, addr: Address) -> Self
        recommends
            self.wf(),
            self.allocs.contains_key(addr.au),
            self.allocs[addr.au].reserved.contains(addr),
    {
        let result = self.allocs[addr.au].observe(set![addr]);
        Self{ allocs: self.allocs.insert(addr.au, result), ..self }
    }

    pub open spec/*(checked)*/ fn prune(self, aus: Set<AU>) -> Self
    recommends
        self.wf(),
    {
        // let new_allocs = Map::new(
        //     |au| self.allocs.contains_key(au) && !aus.contains(au),
        //     |au| self.allocs[au]);

        let new_allocs = self.allocs.remove_keys(aus);
        let new_curr = if self.curr is Some && aus.contains(self.curr.unwrap()) 
                        { None } else { self.curr };

        Self{allocs: new_allocs, curr: new_curr}
    }

    pub open spec fn page_is_reserved(self, addr: Address) -> bool
    {
        &&& self.allocs.contains_key(addr.au)
        &&& self.allocs[addr.au].reserved.contains(addr)
    }

    pub open spec fn reserved_aus(self) -> Set<AU>
    {
        Set::new(|au| self.allocs.contains_key(au) && !self.allocs[au].has_no_outstanding_refs())
    }

    pub open spec fn removable_aus(self) -> Set<AU>
    {
        Set::new(|au| self.can_remove(au))
    }

    pub open spec fn all_aus(self) -> Set<AU>
    {
        self.allocs.dom()
    }
}

}  // end verus!
