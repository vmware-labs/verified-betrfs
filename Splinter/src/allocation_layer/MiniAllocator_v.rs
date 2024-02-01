// Copyright 2018-2023 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, University of Washington
// SPDX-License-Identifier: BSD-2-Clause
//
#![allow(unused_imports)]
use crate::disk::GenericDisk_v::*;
use builtin::*;
use builtin_macros::*;
use vstd::prelude::*;

verus! {

pub struct PageAllocator {
    pub observed: Set<Address>,  // pages reachable from superblock Repr
    pub reserved: Set<Address>,  // pages reachable from stack ref
    pub au: AU,
}

impl PageAllocator {
    pub open spec(checked) fn new(au: AU) -> Self {
        Self { observed: Set::empty(), reserved: Set::empty(), au }
    }

    pub open spec(checked) fn wf(self) -> bool {
        // && observed !! reserved // does not have to be disjoint, cow case
        // && |observed + reserved| <= PageCount()
        // This is a nasty trigger choice that demands some manual triggerin'
        //         &&& (forall |addr| (#[trigger] (self.observed + self.reserved).contains(addr)) ==> addr.wf())
        //         &&& (forall |addr| #[trigger] (self.observed + self.reserved).contains(addr) ==> addr.au == self.au)
        &&& (forall|addr| #![auto] self.observed.contains(addr) ==> addr.wf())
        &&& (forall|addr| #![auto] self.reserved.contains(addr) ==> addr.wf())
        &&& (forall|addr| #![auto] self.observed.contains(addr) ==> addr.au == self.au)
        &&& (forall|addr| #![auto] self.reserved.contains(addr) ==> addr.au == self.au)
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
            forall|addr|
                addrs.contains(addr) ==> self.is_free_addr(
                    addr,
                ),  // ensures out.wf()

    {
        Self { reserved: self.reserved + addrs, ..self }
    }

    /// done with / returns a stack reference
    pub open spec(checked) fn unreserve(self, addrs: Set<Address>) -> (out: Self)
        recommends
            self.wf(),
            addrs.subset_of(self.reserved),  // ensures out.wf()

    {
        Self { reserved: self.reserved.difference(addrs), ..self }
    }

    pub open spec(checked) fn observe(self, addrs: Set<Address>) -> (out: Self)
        recommends
            self.wf(),
            forall|addr|
                #[trigger]
                addrs.contains(addr) ==> addr.wf() && addr.au
                    == self.au,  // ensures out.wf()

    {
        Self { observed: self.observed + addrs, ..self }
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
            addrs.subset_of(self.observed),  // ensures out.wf()

    {
        Self { observed: self.observed.difference(addrs), ..self }
    }

    pub open spec(checked) fn unobserve_all(self) -> (out: Self)
        recommends
            self.wf(),  // ensures out.wf()

    {
        self.unobserve(self.observed)
    }

    pub open spec(checked) fn free(self, addrs: Set<Address>) -> (out: Self)
        recommends
            self.wf(),
            addrs.subset_of(self.observed + self.reserved),  // ensures out.wf()

    {
        Self {
            observed: self.observed.difference(addrs),
            reserved: self.reserved.difference(addrs),
            au: self.au,
        }
    }

    pub open spec(checked) fn has_no_observed_pages(self) -> bool {
        &&& self.observed == Set::<Address>::empty()  // type inference failure

    }

    pub open spec(checked) fn has_no_outstanding_refs(self) -> bool {
        &&& self.reserved == Set::<Address>::empty()  // type inference failure

    }

    pub open spec(checked) fn all_pages_allocated(self) -> bool {
        &&& (self.reserved + self.observed).len() == page_count()
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
        Self { allocs: Map::empty(), curr: None }
    }

    pub open spec(checked) fn wf(self) -> bool {
        &&& forall|au|
            #[trigger]
            self.allocs.contains_key(au) ==> self.allocs[au].wf() && self.allocs[au].au == au
            &&& self.curr.is_Some() ==> self.allocs.contains_key(self.curr.unwrap())
    }

    pub open spec(checked) fn add_aus(self, aus: Set<AU>) -> Self
        recommends
            self.wf(),  // ensures out.wf()

    {
        let new_allocs = Map::new(
            |au| (aus + self.allocs.dom()).contains(au),
            |au|
                if self.allocs.contains_key(au) {
                    self.allocs[au]
                } else {
                    PageAllocator::new(au)
                },
        );
        Self { allocs: new_allocs, ..self }
    }

    // mini allocator's job is to allocate freespace and manage reserved pages
    // as long as there are no reserved pages, it can be safely removed from the mini allocator
    pub open spec(checked) fn can_remove(self, au: AU) -> bool {
        &&& self.allocs.contains_key(au)
        &&& self.allocs[au].has_no_outstanding_refs()
    }

    // a set of AUs that belongs to the frozen freeset
    pub open spec(checked) fn not_observed_aus(self) -> Set<AU> {
        Set::new(|au| self.allocs.contains_key(au) && self.allocs[au].has_no_observed_pages())
    }

    pub open spec(checked) fn can_allocate(self, addr: Address) -> bool {
        &&& self.allocs.contains_key(addr.au)
        &&& self.allocs[addr.au].is_free_addr(addr)
    }

    pub open spec(checked) fn allocate_and_observe(self, addr: Address) -> Self
        recommends
            self.wf(),
            self.can_allocate(addr),  // ensures out.wf()

    {
        let result = self.allocs[addr.au].observe(set![addr]);
        let new_curr = if result.all_pages_allocated() {
            None
        } else {
            Some(addr.au)
        };
        Self { allocs: self.allocs.insert(addr.au, result), curr: new_curr }
    }

    pub proof fn allocate_and_observe_wf(self, addr: Address)
        requires
            self.wf(),
            self.can_allocate(addr),
            addr.wf(),
        ensures
            self.allocate_and_observe(addr).wf(),
    {
        //         assume( false );
        //         let alloc = self.allocs[addr.au];
        //         let addrs = set![addr];
        //         assert forall |addr| #[trigger] addrs.contains(addr) implies addr.wf() && addr.au == alloc.au by {
        //         }
        //         let presult = self.allocs[addr.au];
        //         assert( presult.wf() );
        //         let result = presult.observe(set![addr]);
        //         assert( result.reserved == presult.reserved );
        //         assert( result.observed == result.observed + set![addr] );
        //         assert forall |addrx| (#[trigger] (result.observed + result.reserved).contains(addrx)) implies addrx.wf() by {
        //             if result.reserved.contains(addrx) {
        //                 assert( (presult.observed + presult.reserved).contains(addr) );
        //                 assert(addrx.wf());
        //             } else {
        //                 assert( result.observed.contains(addrx) );
        //                 if addrx == addr {
        //                     assert(addrx.wf());
        //                 } else {
        //                     assert( (presult.observed + presult.reserved).contains(addr) );
        //                    assert(addrx.wf());
        //                 }
        //             }
        //         }
        //         assert( result.wf() );
        //         let post = self.allocate_and_observe(addr);
        //         assert forall |au| #[trigger] post.allocs.contains_key(au)
        //             implies post.allocs[au].wf() && post.allocs[au].au == au by {
        //             if au == addr.au {
        //                 assert( post.allocs[au] == result );
        //                 assert( result.wf() );
        //                 assert( post.allocs[au].wf() );
        //                 assert( post.allocs[au].au == au );
        //             } else {
        //                 assert( post.allocs[au].wf() );
        //                 assert( post.allocs[au].au == au );
        //             }
        //         }
    }

    pub open spec(checked) fn allocate(self, addr: Address) -> Self
        recommends
            self.wf(),
            self.can_allocate(addr),  // ensures out.wf()

    {
        let result = self.allocs[addr.au].reserve(set![addr]);
        let new_curr = if result.all_pages_allocated() {
            None
        } else {
            Some(addr.au)
        };
        Self { allocs: self.allocs.insert(addr.au, result), curr: new_curr }
    }

    // TODO(jailin): is it okay to prune any old thing? No check necessary?
    // remove AUs from the mini allocator
    // removed (checked) due to total lambda
    pub open spec   /*(checked)*/
    fn prune(self, aus: Set<AU>) -> Self
        recommends
            self.wf(),  // ensures out.wf()
    // ensures out.allocs.dom() == self.alloc.dom() - aus

    {
        let new_allocs = Map::new(
            |au| self.allocs.contains_key(au) && !aus.contains(au),
            |au| self.allocs[au],
        );
        let new_curr = if self.curr.is_Some() && aus.contains(self.curr.unwrap()) {
            None
        } else {
            self.curr
        };
        Self { allocs: new_allocs, curr: new_curr }
    }
}

} // verus!
  // end verus!
