// Copyright 2018-2024 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, University of Washington
// SPDX-License-Identifier: BSD-2-Clause
//
#![allow(unused_imports)]
use builtin::*;
use builtin_macros::*;
use vstd::prelude::*;

use crate::disk::GenericDisk_v::*;
use crate::allocation_layer::MiniAllocator_v;

verus! {

broadcast use crate::spec::ImplDisk_t::page_count_equals_ipage_count;

pub struct PageAllocator {
    pub observed: IPage, // pages from [0, observed) are reachable from superblock Repr 
    pub reserved: IPage, // pages from [observed, reserved) are reachable from stack ref
    pub au: IAU,
}

impl View for PageAllocator {
    type V = MiniAllocator_v::PageAllocator; // view lifts it to a model

    open spec fn view(&self) -> Self::V
    {
        let au = self.au as nat;
        let observed = addr_range(self.au, 0, self.observed);
        let reserved = addr_range(self.au, 0, self.reserved);

        MiniAllocator_v::PageAllocator{observed, reserved, au}
    }
}

impl PageAllocator {
    pub exec fn new(au: IAU) -> (alloc: Self) 
        requires au < au_count()
        ensures alloc.wf()
    {
        Self{observed: 0, reserved: 0, au}
    }

    pub open spec(checked) fn wf(self) -> bool {
        &&& self.observed <= self.reserved
        &&& self.reserved <= page_count()
        &&& self.au < au_count()
    }

    pub open spec(checked) fn has_free_addr(self) -> bool {
        &&& self.reserved != page_count()
    }

    pub open spec(checked) fn no_unobserved_pages(self) -> bool {
        self.reserved == self.observed
    }

    /// get a stack reference
    pub exec fn reserve(&mut self) -> (addr: IAddress)
    requires
        old(self).wf(),
        old(self).has_free_addr(),
    ensures 
        self.wf(),
        addr@.wf(),
        addr.page < self.reserved,
        old(self)@.is_free_addr(addr@),
        self@ == old(self)@.reserve(set![addr@]),
    {
        let addr = IAddress{au: self.au, page: self.reserved};
        self.reserved = self.reserved+1;
        assert(old(self)@.reserved + set![addr@] =~= self@.reserved);
        addr
    }

    pub exec fn observe_all(&mut self)
        requires old(self).wf(),
        ensures
            self.wf(),
            self.no_unobserved_pages(),
            self.reserved == old(self).reserved,
            self@ == old(self)@.observe(old(self)@.reserved),
    {
        self.observed = self.reserved;
        assert(old(self)@.observed + old(self)@.reserved =~= self@.observed);
    }

    proof fn free_addr_implies_not_all_allocated(&self)
        requires self.wf()
        ensures self.has_free_addr() == !self@.all_pages_allocated()
    {
        if self.has_free_addr() {
            let addr = IAddress{au: self.au, page: self.reserved};
            assert(self@.is_free_addr(addr@));
        }
    }
}

pub struct MiniAllocator {
    pub allocs: Option<PageAllocator>, // TODO: array later?
}

impl View for MiniAllocator {
    type V = MiniAllocator_v::MiniAllocator;

    open spec fn view(&self) -> Self::V
    {
        match self.allocs {
            Some(alloc) => {
                let allocs = map![alloc@.au => alloc@];
                let curr = if alloc.has_free_addr() { Some(alloc@.au) } else { None };
                MiniAllocator_v::MiniAllocator{allocs, curr}
            }
            None => Self::V::empty(),
        }
    }
}

impl MiniAllocator {
    pub exec fn empty() -> Self {
        Self{allocs: None}
    }

    pub open spec(checked) fn wf(self) -> bool {
        &&& self.allocs is Some ==> self.allocs.unwrap().wf()
    }

    pub exec fn add_aus(&mut self, au: IAU)
        requires 
            old(self).wf(), 
            old(self).allocs is None,
            au < au_count(),
        ensures self.wf()
    {
        let page_allocator = PageAllocator::new(au);
        self.allocs = Some(page_allocator);
    }

    // used by journal to allocate and observe
    pub exec fn allocate_and_observe(&mut self) -> (addr: IAddress)
        requires
            old(self).wf(),
            old(self).allocs is Some,
            old(self).allocs.unwrap().has_free_addr(),
            old(self).allocs.unwrap().no_unobserved_pages(),
        ensures
            self.wf(),
            self.allocs is Some,
            self.allocs.unwrap().no_unobserved_pages(),
            addr@.wf(),
            self@ == old(self)@.allocate(addr@).observe(addr@),
    {
        // NOTE: AWAITING support for as_mut expected code
        // ===============================================
        // let alloc = self.allocs.as_mut().unwrap();
        // let addr = alloc.reserve();
        // alloc.observe_upto(addr.page + 1);
        // ===============================================

        // workaround in the meantime
    
        let mut tmp = None;
        std::mem::swap(&mut self.allocs, &mut tmp);

        let mut alloc = tmp.unwrap();
        let addr = alloc.reserve();
        let ghost post_reserve = alloc;

        alloc.observe_all();
        tmp = Some(alloc);
        std::mem::swap(&mut self.allocs, &mut tmp);

        proof {
            let v = old(self)@.allocate(addr@).observe(addr@);
            assert(self@.allocs =~= v.allocs);
    
            post_reserve.free_addr_implies_not_all_allocated();
//            assert(self@.curr == v.curr);        
        }

        addr
    }

    pub exec fn prune(&mut self)
    requires
        old(self).wf(),
        old(self).allocs is Some,
    ensures 
        self.allocs is None,
        self@ == old(self)@.prune(set![old(self).allocs.unwrap()@.au])
    {
        let ghost v = old(self)@.prune(set![old(self).allocs.unwrap()@.au]);
        self.allocs = None;
        assert(self@.allocs =~= v.allocs);
    }
}
}  // end verus!
