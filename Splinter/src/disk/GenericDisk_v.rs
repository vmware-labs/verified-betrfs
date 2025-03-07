// Copyright 2018-2024 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, University of Washington
// SPDX-License-Identifier: BSD-2-Clause

//! This file contains types relating to generic disk addressing and referencing.

#[allow(unused_imports)]
use builtin::*;
use builtin_macros::*;
use vstd::prelude::*;
use vstd::map_lib::*;

use crate::spec::AsyncDisk_t;
use crate::spec::ImplDisk_t;

verus!{

/// Exporting from trusted disk model
pub type AU = AsyncDisk_t::AU;
pub type Page = AsyncDisk_t::Page;
pub type Address = AsyncDisk_t::Address;

pub type IAU = ImplDisk_t::IAU;
pub type IPage = ImplDisk_t::IPage;
pub type IAddress = ImplDisk_t::IAddress;

pub open spec(checked) fn page_count() -> Page
{
    AsyncDisk_t::page_count()
}

pub open spec(checked) fn au_count() -> AU
{
    AsyncDisk_t::au_count()
}

impl Address {
    /// Returns the Address for the first page of this AU.
    pub open spec(checked) fn first_page(self) -> Address {
        Address{page: 0, ..self}
    }

    /// Returns the previous Address in this AU (may not be well-formed).
    pub open spec(checked) fn previous(self) -> Address {
        Address{page: (self.page-1) as nat, ..self}
    }
    
    /// Returns the next Address in this AU (may not be well-formed).
    pub open spec(checked) fn next(self) -> Address {
        Address{page: self.page+1, ..self}
    }

    // Returns true for WF addresses within the same AU but after self
    pub open spec(checked) fn after_page(self, addr: Self) -> bool {
        &&& addr.wf()
        &&& addr.au == self.au
        &&& addr.page > self.page
    }
}

pub open spec(checked) fn first_page(ptr: Pointer) -> Pointer {
    match ptr {
        None => None,
        Some(addr) => Some(addr.first_page()),
    }
}

/// Return the lowest of two addresses. Addresses are first compared by AU,
/// then by Page index (if AUs match).
pub open spec(checked) fn min_addr(a: Address, b: Address) -> Address {
    if a.au < b.au { a }
    else if a.au > b.au { b }
    else if a.page <= b.page { a }
    else { b }
}

/// Returns the set of AUs that the provided set of Addresses live in.
pub open spec(checked) fn to_aus(addrs: Set<Address>) -> Set<AU> 
    // decreases addrs.len() when addrs.finite()
{
    Map::new(|addr| addrs.contains(addr), |addr: Address| addr.au).values()
}

pub proof fn to_aus_finite(addrs: Set<Address>)
    requires addrs.finite()
    ensures to_aus(addrs).finite()
{
    let m = Map::new(|addr| addrs.contains(addr), |addr: Address| addr.au);
    assert(m.dom() == addrs);
    lemma_values_finite(m);
}

pub proof fn to_aus_singleton(addr: Address) 
    ensures to_aus(set!{addr}) == set!{addr.au}
{
    let s = set!{addr};
    let m = Map::new(|addr| s.contains(addr), |addr: Address| addr.au);

    assert(m.dom() == s);
    assert(m[addr] == addr.au);
    assert(m.values().contains(addr.au));
    assert(set!{addr.au} =~= m.values());
}

pub proof fn to_aus_additive(addrs: Set<Address>, other_addrs: Set<Address>) 
    ensures to_aus(addrs + other_addrs) == to_aus(addrs) + to_aus(other_addrs)
{
    let total = addrs + other_addrs;
    let m_total = Map::new(|addr| total.contains(addr), |addr: Address| addr.au);
    let m_addrs = Map::new(|addr| addrs.contains(addr), |addr: Address| addr.au);
    let m_other_addrs = Map::new(|addr| other_addrs.contains(addr), |addr: Address| addr.au);

    assert(m_total.dom() == total);
    assert(m_addrs.dom() == addrs);
    assert(m_other_addrs.dom() == other_addrs);

    assert forall |au| #[trigger] m_total.values().contains(au) <==> 
        (m_addrs.values() + m_other_addrs.values()).contains(au)
    by {
        if m_total.values().contains(au) {
            let addr = choose |addr| #[trigger] m_total.contains_key(addr) && m_total[addr] == addr.au;
            assert(m_addrs.contains_key(addr) || m_other_addrs.contains_key(addr));
            assert(m_addrs.values().contains(addr.au) || m_other_addrs.values().contains(addr.au));
        }

        if (m_addrs.values() + m_other_addrs.values()).contains(au) {
            if m_addrs.values().contains(au) {
                let addr = choose |addr| #[trigger] m_addrs.contains_key(addr) && m_addrs[addr] == au;
                assert(m_total.contains_key(addr));
                assert(m_total[addr] == addr.au);
            } else {
                assert(m_other_addrs.values().contains(au));
                let addr = choose |addr| #[trigger] m_other_addrs.contains_key(addr) && m_other_addrs[addr] == au;
                assert(m_total.contains_key(addr));
                assert(m_total[addr] == addr.au);
            }
        }
    }
    assert(m_total.values() =~= m_addrs.values() + m_other_addrs.values());
}

pub open spec(checked) fn addr_range(au: IAU, start: IPage, end_excl: IPage) -> (addrs: Set<Address>) {
    Set::new(|addr: Address| {
        &&& addr.au == au 
        &&& addr.page >= start 
        &&& addr.page < end_excl
    })
}

impl View for IAddress {
    type V = Address;

    open spec fn view(&self) -> Self::V
    {
        Address{au: self.au as nat, page: self.page as nat}
    }
}

/// A Pointer is either an Address or None. (i.e.: we wrap Address with the semantics for
/// "NULL" pointers). Used when certain data structures might have unallocated pointers.
pub type Pointer = Option<Address>;
pub type Ranking = Map<Address, nat>;   // Used by Linked* layers to show acyclicity.

}
