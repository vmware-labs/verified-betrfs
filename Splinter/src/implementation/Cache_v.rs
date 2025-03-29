// Copyright 2018-2024 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, University of Washington
// SPDX-License-Identifier: BSD-2-Clause

#![allow(unused_imports)]
use builtin::*;

use builtin_macros::*;
use state_machines_macros::state_machine;
use vstd::prelude::*;
use vstd::{map::*, map_lib::*, seq::*, set::*};

use crate::spec::AsyncDisk_t::*;
use crate::spec::MapSpec_t::{ID};

verus!{

pub type Slot = i32;

//  Entry is separate from Status because there are some cases
//  where we need to have shared access to the Entry while modifying
//  the Status
pub enum Status {
    NotFilled,
    Clean,
    Dirty,
    Writeback,
}

pub enum Entry {
    Empty,
    Reserved{addr: Address},
    Loading{addr: Address}, 
    Filled{addr: Address, data: RawPage},
}

impl Entry {
    pub open spec(checked) fn get_addr(self) -> Address 
        recommends !(self is Empty)
    {
        match self {
            Entry::Reserved{addr} => { addr }
            Entry::Loading{addr, ..} => { addr }
            Entry::Filled{addr, ..} => { addr }
            _ => arbitrary()
        }
    }
}

state_machine!{ Cache {
    fields {
        pub entries: Map<Slot, Entry>,
        pub status_map: Map<Slot, Status>,
        pub lookup_map: Map<Address, Slot>,
        pub outstanding_reqs: Map<ID, Slot>,
    }

    pub enum Label {
        Access{reads: Map<Address, RawPage>, writes: Map<Address, RawPage>},
        EvictableCheck{addrs: Set<Address>},
        DiskOps{requests: Map<ID, DiskRequest>, responses: Map<ID, DiskResponse>},
        Internal,
    }

    pub open spec fn valid_read(self, addr: Address, data: RawPage) -> bool 
    {
        &&& self.lookup_map.contains_key(addr)
        &&& self.entries[self.lookup_map[addr]] is Filled
        &&& data == self.entries[self.lookup_map[addr]]->data
    }

    pub open spec fn valid_write(self, addr: Address) -> bool 
    {
        &&& self.lookup_map.contains_key(addr) 
        &&& { 
            let slot = self.lookup_map[addr];
            ||| self.entries[slot] is Reserved
            ||| (self.entries[slot] is Filled && !(self.status_map[slot] is Writeback))
        }
    }

    pub open spec(checked) fn valid_new_slots_mapping(self, mapping: Map<Slot, Address>) -> bool 
    {
        // 1 address can't be mapped to 2 slots
        &&& mapping.is_injective()
        &&& self.lookup_map.dom().disjoint(mapping.values())

        // new slot must be empty and within the slot range
        &&& mapping.dom() <= self.entries.dom()
        &&& forall |slot| #[trigger] mapping.contains_key(slot) ==> self.entries[slot] is Empty
    }

    // reserve is only used for bypass writes
    transition!{ reserve(lbl: Label, new_slots_mapping: Map<Slot, Address>) {
        require lbl is Internal;
        require pre.valid_new_slots_mapping(new_slots_mapping);

        let updated_entries = Map::new(
            |slot| new_slots_mapping.contains_key(slot),
            |slot| Entry::Reserved{addr: new_slots_mapping[slot]}
        );

        // reserve is not filled plus reserved
        update entries = pre.entries.union_prefer_right(updated_entries);
        update lookup_map = pre.lookup_map.union_prefer_right(new_slots_mapping.invert());
    }}

    transition!{ load_initiate(lbl: Label, new_slots_mapping: Map<Slot, Address>) {
        require let Label::DiskOps{requests, responses} = lbl;
        require !requests.is_empty();
        require responses.is_empty();

        assert(lbl is DiskOps);

        require pre.valid_new_slots_mapping(new_slots_mapping);
        
        require requests.is_injective();
        require forall |id| #[trigger] requests.contains_key(id) ==> requests[id] is ReadReq;
        require forall |req| #[trigger] requests.contains_value(req) <==> new_slots_mapping.contains_value(req->from);

        // new slots mapping should be identical 
        let invert_slot_map = new_slots_mapping.invert();
        let updated_outstanding_reqs = Map::new(
            |id| requests.contains_key(id), 
            |id| invert_slot_map[requests[id]->from]);

        let updated_entries = Map::new(
            |slot| new_slots_mapping.contains_key(slot),
            |slot| Entry::Loading{addr: new_slots_mapping[slot]}
        );

        update entries = pre.entries.union_prefer_right(updated_entries);
        update lookup_map = pre.lookup_map.union_prefer_right(invert_slot_map);
        update outstanding_reqs = pre.outstanding_reqs.union_prefer_right(updated_outstanding_reqs);
    }}

    // receive read responses from disk
    transition!{ load_complete(lbl: Label) {
        require let Label::DiskOps{requests, responses} = lbl;
        require requests.is_empty();
        require !responses.is_empty();

        require responses.dom() <= pre.outstanding_reqs.dom();
        require forall |id| #[trigger] responses.contains_key(id) ==> {
            &&& responses[id] is ReadResp
            &&& pre.entries[pre.outstanding_reqs[id]] is Loading
        };

        let slot_id_map = pre.outstanding_reqs.restrict(responses.dom()).invert();
        let updated_entries = Map::new(
            |slot| slot_id_map.contains_key(slot),
            |slot| Entry::Filled{
                addr: pre.entries[slot].get_addr(),
                data: responses[slot_id_map[slot]]->data
            }
        );

        let updated_status_map = Map::new(
            |slot| slot_id_map.contains_key(slot),
            |slot| Status::Clean
        );

        update entries = pre.entries.union_prefer_right(updated_entries);
        update status_map = pre.status_map.union_prefer_right(updated_status_map);
        update outstanding_reqs = pre.outstanding_reqs.remove_keys(responses.dom());
    }}

    // NOTE: access must enable batched accesses because program
    // model needs to make batch updates as an atomic transition
    transition!{ access(lbl: Label) {
        require lbl is Access;
        require forall |addr| #[trigger] lbl->reads.contains_key(addr) 
            ==> pre.valid_read(addr, lbl->reads[addr]);
        require forall |addr| #[trigger] lbl->writes.contains_key(addr) 
            ==> pre.valid_write(addr);

        let write_slots = pre.lookup_map.restrict(lbl->writes.dom()).values();

        let updated_entries = Map::new(
            |slot| write_slots.contains(slot),
            |slot| Entry::Filled{
                addr: pre.entries[slot].get_addr(), 
                data: lbl->writes[pre.entries[slot].get_addr()]
            });

        let updated_status_map = Map::new(
            |slot| write_slots.contains(slot),
            |slot| Status::Dirty
        );

        update entries = pre.entries.union_prefer_right(updated_entries);
        update status_map = pre.status_map.union_prefer_right(updated_status_map);
    }}

    transition!{ writeback_initiate(lbl: Label) {
        require let Label::DiskOps{requests, responses} = lbl;
        require !requests.is_empty();
        require responses.is_empty();

        require forall |req| requests.values().contains(req) ==> {
            &&& req is WriteReq
            &&& #[trigger] pre.lookup_map.contains_key(req->to)
            &&& pre.entries[pre.lookup_map[req->to]] == Entry::Filled{addr: req->to, data: req->data}
            &&& pre.status_map[pre.lookup_map[req->to]] is Dirty
        };

        let updated_outstanding_reqs = Map::new(|id| requests.contains_key(id), |id| pre.lookup_map[requests[id]->to]);
        let updated_status_map = Map::new(|slot| updated_outstanding_reqs.contains_value(slot), |slot| Status::Writeback{});

        update status_map = pre.status_map.union_prefer_right(updated_status_map);
        update outstanding_reqs = pre.outstanding_reqs.union_prefer_right(updated_outstanding_reqs);
    }}

    // receive write responses from disk
    transition!{ writeback_complete(lbl: Label) {
        require let Label::DiskOps{requests, responses} = lbl;
        require requests.is_empty();
        require !responses.is_empty();
    
        require responses.dom() <= pre.outstanding_reqs.dom();
        require forall |id| #[trigger] responses.contains_key(id) ==> {
            &&& responses[id] is WriteResp
            &&& pre.entries[pre.outstanding_reqs[id]] is Filled
            &&& pre.status_map[pre.outstanding_reqs[id]] is Writeback
        };

        let resps_slots = pre.outstanding_reqs.restrict(responses.dom()).values();
        let updated_status_map = Map::new(
            |slot| resps_slots.contains(slot), 
            |slot| Status::Clean
        );

        update status_map = pre.status_map.union_prefer_right(updated_status_map);
        update outstanding_reqs = pre.outstanding_reqs.remove_keys(responses.dom());
    }}

    transition!{ evict(lbl: Label, evicted_slots: Set<Slot>) {
        // eviction of pages should be seen as internal or not
        // I guess this is an invalidate page access, we can imagine 
        // the difference is when the cache is required to enforce it, 
        // if it's not enforced right away then. the question is is it ever possible
        // for us to discard journal pages that have never been marshalled and 

        require lbl is Internal;
        require evicted_slots <= pre.entries.dom();
        require forall |slot| #[trigger] evicted_slots.contains(slot) ==> {        
            &&& pre.entries[slot] is Filled
            &&& pre.status_map[slot] is Clean
        };

        // &&& self.lookup_map.contains_key(addr)
        // &&& (self.status_map[self.lookup_map[addr]] is Writeback 
        //     || self.status_map[self.lookup_map[addr]] is Dirty)
 
        let evicted_addrs = Map::new(|slot| evicted_slots.contains(slot), |slot| pre.entries[slot].get_addr()).values();
        let updated_entries = Map::new(|slot| evicted_slots.contains(slot), |slot| Entry::Empty);
        let updated_status_map = Map::new(|slot| evicted_slots.contains(slot), |slot| Status::NotFilled);

        update entries = pre.entries.union_prefer_right(updated_entries);
        update status_map = pre.status_map.union_prefer_right(updated_status_map);
        update lookup_map = pre.lookup_map.remove_keys(evicted_addrs);
    }}

    transition!{ evictable(lbl: Label) {
        require lbl is EvictableCheck;
        require forall |addr| #[trigger] lbl->addrs.contains(addr) && pre.lookup_map.contains_key(addr)
                ==> {
                    &&& pre.entries[pre.lookup_map[addr]] is Filled
                    &&& pre.status_map[pre.lookup_map[addr]] is Clean
                };
    }}

    transition!{ noop(lbl: Label) {
        require lbl is Internal;
    }}

    init!{ initialize(slots: nat) {
        init entries = Map::new(|i: Slot| i < slots , |i| Entry::Empty);
        init status_map = Map::new(|i: Slot| i < slots , |i| Status::NotFilled);
        init lookup_map = Map::empty();
        init outstanding_reqs = Map::empty();
    }}

    #[invariant]
    pub open spec(checked) fn inv(self) -> bool {
        &&& self.slots_hold_unique_addr()
        &&& self.status_map.dom() =~= self.entries.dom()
        &&& self.lookup_map == self.build_lookup_map()

        &&& forall |slot| #[trigger] self.status_map.contains_key(slot)
            ==> ( (self.status_map[slot] is NotFilled) <==> !(self.entries[slot] is Filled) )

        // &&& self.outstanding_reqs.values() <= self.entries.dom()
        &&& self.outstanding_reqs.values() <= self.lookup_map.values()
        &&& self.outstanding_reqs.is_injective()
        &&& self.outstanding_reqs_non_empty_slots()

        // do we also need to require self.outstanding
        // NOTE(disk): 1 outstanding IO for each loading/writeback page, reserved & filled (!writeback) -> 0 I/O
    }

    pub open spec fn build_lookup_map(self) -> Map<Address, Slot>
    {
        let filled_slot_addr_map = Map::new(
            |slot| self.entries.contains_key(slot) && self.entries[slot] is Filled,
            |slot| self.entries[slot].get_addr()
        );
        filled_slot_addr_map.invert()
    }

    pub open spec fn non_empty_slot(self, slot: Slot) -> bool
    {
        &&& self.entries.contains_key(slot) 
        &&& !(self.entries[slot] is Empty)
    }

    pub open spec fn slots_hold_unique_addr(self) -> bool
    {
        forall |s1, s2| #[trigger] self.non_empty_slot(s1)
            && #[trigger] self.non_empty_slot(s2) && s1 != s2 
        ==> self.entries[s1].get_addr() != self.entries[s2].get_addr()
    }

    pub proof fn build_lookup_map_ensures(self)
    requires self.slots_hold_unique_addr()
    ensures ({
        let lookup_map = self.build_lookup_map();
        &&& forall |addr| #[trigger] lookup_map.contains_key(addr) 
            <==> self.non_empty_slot(lookup_map[addr]) 
        &&& forall |slot| #[trigger] self.non_empty_slot(slot)
            ==> lookup_map.contains_key(self.entries[slot].get_addr()) 
                && lookup_map[self.entries[slot].get_addr()] == slot
    }) {
        assume(false);
    }

    pub open spec fn outstanding_reqs_non_empty_slots(self) -> bool
    {
        forall |id| #[trigger] self.outstanding_reqs.contains_key(id)
            ==> self.non_empty_slot(self.outstanding_reqs[id])
    }

    pub open spec fn outstanding_reqs_unique_slots(self) -> bool
    {
        forall |id1, id2| #[trigger] self.outstanding_reqs.contains_key(id1)
            && #[trigger] self.outstanding_reqs.contains_key(id2) && id1 != id2
            ==> self.outstanding_reqs[id1] != self.outstanding_reqs[id2]
    }

    #[inductive(reserve)]
    fn reserve_inductive(pre: Self, post: Self, lbl: Label, new_slots_mapping: Map<Slot, Address>) { 
        assume(false);
    }
    
    #[inductive(load_initiate)]
    fn load_initiate_inductive(pre: Self, post: Self, lbl: Label, new_slots_mapping: Map<Slot, Address>) {
        assume(false);
    }
    
    #[inductive(load_complete)]
    fn load_complete_inductive(pre: Self, post: Self, lbl: Label) { 
        assume(false);
    }

    #[inductive(access)]
    fn access_inductive(pre: Self, post: Self, lbl: Label) { 
        assume(false);
    }
    
    #[inductive(writeback_initiate)]
    fn writeback_initiate_inductive(pre: Self, post: Self, lbl: Label) { 
        assume(false);
    }
    
    #[inductive(writeback_complete)]
    fn writeback_complete_inductive(pre: Self, post: Self, lbl: Label) { 
        assume(false);
    }
    
    #[inductive(evict)]
    fn evict_inductive(pre: Self, post: Self, lbl: Label, evicted_slots: Set<Slot>) { 
        assume(false);
    }
    
    #[inductive(evictable)]
    fn evictable_inductive(pre: Self, post: Self, lbl: Label) { }
    
    #[inductive(noop)]
    fn noop_inductive(pre: Self, post: Self, lbl: Label) { }
    
    #[inductive(initialize)]
    pub fn initialize_inductive(post: Self, slots: nat) { 
        assume(false);
    }

    pub proof fn inv_next(pre: Self, post: Self, lbl: Label)
        requires Self::next(pre, post, lbl), pre.inv()
        ensures post.inv()
    {
        assume(false);

        // NOTE(JL): commenting out for now, seems like we can't satisfy the *_strong
        // predicate needed by each inductive proof, probably due to triggers
        // assuming false here for now since those proofs aren't proven anyway

        // reveal(Cache::State::next);
        // reveal(Cache::State::next_by);

        // let step = choose |step| Self::next_by(pre, post, lbl, step);
        // match step {
        //     Cache::Step::reserve(new_slots_mapping) => {
        //         Self::reserve_inductive(pre, post, lbl, new_slots_mapping);
        //     }
        //     Cache::Step::load_initiate(new_slots_mapping) => {
        //         assert(pre.inv());
        //         assert(Self::next_by(pre, post, lbl, step));
        //         assert(Self::load_initiate(pre, post, lbl, new_slots_mapping));

        //         // assume(false);
        //         Self::load_initiate_inductive(pre, post, lbl, new_slots_mapping);
        //     }
        //     Cache::Step::load_complete() => {
        //         assume(false);
        //         Self::load_complete_inductive(pre, post, lbl);
        //     }
        //     Cache::Step::access() => {
        //         assume(false);

        //         Self::access_inductive(pre, post, lbl);
        //     }
        //     Cache::Step::writeback_initiate() => {
        //         assume(false);

        //         Self::writeback_initiate_inductive(pre, post, lbl);
        //     }
        //     Cache::Step::writeback_complete() => {
        //         assume(false);

        //         Self::writeback_complete_inductive(pre, post, lbl);
        //     }
        //     Cache::Step::evict(evicted_slots) => {
        //         assume(false);

        //         Self::evict_inductive(pre, post, lbl, evicted_slots);
        //     }
        //     Cache::Step::evictable() => {
        //         assume(false);

        //         Self::evictable_inductive(pre, post, lbl);
        //     }
        //     Cache::Step::noop() => {
        //         assume(false);
        //         Self::noop_inductive(pre, post, lbl);
        //     }
        //     _ => { assert(false); }
        // }
    }
}}

pub proof fn injective_map_property<K,V>(map: Map<K, V>)
    requires map.is_injective()
    ensures 
        map.dom() =~= map.invert().values(),
        forall |k| #[trigger] map.contains_key(k) ==> map.invert()[map[k]] == k,
{
    assume(false);
}
} // end of !verus