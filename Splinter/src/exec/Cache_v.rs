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
        recommends self is Reserved || self is Loading || self is Filled
    {
        if let Entry::Reserved{addr} = self {
            addr
        } else if let Entry::Loading{addr} = self {
            addr
        } else if let Entry::Filled{addr, data} = self {
            addr
        } else {
            arbitrary()
        }
    }
}

// TODO: update status_map 
state_machine!{ Cache {
    fields {
        pub entries: Map<Slot, Entry>,
        pub status_map: Map<Slot, Status>,
        pub lookup_map: Map<Address, Slot>,
    }

    pub enum Label {
        Access{reads: Map<Slot, RawPage>, writes: Map<Slot, RawPage>},
        DiskOps{requests: Map<ID, DiskRequest>, responses: Map<ID, DiskResponse>},
        Internal,
    }

    pub open spec fn valid_read(self, slot: Slot, data: RawPage) -> bool 
    {
        &&& self.entries.contains_key(slot)
        &&& self.entries[slot] is Filled
        &&& data == self.entries[slot]->data
    }

    pub open spec fn valid_write(self, slot: Slot) -> bool 
    {
        if self.entries.contains_key(slot) {
            self.entries[slot] is Reserved // write to bypass page
            || (self.entries[slot] is Filled && !(self.status_map[slot] is Writeback))
        } else {
            false
        }
    }

    pub open spec(checked) fn valid_new_slots_mapping(self, mapping: Map<Slot, Address>) -> bool 
    {
        // 1 address can't be mapped to 2 slots
        &&& mapping.is_injective()
        &&& self.lookup_map.dom().disjoint(mapping.values())

        // new slot must be within the existing range and be empty
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

        update entries = pre.entries.union_prefer_right(updated_entries);
        update lookup_map = pre.lookup_map.union_prefer_right(new_slots_mapping.invert());
    }}

    // load pages from disk
    transition!{ load_initiate(lbl: Label, new_slots_mapping: Map<Slot, Address>) {
        require let Label::DiskOps{requests, responses} = lbl;
        require !requests.is_empty();
        require responses.is_empty();

        // the same address can't be requested twice
        require requests.is_injective();
        require forall |req| #[trigger] requests.values().contains(req) ==> {
            &&& req is ReadReq
            &&& pre.lookup_map.contains_key(req->from)
            &&& pre.entries[pre.lookup_map[req->from]] is Empty
        };

        let read_addrs = Map::new(|id| requests.contains_key(id), |id| requests[id]->from).values();

        require pre.valid_new_slots_mapping(new_slots_mapping);
        require read_addrs =~= new_slots_mapping.values();

        let updated_entries = Map::new(
            |slot| new_slots_mapping.contains_key(slot),
            |slot| Entry::Loading{addr: new_slots_mapping[slot]}
        );

        update entries = pre.entries.union_prefer_right(updated_entries);
        update lookup_map = pre.lookup_map.union_prefer_right(new_slots_mapping.invert());
    }}

    // receive read responses from disk
    transition!{ load_complete(lbl: Label) {
        require let Label::DiskOps{requests, responses} = lbl;
        require requests.is_empty();
        require !responses.is_empty();

        require forall |resp| #[trigger] responses.values().contains(resp) ==> {
            &&& resp is ReadResp
            &&& pre.lookup_map.contains_key(resp->from)
            &&& pre.entries[pre.lookup_map[resp->from]] is Loading
        };

        let read_map = Map::new(|id| responses.contains_key(id), |id| responses[id]->from).invert();
        let load_slots = pre.lookup_map.restrict(read_map.dom()).values();

        let updated_entries = Map::new(
            |slot| load_slots.contains(slot),
            |slot| Entry::Filled{
                addr: pre.entries[slot].get_addr(),
                data: responses[read_map[pre.entries[slot].get_addr()]]->data
            }
        );

        let updated_status_map = Map::new(
            |slot| load_slots.contains(slot),
            |slot| Status::Clean
        );

        update entries = pre.entries.union_prefer_right(updated_entries);
        update status_map = pre.status_map.union_prefer_right(updated_status_map);
    }}

    // NOTE: access must enable batched accesses because program
    // model needs to make batch updates as an atomic transition
    transition!{ access(lbl: Label) {
        require lbl is Access;
        require forall |slot| #[trigger] lbl->reads.contains_key(slot) 
            ==> pre.valid_read(slot, lbl->reads[slot]);
        require forall |slot| #[trigger] lbl->writes.contains_key(slot) 
            ==> pre.valid_write(slot);

        let updated_entries = Map::new(
            |slot| lbl->writes.contains_key(slot),
            |slot| Entry::Filled{
                addr: pre.entries[slot].get_addr(), 
                data: lbl->writes[slot]
            });

        let updated_status_map = Map::new(
            |slot| lbl->writes.contains_key(slot),
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

        let write_addrs = Map::new(|id| requests.contains_key(id), |id| requests[id]->to).values();
        let write_slots = pre.lookup_map.restrict(write_addrs).values();
        let updated_status_map = Map::new(|slot| write_slots.contains(slot), |slot| Status::Writeback);

        update status_map = pre.status_map.union_prefer_right(updated_status_map);
    }}

    // receive write responses from disk
    transition!{ writeback_complete(lbl: Label) {
        require let Label::DiskOps{requests, responses} = lbl;
        require requests.is_empty();
        require !responses.is_empty();
    
        require forall |resp| responses.values().contains(resp) ==> {
            &&& resp is WriteResp
            &&& #[trigger] pre.lookup_map.contains_key(resp->to)
            &&& pre.status_map.contains_key(pre.lookup_map[resp->to])
            &&& pre.status_map[pre.lookup_map[resp->to]] is Writeback
        };
    
        // unless writes happen outside the cache, multiple read requests should see the same content
        let write_addrs = Map::new(|id| responses.contains_key(id), |id| responses[id]->to).values();
        let write_slots = pre.lookup_map.restrict(write_addrs).values();
        let updated_status_map = Map::new(|slot| write_slots.contains(slot), |slot| Status::Clean);

        update status_map = pre.status_map.union_prefer_right(updated_status_map);
    }}

    transition!{ evict(lbl: Label, evicted_slots: Set<Slot>) {
        require lbl is Internal;
        require evicted_slots <= pre.entries.dom();
        require forall |slot| #[trigger] evicted_slots.contains(slot) ==> {        
            &&& pre.entries[slot] is Filled
            &&& pre.status_map[slot] is Clean
        };
 
        let evicted_addrs = Map::new(|slot| evicted_slots.contains(slot), |slot| pre.entries[slot].get_addr()).values();
        let updated_entries = Map::new(|slot| evicted_slots.contains(slot), |slot| Entry::Empty);
        let updated_status_map = Map::new(|slot| evicted_slots.contains(slot), |slot| Status::NotFilled);

        update entries = pre.entries.union_prefer_right(updated_entries);
        update status_map = pre.status_map.union_prefer_right(updated_status_map);
        update lookup_map = pre.lookup_map.remove_keys(evicted_addrs);
    }}

    transition!{ noop(lbl: Label) {
        require lbl is Internal;
    }}

    init!{ initialize(slots: nat) {
        init entries = Map::new(|i: Slot| i < slots , |i| Entry::Empty);
        init status_map = Map::new(|i: Slot| i < slots , |i| Status::NotFilled);
        init lookup_map = Map::empty();
    }}

    // NOTE(disk): 1 outstanding IO for each loading/writeback page, reserved & filled (!writeback) -> 0 I/O

    #[invariant]
    pub open spec(checked) fn inv(self) -> bool {
        &&& self.status_map.dom() =~= self.entries.dom()
        &&& self.lookup_map.values() <= self.entries.dom()

        &&& forall |slot| #[trigger] self.entries.contains_key(slot) && !(self.entries[slot] is Empty) 
            ==> {
                &&& self.lookup_map.contains_key(self.entries[slot].get_addr())
                &&& self.lookup_map[self.entries[slot].get_addr()] == slot
            }

        &&& forall |addr| #[trigger] self.lookup_map.contains_key(addr) 
            ==> {
                &&& !(self.entries[self.lookup_map[addr]] is Empty)
                &&& self.entries[self.lookup_map[addr]].get_addr() == addr
            }

        &&& forall |slot| #[trigger] self.status_map.contains_key(slot)
            ==> ( (self.status_map[slot] is NotFilled) <==> !(self.entries[slot] is Filled) )
    }

    #[inductive(reserve)]
    fn reserve_inductive(pre: Self, post: Self, lbl: Label, new_slots_mapping: Map<Slot, Address>) { 
        injective_map_property(new_slots_mapping);

    }
   
    #[inductive(load_initiate)]
    fn load_initiate_inductive(pre: Self, post: Self, lbl: Label, new_slots_mapping: Map<Slot, Address>) { 
        injective_map_property(new_slots_mapping);
    }
   
    #[inductive(load_complete)]
    fn load_complete_inductive(pre: Self, post: Self, lbl: Label) { }
   
    #[inductive(access)]
    fn access_inductive(pre: Self, post: Self, lbl: Label) { }

    #[inductive(writeback_initiate)]
    fn writeback_initiate_inductive(pre: Self, post: Self, lbl: Label) { }

    #[inductive(writeback_complete)]
    fn writeback_complete_inductive(pre: Self, post: Self, lbl: Label) { }

    #[inductive(evict)]
    fn evict_inductive(pre: Self, post: Self, lbl: Label, evicted_slots: Set<Slot>) {
        assert forall |addr| #[trigger] post.lookup_map.contains_key(addr) 
        implies !(post.entries[post.lookup_map[addr]] is Empty)
        by {
            if evicted_slots.contains(post.lookup_map[addr]) {
                let evicted_mappings = Map::new(|slot| evicted_slots.contains(slot), |slot| pre.entries[slot].get_addr());
                assert(evicted_mappings.contains_key(post.lookup_map[addr]));
                assert(evicted_mappings[post.lookup_map[addr]] == addr);
                assert(false);
            }
        }
    }

    #[inductive(noop)]
    fn noop_inductive(pre: Self, post: Self, lbl: Label) { }
   
    #[inductive(initialize)]
    fn initialize_inductive(post: Self, slots: nat) { }
}}

// TODO: prove & add to vstd
pub proof fn injective_map_property<K,V>(map: Map<K, V>)
    requires map.is_injective()
    ensures 
        map.dom() =~= map.invert().values(),
        forall |k| #[trigger] map.contains_key(k) ==> map.invert()[map[k]] == k,
{
    assume(false);
}
} // end of !verus