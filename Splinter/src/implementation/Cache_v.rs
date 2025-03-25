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
    Writeback{id: ID},
}

pub enum Entry {
    Empty,
    Reserved{addr: Address},
    Loading{addr: Address, id: ID}, 
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

pub open spec fn build_lookup_map(entries: Map<Slot, Entry>) -> Map<Address, Slot>
{
    let filled_slot_addr_map = Map::new(
        |slot| entries.contains_key(slot) && entries[slot] is Filled,
        |slot| entries[slot].get_addr()
    );
    filled_slot_addr_map.invert()
}

state_machine!{ Cache {
    fields {
        pub entries: Map<Slot, Entry>,
        pub status_map: Map<Slot, Status>,
        pub lookup_map: Map<Address, Slot>,
    }

    pub enum Label {
        Access{reads: Map<Address, RawPage>, writes: Map<Address, RawPage>},

        // I think we can break up DiskOps into 2
        // cache writes
        // cache reads 

        // 
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

        update entries = pre.entries.union_prefer_right(updated_entries);
        update lookup_map = pre.lookup_map.union_prefer_right(new_slots_mapping.invert());
    }}

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

        let addr_id_map = Map::new(|id| requests.contains_key(id), |id| requests[id]->from).invert();

        require pre.valid_new_slots_mapping(new_slots_mapping);
        require addr_id_map.dom() =~= new_slots_mapping.values();

        let updated_entries = Map::new(
            |slot| new_slots_mapping.contains_key(slot),
            |slot| Entry::Loading{addr: new_slots_mapping[slot], id: addr_id_map[new_slots_mapping[slot]]}
        );

        update entries = pre.entries.union_prefer_right(updated_entries);
        update lookup_map = pre.lookup_map.union_prefer_right(new_slots_mapping.invert());
    }}

    // receive read responses from disk
    transition!{ load_complete(lbl: Label, id_slot_map: Map<ID, Slot>) {
        require let Label::DiskOps{requests, responses} = lbl;
        require requests.is_empty();
        require !responses.is_empty();

        require id_slot_map.dom() == responses.dom();
        require id_slot_map.values() <= pre.entries.dom();

        require forall |id| #[trigger] responses.contains_key(id) ==> {
            &&& responses[id] is ReadResp
            &&& pre.entries[id_slot_map[id]] is Loading
            &&& pre.entries[id_slot_map[id]]->id == id
        };

        let slot_id_map = id_slot_map.invert();

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

    // should write back allow 
    // when we perform the flush we probably want to give an entire range?
    // user of the cache wouldn't really know though :o

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

        let id_slot_map = Map::new(|id| requests.contains_key(id), |id| pre.lookup_map[requests[id]->to]);
        let slot_id_map = id_slot_map.invert();

        let updated_status_map = Map::new(
            |slot| slot_id_map.contains_key(slot), 
            |slot| Status::Writeback{id: slot_id_map[slot]}
        );

        update status_map = pre.status_map.union_prefer_right(updated_status_map);
    }}

    // receive write responses from disk
    transition!{ writeback_complete(lbl: Label, id_slot_map: Map<ID, Slot>) {
        require let Label::DiskOps{requests, responses} = lbl;
        require requests.is_empty();
        require !responses.is_empty();
    
        require id_slot_map.dom() == responses.dom();
        require id_slot_map.values() <= pre.entries.dom();

        require forall |id| #[trigger] responses.contains_key(id) ==> {
            &&& responses[id] is WriteResp
            &&& pre.entries[id_slot_map[id]] is Filled 
            &&& pre.status_map[id_slot_map[id]] is Writeback
            &&& pre.status_map[id_slot_map[id]]->id == id
        };
    
        let updated_status_map = Map::new(
            |slot| id_slot_map.contains_value(slot), 
            |slot| Status::Clean
        );

        update status_map = pre.status_map.union_prefer_right(updated_status_map);
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

    // #[invariant]
    pub open spec(checked) fn inv(self) -> bool {
        &&& self.status_map.dom() =~= self.entries.dom()
        &&& self.lookup_map == build_lookup_map(self.entries)
        &&& forall |slot| #[trigger] self.status_map.contains_key(slot)
            ==> ( (self.status_map[slot] is NotFilled) <==> !(self.entries[slot] is Filled) )
    }

    // #[inductive(reserve)]
    // fn reserve_inductive(pre: Self, post: Self, lbl: Label, new_slots_mapping: Map<Slot, Address>) { 
    //     injective_map_property(new_slots_mapping);
    // }
   
    // #[inductive(load_initiate)]
    // fn load_initiate_inductive(pre: Self, post: Self, lbl: Label, new_slots_mapping: Map<Slot, Address>) { 
    //     injective_map_property(new_slots_mapping);
    // }
   
    // #[inductive(load_complete)]
    // fn load_complete_inductive(pre: Self, post: Self, lbl: Label, id_slot_map: Map<ID, Slot>) { 
    //     assume(false);
    // }

    // #[inductive(access)]
    // fn access_inductive(pre: Self, post: Self, lbl: Label) { 
    //     assume(false);
    // }

    // #[inductive(writeback_initiate)]
    // fn writeback_initiate_inductive(pre: Self, post: Self, lbl: Label) { 
    //     assume(false);
    // }

    // #[inductive(writeback_complete)]
    // fn writeback_complete_inductive(pre: Self, post: Self, lbl: Label, id_slot_map: Map<ID, Slot>) { 
    //     assume(false);
    // }

    // #[inductive(evict)]
    // fn evict_inductive(pre: Self, post: Self, lbl: Label, evicted_slots: Set<Slot>) {
    //     assume(false);
    //     // assert forall |addr| #[trigger] post.lookup_map.contains_key(addr) 
    //     // implies !(post.entries[post.lookup_map[addr]] is Empty)
    //     // by {
    //     //     if evicted_slots.contains(post.lookup_map[addr]) {
    //     //         let evicted_mappings = Map::new(|slot| evicted_slots.contains(slot), |slot| pre.entries[slot].get_addr());
    //     //         assert(evicted_mappings.contains_key(post.lookup_map[addr]));
    //     //         assert(evicted_mappings[post.lookup_map[addr]] == addr);
    //     //         assert(false);
    //     //     }
    //     // }
    // }

    // #[inductive(noop)]
    // fn noop_inductive(pre: Self, post: Self, lbl: Label) { }
   
    // #[inductive(initialize)]
    // fn initialize_inductive(post: Self, slots: nat) {
    //     assert(build_lookup_map(post.entries) =~= Map::empty());
    //     // let filled_slot_addr_map = Map::new(
    //     //     |slot| entries.contains_key(slot) && entries[slot] is Filled,
    //     //     |slot| entries[slot].get_addr()
    //     // );
    // }
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