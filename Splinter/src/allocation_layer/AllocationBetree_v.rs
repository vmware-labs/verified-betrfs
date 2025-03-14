// Copyright 2018-2024 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, University of Washington
// SPDX-License-Identifier: BSD-2-Clause
#![allow(unused_imports)]
use builtin::*;

use builtin_macros::*;
use state_machines_macros::state_machine;

use vstd::{prelude::*, seq_lib::*, set_lib::*, map_lib::*, multiset::*};
use crate::spec::KeyType_t::*;
use crate::spec::Messages_t::*;
use crate::disk::GenericDisk_v::*;
use crate::betree::Buffer_v::*;
use crate::betree::LinkedSeq_v::*;
use crate::betree::BufferDisk_v;
use crate::betree::BufferDisk_v::*;
use crate::betree::BufferOffsets_v::*;
use crate::betree::OffsetMap_v::*;
use crate::betree::Memtable_v::*;
use crate::betree::Domain_v::*;
use crate::betree::PivotTable_v::*;
use crate::betree::SplitRequest_v::*;
use crate::betree::LinkedBetree_v::*;
use crate::allocation_layer::Likes_v::*;
use crate::allocation_layer::LikesBetree_v::*;
use crate::abstract_system::StampedMap_v::*;
use crate::abstract_system::MsgHistory_v::*;

verus! {

// read only inputs for the compaction
pub struct CompactorInput{
    pub input_buffers: LinkedSeq,
    pub offset_map: OffsetMap,
}

pub open spec fn seq_addrs_to_aus(s: Seq<Address>) -> Set<AU>
    // decreases s.len()
{
    to_aus(s.to_set())
    // if s.len() > 0 {
    //     set![s.last().au] + seq_addrs_to_aus(s.drop_last())
    // } else {
    //     set![]
    // }
}

// to aus 

impl CompactorInput{
    pub open spec(checked) fn input_aus(inputs: Seq<CompactorInput>) -> Set<AU>
        // decreases inputs.len()
    {
        inputs.fold_left(Set::empty(), |u: Set<AU>, s: CompactorInput| u.union(seq_addrs_to_aus(s.input_buffers.addrs)))
        // if inputs.len() > 0 {
        //     seq_addrs_to_aus(inputs.last().input_buffers.addrs) + Self::input_aus(inputs.drop_last())
        // } else {
        //     set![]
        // }
    }
}

pub open spec fn restrict_domain_au<V>(m: Map<Address, V>, aus: Set<AU>) -> Set<Address>
{
    m.dom().filter(|addr: Address| aus.contains(addr.au))
}

pub proof fn restrict_domain_au_ensures<V>(likes: Likes, m: Map<Address, V>)
    requires likes.dom() <= m.dom()
    ensures likes.dom() <= restrict_domain_au(m, to_au_likes(likes).dom()) 
{
    let aus = to_au_likes(likes);
    let kept_addrs = restrict_domain_au(m, aus.dom());

    to_au_likes_domain(likes);

    assert forall |addr| #[trigger] likes.dom().contains(addr)
    implies kept_addrs.contains(addr) 
    by {
        assert(m.contains_key(addr));
        assert(likes.contains(addr)); // trigger
    }
}

/// Introduces aulikes to track the life time of disk data structures in terms of Allocation Unit.
/// Incorporates read only reference tracking for determining GC

state_machine!{ AllocationBetree {
    fields {
        pub betree: LinkedBetreeVars::State<SimpleBuffer>,

        pub betree_aus: AULikes,    // tree node reference
        pub buffer_aus: AULikes,    // root au of each branch
        pub compactors: Seq<CompactorInput>, // track ongoing compactions
    }

    pub enum Label
    {
        Label{linked_lbl: LinkedBetreeVars::Label},
    }

    // remain like this until we strictly describe a tight disk range based on AULikes (next layer)
    pub open spec fn is_fresh(self, addrs: Set<Address>) -> bool
    {
        self.betree.linked.is_fresh(addrs)
    }

    pub open spec fn read_ref_aus(self) -> Set<AU>
    {
        CompactorInput::input_aus(self.compactors)
    }

    init!{ initialize(betree: LinkedBetreeVars::State<SimpleBuffer>) {
        require LinkedBetreeVars::State::initialize(betree, betree);

        let (betree_likes, buffer_likes) = betree.linked.transitive_likes();

        init betree = betree;
        init betree_aus = to_au_likes(betree_likes);
        init buffer_aus = to_au_likes(buffer_likes);
        init compactors = Seq::empty();
    }}

    transition!{ au_likes_noop(lbl: Label, new_betree: LinkedBetreeVars::State<SimpleBuffer>) {
        require lbl->linked_lbl is Query || lbl->linked_lbl is Put || lbl->linked_lbl is FreezeAs;
        require LinkedBetreeVars::State::next(pre.betree, new_betree, lbl->linked_lbl);
        update betree = new_betree;
    }}

    pub open spec fn flush_memtable_au_likes<T: Buffer>(betree: LinkedBetreeVars::State<T>, new_betree: LinkedBetreeVars::State<T>, 
        new_addrs: TwoAddrs, betree_aus: AULikes, buffer_aus: AULikes) -> (AULikes, AULikes)
    {
        let discard_betree_aus = to_au_likes(betree.linked.root_likes());
        let add_betree_aus = to_au_likes(new_betree.linked.root_likes());

        let new_betree_aus = betree_aus.sub(discard_betree_aus).add(add_betree_aus);
        let new_buffer_aus = buffer_aus.insert(new_addrs.addr2.au);

        (new_betree_aus, new_buffer_aus)
    }

    transition!{ internal_flush_memtable(lbl: Label, new_betree: LinkedBetreeVars::State<SimpleBuffer>, new_addrs: TwoAddrs) {
        require LinkedBetreeVars::State::internal_flush_memtable(pre.betree, 
            new_betree, lbl->linked_lbl, new_betree.memtable.buffer, new_betree.linked, new_addrs);
        require pre.is_fresh(new_addrs.repr());

        let pushed = pre.betree.linked.push_memtable(new_betree.memtable.buffer, new_addrs);
        let (new_betree_aus, new_buffer_aus) = Self::flush_memtable_au_likes(pre.betree, new_betree, new_addrs, pre.betree_aus, pre.buffer_aus);

        // restrict the range based on aus
        require restrict_domain_au(pushed.dv.entries, new_betree_aus.dom()) <= new_betree.linked.dv.entries.dom();
        require restrict_domain_au(pushed.buffer_dv.entries, new_buffer_aus.dom() + pre.read_ref_aus()) <= new_betree.linked.buffer_dv.repr();

        update betree = new_betree;
        update betree_aus = new_betree_aus;
        update buffer_aus = new_buffer_aus; // buffer address
    }}

    transition!{ internal_grow(lbl: Label, new_betree: LinkedBetreeVars::State<SimpleBuffer>, new_root_addr: Address) {
        require LinkedBetreeVars::State::internal_grow(pre.betree, new_betree, lbl->linked_lbl, new_root_addr);
        require pre.is_fresh(Set::empty().insert(new_root_addr));

        update betree = new_betree;
        update betree_aus = pre.betree_aus.insert(new_root_addr.au);
    }}

    pub open spec fn internal_split_au_likes<T: Buffer>(path: Path<T>, request: SplitRequest, new_addrs: SplitAddrs, 
        path_addrs: PathAddrs, betree_aus: AULikes, buffer_aus: AULikes) -> (AULikes, AULikes)
    {
        let discard_betree_aus = to_au_likes(split_discard_betree(path, request));
        let add_betree_aus = to_au_likes(split_add_betree(new_addrs, path_addrs));
        let new_betree_aus = betree_aus.sub(discard_betree_aus).add(add_betree_aus);

        let add_buffer_aus = to_au_likes(split_add_buffers(path, request));
        let new_buffer_aus = buffer_aus.add(add_buffer_aus);

        (new_betree_aus, new_buffer_aus)
    }

    transition!{ internal_split(lbl: Label, new_betree: LinkedBetreeVars::State<SimpleBuffer>, path: Path<SimpleBuffer>, 
        request: SplitRequest, new_addrs: SplitAddrs, path_addrs: PathAddrs) {
        require LinkedBetreeVars::State::internal_split(pre.betree, new_betree, lbl->linked_lbl, 
            new_betree.linked, path, request, new_addrs, path_addrs);
        require pre.is_fresh(new_addrs.repr().union(path_addrs.to_set()));

        let splitted = LinkedBetreeVars::State::post_split(path, request, new_addrs, path_addrs);
        let (new_betree_aus, new_buffer_aus) = Self::internal_split_au_likes(path, request, new_addrs, path_addrs, pre.betree_aus, pre.buffer_aus);

        require restrict_domain_au(splitted.dv.entries, new_betree_aus.dom()) <= new_betree.linked.dv.entries.dom();
        require restrict_domain_au(splitted.buffer_dv.entries, new_buffer_aus.dom() + pre.read_ref_aus()) <= new_betree.linked.buffer_dv.repr();

        update betree = new_betree;
        update betree_aus = new_betree_aus;
        update buffer_aus = new_buffer_aus;
    }}

    pub open spec fn internal_flush_au_likes<T: Buffer>(path: Path<T>, child_idx: nat, buffer_gc: nat, 
        new_addrs: TwoAddrs, path_addrs: PathAddrs, betree_aus: AULikes, buffer_aus: AULikes) -> (AULikes, AULikes)
    {
        let discard_betree_aus = to_au_likes(flush_discard_betree(path, child_idx));
        let add_betree_aus = to_au_likes(flush_add_betree(new_addrs, path_addrs));
        let new_betree_aus = betree_aus.sub(discard_betree_aus).add(add_betree_aus);

        let discard_buffer_aus = to_au_likes(flush_discard_buffers(path, buffer_gc));
        let add_buffer_aus = to_au_likes(flush_add_buffers(path, child_idx, buffer_gc));
        let new_buffer_aus = buffer_aus.sub(discard_buffer_aus).add(add_buffer_aus);

        (new_betree_aus, new_buffer_aus)
    }

    transition!{ internal_flush(lbl: Label, new_betree: LinkedBetreeVars::State<SimpleBuffer>, path: Path<SimpleBuffer>, 
        child_idx: nat, buffer_gc: nat, new_addrs: TwoAddrs, path_addrs: PathAddrs) {
        require LinkedBetreeVars::State::internal_flush(pre.betree, new_betree, lbl->linked_lbl, 
            new_betree.linked, path, child_idx, buffer_gc, new_addrs, path_addrs);
        require pre.is_fresh(new_addrs.repr() + path_addrs.to_set());

        let flushed = LinkedBetreeVars::State::post_flush(path, child_idx, buffer_gc, new_addrs, path_addrs);
        let (new_betree_aus, new_buffer_aus) = Self::internal_flush_au_likes(path, child_idx, 
            buffer_gc, new_addrs, path_addrs, pre.betree_aus, pre.buffer_aus);

        require restrict_domain_au(flushed.dv.entries, new_betree_aus.dom()) <= new_betree.linked.dv.entries.dom();
        require restrict_domain_au(flushed.buffer_dv.entries, new_buffer_aus.dom() + pre.read_ref_aus()) <= new_betree.linked.buffer_dv.repr();

        update betree = new_betree;
        update betree_aus = new_betree_aus;
        update buffer_aus = new_buffer_aus;
    }}

    pub open spec fn valid_compactor_input<T>(path: Path<T>, start: nat, end: nat, input: CompactorInput) -> bool
    {
        &&& path.valid()
        &&& path.target().has_root()
        &&& {
            let node = path.target().root();
            &&& start < end <= node.buffers.len()
            &&& input == CompactorInput{
                input_buffers: node.buffers.slice(start as int, end as int),
                // offset map tracks live buffers for each key given the entire seq of buffers,
                // here we decrement to account for the slice offset
                offset_map: node.make_offset_map().decrement(start), 
            }
        }
    }

    transition!{ internal_compact_begin(lbl: Label, path: Path<SimpleBuffer>, start: nat, end: nat, input: CompactorInput) {
        require LinkedBetreeVars::State::internal_noop(pre.betree, pre.betree, lbl->linked_lbl);
        require path.linked == pre.betree.linked;
        require Self::valid_compactor_input(path, start, end, input);
        update compactors = pre.compactors.push(input);
    }}

    // can abort a compaction for any reason
    transition!{ internal_compact_abort(lbl: Label, input_idx: int) {
        require LinkedBetreeVars::State::internal_noop(pre.betree, pre.betree, lbl->linked_lbl);
        require 0 <= input_idx < pre.compactors.len();
        update compactors = pre.compactors.remove(input_idx);
    }}

    pub open spec fn internal_compact_complete_au_likes<T: Buffer>(path: Path<T>, start: nat, end: nat, 
        new_addrs: TwoAddrs, path_addrs: PathAddrs, betree_aus: AULikes, buffer_aus: AULikes) -> (AULikes, AULikes)
    {
        let discard_betree_aus = to_au_likes(compact_discard_betree(path));
        let add_betree_aus = to_au_likes(compact_add_betree(new_addrs, path_addrs));
        let new_betree_aus = betree_aus.sub(discard_betree_aus).add(add_betree_aus);

        let discard_buffer_aus = to_au_likes(compact_discard_buffers(path, start, end));
        let add_buffer_aus = to_au_likes(compact_add_buffers(new_addrs));
        let new_buffer_aus = buffer_aus.sub(discard_buffer_aus).add(add_buffer_aus);

        (new_betree_aus, new_buffer_aus)
    }

    transition!{ internal_compact_complete(lbl: Label, input_idx: int, new_betree: LinkedBetreeVars::State<SimpleBuffer>, 
        path: Path<SimpleBuffer>, start: nat, end: nat, compacted_buffer: SimpleBuffer, new_addrs: TwoAddrs, path_addrs: PathAddrs) {
        require 0 <= input_idx < pre.compactors.len();
        require Self::valid_compactor_input(path, start, end, pre.compactors[input_idx]);

        require LinkedBetreeVars::State::internal_compact(pre.betree, new_betree, lbl->linked_lbl, 
            new_betree.linked, path, start, end, compacted_buffer, new_addrs, path_addrs);
        require pre.is_fresh(new_addrs.repr().union(path_addrs.to_set()));
       
        let new_compactors = pre.compactors.remove(input_idx);
        let compacted = LinkedBetreeVars::State::post_compact(path, start, end, compacted_buffer, new_addrs, path_addrs);
        let (new_betree_aus, new_buffer_aus) = Self::internal_compact_complete_au_likes(
            path, start, end, new_addrs, path_addrs, pre.betree_aus, pre.buffer_aus);

        // likes level requirement that new betree must contain all live betree addresses
        require restrict_domain_au(compacted.dv.entries, new_betree_aus.dom()) <= new_betree.linked.dv.entries.dom();
        require restrict_domain_au(compacted.buffer_dv.entries, new_buffer_aus.dom() + CompactorInput::input_aus(new_compactors)) <= new_betree.linked.buffer_dv.repr();

        update betree = new_betree;
        update betree_aus = new_betree_aus;
        update buffer_aus = new_buffer_aus;
        update compactors = new_compactors;
    }}
    
    transition!{ internal_buffer_noop(lbl: Label, new_betree: LinkedBetreeVars::State<SimpleBuffer>) {
        require LinkedBetreeVars::State::internal_buffer_noop(pre.betree, new_betree, lbl->linked_lbl, new_betree.linked);
        update betree = new_betree;
    }}

    transition!{ internal_noop(lbl: Label) {
        require LinkedBetreeVars::State::internal_noop(pre.betree, pre.betree, lbl->linked_lbl);
    }}

}} // end of AllocationBetree state machine

} // end of verus!