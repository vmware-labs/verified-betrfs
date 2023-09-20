// Copyright 2018-2021 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, and University of Washington
// SPDX-License-Identifier: BSD-2-Clause
//
#![allow(unused_imports)]
use builtin::*;
use vstd::prelude::*;
use vstd::math;

use builtin_macros::*;
use state_machines_macros::state_machine;

use vstd::prelude::*;
use vstd::map::*;
use crate::abstract_system::StampedMap_v::LSN;
use crate::abstract_system::MsgHistory_v::*;
use crate::disk::GenericDisk_v::*;
use crate::disk::GenericDisk_v::AU;
use crate::journal::LinkedJournal_v;
use crate::journal::LinkedJournal_v::{DiskView, TruncatedJournal};
use crate::journal::LikesJournal_v;
use crate::journal::LikesJournal_v::LikesJournal;
use crate::allocation_layer::MiniAllocator_v::*;

verus!{

pub struct JournalImage {
    pub tj: TruncatedJournal,
    pub first: AU,
}

impl JournalImage {
    pub open spec(checked) fn wf(self) -> bool
    {
        self.tj.wf()
    }

    pub open spec(checked) fn accessible_aus(self) -> Set<AU>
    {
        to_aus(self.tj.disk_view.entries.dom())
    }

    pub open spec(checked) fn empty() -> Self
    {
        Self{ tj: LinkedJournal_v::TruncatedJournal::mkfs(), first: 0 }
    }
}

state_machine!{ AllocationJournal {
    fields {
        pub journal: LikesJournal::State,

        // lsnAUAddrIndex maps in-repr lsn's to their AU addr
        pub lsn_au_index: Map<LSN, AU>,

        // AU containing the first journal record, boundarylsn can be found somewhere in this AU
        // (We only record the AU here because that's what the implementation can efficiently
        // recover from lsn_au_index at discard time.)
        pub first: AU,

        pub mini_allocator: MiniAllocator,
    }

    #[is_variant]
    pub enum Label
    {
        ReadForRecovery{messages: MsgHistory},
        FreezeForCommit{frozen_journal: JournalImage},
        QueryEndLsn{end_lsn: LSN},
        Put{messages: MsgHistory},
        DiscardOld{start_lsn: LSN, require_end: LSN, deallocs: Set<AU>},
        InternalAllocations{allocs: Set<AU>, deallocs: Set<AU>},
    }

    pub closed spec(checked) fn lbl_wf(lbl: Label) -> bool {
        match lbl {
            Label::FreezeForCommit{frozen_journal} => frozen_journal.tj.decodable(),
            _ => true,
        }
    }

    pub closed spec(checked) fn lbl_i(lbl: Label) -> LikesJournal::Label {
        match lbl {
            Label::ReadForRecovery{messages} =>
                LikesJournal::Label::ReadForRecovery{messages},
            Label::FreezeForCommit{frozen_journal} =>
                LikesJournal::Label::FreezeForCommit{frozen_journal: frozen_journal.tj},
            Label::QueryEndLsn{end_lsn} =>
                LikesJournal::Label::QueryEndLsn{end_lsn},
            Label::Put{messages} =>
                LikesJournal::Label::Put{messages},
            Label::DiscardOld{start_lsn, require_end, deallocs} =>
                LikesJournal::Label::DiscardOld{start_lsn, require_end},
            Label::InternalAllocations{allocs, deallocs} =>
                LikesJournal::Label::Internal{},
        }
    }

    pub open spec(checked) fn wf(self) -> bool {
        &&& self.journal.wf()
        &&& self.mini_allocator.wf()
    }

    pub open spec(checked) fn accessible_aus(self) -> Set<AU> {
        self.lsn_au_index.values() + self.mini_allocator.allocs.dom()
    }

    transition!{ discard_old(lbl: Label, post_journal: LikesJournal::State) {
        require pre.wf();
        require Self::lbl_wf(lbl);
        require lbl.is_DiscardOld();
        require LikesJournal::State::discard_old(pre.journal, post_journal, Self::lbl_i(lbl));

        let new_lsn_au_index = Self::lsn_au_index_discarding_up_to(pre.lsn_au_index, lbl.get_DiscardOld_start_lsn());
        let discarded_aus = pre.lsn_au_index.values().difference(new_lsn_au_index.values());
        let new_first =
            if post_journal.journal.truncated_journal.freshest_rec.is_None() { pre.first }
            else { pre.lsn_au_index[lbl.get_DiscardOld_start_lsn()] };
        require lbl.get_DiscardOld_deallocs() == discarded_aus;

        update journal = post_journal;
        update lsn_au_index = new_lsn_au_index;
        update first = new_first;
        update mini_allocator = pre.mini_allocator.prune(discarded_aus.intersect(pre.mini_allocator.allocs.dom()));
      // note that these AUs refine to free (in the frozen freeset)
    } }

    transition!{ freeze_for_commit(lbl: Label, depth: nat, post_journal: LikesJournal::State) {
        require pre.wf();
        require Self::lbl_wf(lbl);
        require lbl.is_ReadForRecovery();
        require LikesJournal::State::freeze_for_commit(pre.journal, post_journal, Self::lbl_i(lbl), depth, post_journal.journal);
        update journal = post_journal;
    } }

    transition!{ internal_journal_marshal(lbl: Label, cut: LSN, addr: Address, post_linked_journal: LinkedJournal_v::LinkedJournal::State) {
        require pre.wf();
        require Self::lbl_wf(lbl);
        require lbl.is_InternalAllocations();
        require pre.valid_next_journal_addr(addr);
        // TODO(jialin): How do we feel about reaching up two layers to a transition? Eww?
        require LinkedJournal_v::LinkedJournal::State::internal_journal_marshal(
            pre.journal.journal, post_linked_journal,
            LikesJournal::State::lbl_i(Self::lbl_i(lbl)), cut, addr);
        let discard_msgs = pre.journal.journal.unmarshalled_tail.discard_recent(cut);
        update journal = LikesJournal::State{
            journal: post_linked_journal,
            lsn_addr_index: LikesJournal_v::lsn_addr_index_append_record(
                pre.journal.lsn_addr_index, discard_msgs, addr),
            };
        update first =
            if pre.journal.journal.truncated_journal.freshest_rec.is_Some() { pre.first }
            else { addr.au };
        update mini_allocator = pre.mini_allocator.allocate_and_observe(addr);
    } }

    transition!{ internal_mini_allocator_fill(lbl: Label) {
        require pre.wf();
        require Self::lbl_wf(lbl);
        require lbl.is_InternalAllocations();
        require lbl.get_InternalAllocations_deallocs() == Set::<AU>::empty();
        // TODO: maybe we want to eliminate this check and just use the label
        require lbl.get_InternalAllocations_allocs().disjoint(
            pre.mini_allocator.allocs.dom());

        update mini_allocator = pre.mini_allocator.add_aus(lbl.get_InternalAllocations_allocs());
    } }

    transition!{ internal_mini_allocator_prune(lbl: Label) {
        require pre.wf();
        require Self::lbl_wf(lbl);
        require lbl.is_InternalAllocations();
        require lbl.get_InternalAllocations_allocs() == Set::<AU>::empty();
        require forall |au| lbl.get_InternalAllocations_deallocs().contains(au)
                ==> pre.mini_allocator.can_remove(au);

        update mini_allocator = pre.mini_allocator.prune(lbl.get_InternalAllocations_deallocs());
    } }

    // TODO(jonh): delete. Subsumed by only_advance_likes_journal.
    transition!{ internal_journal_no_op(lbl: Label, post_linked_journal: LinkedJournal_v::LinkedJournal::State) {
        require pre.wf();
        require Self::lbl_wf(lbl);
        require lbl.is_InternalAllocations();
    } }

    transition!{ only_advance_likes_journal(lbl: Label, depth: nat, post_likes_journal: LikesJournal::State) {
        require pre.wf();
        require Self::lbl_wf(lbl);
        require {
            ||| lbl.is_ReadForRecovery()
            ||| lbl.is_QueryEndLsn()
            ||| lbl.is_Put()
            // TODO add InternalJournalNoOp?
        };

        require LikesJournal::State::next(
            pre.journal, post_likes_journal,
            Self::lbl_i(lbl));

        update journal = post_likes_journal;
    } }

    // Update lsnAUIndex with by discarding lsn's strictly smaller than bdy
    // Removed (checked) due to lambda being total
    pub open spec/*(checked)*/ fn lsn_au_index_discarding_up_to(lsn_au_index: Map<LSN, AU>, bdy: LSN) -> (out: Map<LSN, AU>)
//     ensures
//         out.len(lsn_au_index),
//         forall |k| out.contains_key(k) :: bdy <= k,
//         forall |k| lsn_au_index.contains_key(k) && bdy <= k ==> out.contains_key(k),
    {
        Map::new(|lsn| lsn_au_index.contains_key(lsn) && bdy <= lsn,
                 |lsn| lsn_au_index[lsn])
    }

    // TODO(jonh): duplicates text in LikesJournal_v. Eww.
    pub open spec(checked) fn singleton_index(start_lsn: LSN, end_lsn: LSN, value: AU) -> (index: Map<LSN, AU>)
    {
        Map::new(|lsn| start_lsn <= lsn < end_lsn, |lsn| value)
    }

    // Update lsnAUIndex with additional lsn's from a new record
    pub open spec(checked) fn lsn_au_index_append_record(lsn_au_index: Map<LSN, AU>, msgs: MsgHistory, au: AU) -> (out: Map<LSN, AU>)
    recommends
        msgs.wf(),
        msgs.seq_start < msgs.seq_end,   // nonempty history
    // ensures LikesJournal::lsn_disjoint(lsn_au_index.dom(), msgs)
    //      ==> out.values() == lsn_au_index.values() + set![au]
    {
        // msgs is complete map from seqStart to seqEnd
        let update = Self::singleton_index(msgs.seq_start, msgs.seq_end, au);
        let out = lsn_au_index.union_prefer_right(update);
        // assertion here in dafny original
        out
    }

    pub open spec(checked) fn valid_next_journal_addr(self, addr: Address) -> bool {
        &&& self.mini_allocator.can_allocate(addr)
        &&& (self.mini_allocator.curr.is_None() ==> {
              &&& self.mini_allocator.allocs[addr.au].all_pages_free()
              &&& addr.page == 0
        })
        &&& (self.mini_allocator.curr.is_Some() && self.journal.journal.truncated_journal.freshest_rec.is_Some() ==>
                addr == self.journal.journal.truncated_journal.freshest_rec.unwrap().next_page())
    }


    pub open spec(checked) fn build_lsn_au_index_page_walk(dv: DiskView, root: Pointer) -> Map<LSN, AU>
    recommends
        dv.decodable(root),
        dv.acyclic(),
    decreases dv.the_rank_of(root)
        // TODO(chris): this when clause isn't working!
        when {
        // TODO(chris): oh look, &&&s not ,s! Let's run with that!
        &&& dv.decodable(root)
        &&& dv.acyclic()
    }
    {
        decreases_when({
            &&& dv.decodable(root)
            &&& dv.acyclic()
        });
//         decreases_by(Self::build_lsn_au_index_page_walk_proof);
        if root.is_None() { Map::empty() }
        else {
            let curr_msgs = dv.entries[root.unwrap()].message_seq;
            let update = Self::singleton_index(
                math::max(dv.boundary_lsn as int, curr_msgs.seq_start as int) as nat, curr_msgs.seq_end, root.unwrap().au);
            Self::build_lsn_au_index_page_walk(dv, dv.next(root)).union_prefer_right(update)
        }
    }

    pub open spec(checked) fn au_page_linked_in_order(dv: DiskView, addr: Address) -> bool
    {
        let prior_addr = Address{au: addr.au, page: (addr.page - 1) as nat};
        &&& dv.decodable(Some(prior_addr))
        &&& dv.next(Some(addr)) == Some(prior_addr)
    }

    // inv to prove transitive ranking
    // Every page in addr.au that is before addr (except page 0) is present
    // in the diskview and points to the one before it.
    pub open spec(checked) fn au_pages_linked_till_first_in_order(dv: DiskView, addr: Address) -> bool
    {
        forall |earlier: Address| #![auto] earlier.au == addr.au && 0 < earlier.page <= addr.page ==> Self::au_page_linked_in_order(dv, earlier)
        //forall |page: nat| #![auto] 0 < page <= addr.page ==> Self::au_page_linked_in_order(dv, Address{au: addr.au, page})
    }

    pub open spec(checked) fn internal_au_pages_fully_linked(dv: DiskView, first: AU) -> bool {
        forall |addr| #[trigger] dv.entries.contains_key(addr) && addr.au != first ==>
            Self::au_pages_linked_till_first_in_order(dv, addr)
    }

    pub proof fn transitive_ranking(dv: LinkedJournal_v::DiskView, root: Address, later: Address, first: AU)
    requires
        dv.decodable(Some(later)),
        dv.acyclic(),
        root.au != first,
        root.au == later.au,
        root.page <= later.page,
        Self::internal_au_pages_fully_linked(dv, first),
    // should be less than <= bc it's enough to prove termination, cause later is already < caller's root
    ensures
        dv.decodable(Some(root)),
        dv.the_rank_of(Some(root)) <= dv.the_rank_of(Some(later)),
    decreases later.page
    {
        if root == later { return; }


        // fonky trigger. wish I could add an ensures to au_pages_linked_till_first_in_order!
        //assert( Self::au_page_linked_in_order(dv, Address{au: later.au, page: later.page}) );
        assert( Self::au_page_linked_in_order(dv, later) ); // trigger

        //let prior = dv.entries[later].cropped_prior(dv.boundary_lsn);
        let prior = dv.next(Some(later));
        Self::transitive_ranking(dv, root, prior.unwrap(), first);
    }

    #[verifier(decreases_by)]
    pub proof fn build_lsn_au_index_au_walk_helper(dv: DiskView, root: Pointer, first: AU)
    {
        match root {
            None => {},
            Some(addr) => {
                if addr.au == first { }
                else {
                    // Nine lines of boilerplate to insert this one line in the right place. :v/
                    let bottom = first_page(root);
                    Self::transitive_ranking(dv, bottom.unwrap(), root.unwrap(), first);
                }
            }
        }
    }

    pub open spec/*(checked)*/ fn build_lsn_au_index_au_walk(dv: DiskView, root: Pointer, first: AU) -> Map<LSN, AU>
    recommends
        dv.decodable(root),
        dv.acyclic(),
        Self::internal_au_pages_fully_linked(dv, first),
    decreases dv.the_rank_of(root)
    {
        decreases_when({
            &&& dv.decodable(root)
            &&& dv.acyclic()
            &&& Self::internal_au_pages_fully_linked(dv, first)
        });
        decreases_by(Self::build_lsn_au_index_au_walk_helper);
        match root {
            None => map![],
            Some(addr) => {
                if addr.au == first { Self::build_lsn_au_index_page_walk(dv, root) }
                else {
                    // Jump over all the intermediate pages in the AU; we know how they're laid out already.
                    let bottom = first_page(root);
                    let last_lsn = dv.entries[root.unwrap()].message_seq.seq_end;
                    let first_lsn = dv.entries[bottom.unwrap()].message_seq.seq_start;
                    let update = Self::singleton_index(first_lsn, last_lsn, bottom.unwrap().au);
                    let prior_result = Self::build_lsn_au_index_au_walk(dv, dv.next(bottom), first);
                    prior_result.union_prefer_right(update)
                }
            }
        }
    }

    #[verifier(recommends_by)]
    pub proof fn build_lsn_au_index_helper(tj: TruncatedJournal, first: AU)
    {
        match tj.freshest_rec {
            None => {},
            Some(addr) => {
                if addr.au == first { }
                else {
                    Self::transitive_ranking(tj.disk_view, tj.freshest_rec.unwrap().first_page(), tj.freshest_rec.unwrap(), first);
                }
            }
        }
    }

    pub open spec(checked) fn build_lsn_au_index(tj: TruncatedJournal, first: AU) -> Map<LSN, AU>
    recommends
        tj.decodable(),
        Self::internal_au_pages_fully_linked(tj.disk_view, first),
    {
        recommends_by(Self::build_lsn_au_index_helper);
        Self::build_lsn_au_index_au_walk(tj.disk_view, tj.freshest_rec, first)
    }

    pub open spec(checked) fn wf_addrs(dv: DiskView) -> bool
    {
        forall |addr| #[trigger] dv.entries.contains_key(addr) ==> addr.wf()
    }

    pub open spec(checked) fn valid_journal_image(image: JournalImage) -> bool
    {
        &&& Self::wf_addrs(image.tj.disk_view)
        &&& image.tj.decodable()
        &&& Self::internal_au_pages_fully_linked(image.tj.disk_view, image.first)
        &&& Self::valid_first_au(image.tj.disk_view, image.first)
    }


    init!{ initialize(journal: LikesJournal::State, image: JournalImage) {
        require Self::valid_journal_image(image);
        require LikesJournal::State::initialize(journal, image.tj);
        let lsn_au_index = Self::build_lsn_au_index(image.tj, image.first);

        init journal = journal;
        init lsn_au_index = lsn_au_index;
        init first = image.first;
        init mini_allocator = MiniAllocator::empty();
    } }

    //////////////////////////////////////////////////////////////////////////////
    // AllocationJournalRefinement stuff
    //

    pub open spec(checked) fn addr_index_consistent_with_au_index(lsn_addr_index: Map<LSN, Address>, lsn_au_index: Map<LSN, AU>) -> bool
    {
        &&& lsn_addr_index.dom() =~= lsn_au_index.dom() // NB hiding a proof strategy behind that tilde. Ugh.
        &&& forall |lsn| #[trigger] lsn_addr_index.contains_key(lsn) ==> lsn_addr_index[lsn].au == lsn_au_index[lsn]
    }

    pub open spec(checked) fn journal_pages_not_free(addrs: Set<Address>, allocator: MiniAllocator) -> bool
    {
        forall |addr| #[trigger] addrs.contains(addr) ==> addr.wf() && !allocator.can_allocate(addr)
    }

    pub open spec(checked) fn mini_allocator_follows_freshest_rec(freshest_rec: Pointer, allocator: MiniAllocator) -> bool
    {
        allocator.curr.is_Some() ==> {
            &&& freshest_rec.is_Some()
            &&& freshest_rec.unwrap().au == allocator.curr.unwrap()
        }
    }

    pub open spec(checked) fn get_tj(self) -> TruncatedJournal
    {
        self.journal.journal.truncated_journal
    }

    pub open spec(checked) fn contiguous_lsns(lsn_au_index: Map<LSN, AU>, lsn1: LSN, lsn2: LSN, lsn3: LSN) -> bool
    {
        ({
            &&& lsn1 <= lsn2 <= lsn3
            &&& lsn_au_index.contains_key(lsn1)
            &&& lsn_au_index.contains_key(lsn3)
            &&& lsn_au_index[lsn1] == lsn_au_index[lsn3]
        }) ==> {
            &&& lsn_au_index.contains_key(lsn2)
            &&& lsn_au_index[lsn1] == lsn_au_index[lsn2]
        }
    }

    pub open spec(checked) fn aus_hold_contiguous_lsns(lsn_au_index: Map<LSN, AU>) -> bool
    {
        forall |lsn1, lsn2, lsn3| Self::contiguous_lsns(lsn_au_index, lsn1, lsn2, lsn3)
    }

    pub proof fn lemma_aus_hold_contiguous_lsns_inner(dv: DiskView, root: Pointer, first: AU)
    requires
        dv.decodable(root),
        dv.acyclic(),
        Self::internal_au_pages_fully_linked(dv, first),
    ensures
        Self::aus_hold_contiguous_lsns(Self::build_lsn_au_index_au_walk(dv, root, first)),
    {
        match root {
            None => {
                assert( Self::aus_hold_contiguous_lsns(Self::build_lsn_au_index_au_walk(dv, root, first)) );
            },
            Some(addr) => {
                if addr.au == first {
                    assume(false);
                    assert( Self::aus_hold_contiguous_lsns(Self::build_lsn_au_index_au_walk(dv, root, first)) );
                } else {
                    let bottom = first_page(root);
                    Self::transitive_ranking(dv, bottom.unwrap(), root.unwrap(), first);
                    let last_lsn = dv.entries[root.unwrap()].message_seq.seq_end;
                    let first_lsn = dv.entries[bottom.unwrap()].message_seq.seq_start;
                    let update = Self::singleton_index(first_lsn, last_lsn, bottom.unwrap().au);
                    let prior_result = Self::build_lsn_au_index_au_walk(dv, dv.next(bottom), first);
                    let result = prior_result.union_prefer_right(update);
                    assert({
                        &&& dv.decodable(root)
                        &&& dv.acyclic()
                        &&& Self::internal_au_pages_fully_linked(dv, first)
                    });
                        
                    assert( result == Self::build_lsn_au_index_au_walk(dv, root, first) );
                    if root.unwrap().page != 0 {
                        assume( false );
                        assert( Self::aus_hold_contiguous_lsns(Self::build_lsn_au_index_au_walk(dv, root, first)) );
                    } else {
                        let lsn_au_index = Self::build_lsn_au_index_au_walk(dv, root, first);
                        assert forall |lsn1, lsn2, lsn3| Self::contiguous_lsns(lsn_au_index, lsn1, lsn2, lsn3) by {
                            if ({
                                &&& lsn1 <= lsn2 <= lsn3
                                &&& lsn_au_index.contains_key(lsn1)
                                &&& lsn_au_index.contains_key(lsn3)
                                &&& lsn_au_index[lsn1] == lsn_au_index[lsn3]
                            }) {
                                if lsn3 < first_lsn {
                                    // recursive call
                                    assume( false );
                                    assert( lsn_au_index.contains_key(lsn2) );
                                    assert( lsn_au_index[lsn1] == lsn_au_index[lsn2] );
                                } else {
                                    assert( first_lsn <= lsn3 );
                                    assert( lsn3 < last_lsn );
                                    if lsn1 < first_lsn {
                                        assert( lsn_au_index[lsn3] == root.unwrap().au );
                                        assert( lsn_au_index[lsn1] != root.unwrap().au );
                                        assert( false );
                                    }
                                    assert( first_lsn <= lsn1 );
                                    // local
                                    assert( lsn_au_index.contains_key(lsn2) );
                                    assert( lsn_au_index[lsn1] == lsn_au_index[lsn2] );
                                }
                                
                            }
                        }
                        assert( Self::aus_hold_contiguous_lsns(Self::build_lsn_au_index_au_walk(dv, root, first)) );
                    }
                }
            }
        }
        
        assume(false);
    }

    pub proof fn lemma_aus_hold_contiguous_lsns(image: JournalImage)
    requires
        Self::valid_journal_image(image),
    ensures
        Self::aus_hold_contiguous_lsns(Self::build_lsn_au_index(image.tj, image.first)),
    {
        Self::lemma_aus_hold_contiguous_lsns_inner(image.tj.disk_view, image.tj.freshest_rec, image.first)
    }

    proof fn smaller_page_has_smaller_lsns(dv: DiskView, prior: Address, later: Address)
    requires
        dv.wf(),
        prior.au == later.au,
        prior.page < later.page,
        dv.entries.contains_key(later),
        Self::au_pages_linked_till_first_in_order(dv, later),
    ensures
        dv.entries.contains_key(prior),
        dv.entries[prior].message_seq.seq_end <= dv.entries[later].message_seq.seq_start,
    decreases later.page
    {
        assert( Self::au_page_linked_in_order(dv, later) ); // trigger?
        if prior.page + 1 < later.page {
            Self::smaller_page_has_smaller_lsns(dv, prior, Address{ page: (later.page-1) as nat, ..later});
        }
    }

    pub open spec fn addr_has_lsn(dv: DiskView, addr: Address, lsn: LSN) -> bool
    {
        &&& dv.entries.contains_key(addr)
        &&& dv.entries[addr].message_seq.contains(lsn)
    }

    pub open spec fn has_unique_lsns(dv: DiskView) -> bool
    {
        forall |lsn, addr1, addr2|
            Self::addr_has_lsn(dv, addr1, lsn) && Self::addr_has_lsn(dv, addr2, lsn)
            ==> addr1 == addr2
    }

    pub open spec(checked) fn valid_first_au(dv: DiskView, first: AU) -> bool
    {
        exists |addr: Address| #![auto] addr.au == first && Self::addr_has_lsn(dv, addr, dv.boundary_lsn)
    }

    #[invariant]
    pub open spec(checked) fn inv(self) -> bool {
        &&& self.wf()
        // The following is opaqued in AllocationJournalRefinement.
        // (Note: that suggests this is a good place to think about
        // building an isolation cell!)
        &&& LikesJournal_v::LikesJournal::State::inv(self.journal)
        &&& Self::addr_index_consistent_with_au_index(self.journal.lsn_addr_index, self.lsn_au_index)
        &&& Self::journal_pages_not_free(self.journal.lsn_addr_index.values(), self.mini_allocator)
        &&& Self::mini_allocator_follows_freshest_rec(self.get_tj().freshest_rec, self.mini_allocator)
        &&& Self::aus_hold_contiguous_lsns(self.lsn_au_index)
        &&& (self.get_tj().freshest_rec.is_Some()
            ==> Self::valid_first_au(self.get_tj().disk_view, self.first))
        &&& (self.get_tj().freshest_rec.is_Some()
            ==> Self::internal_au_pages_fully_linked(self.get_tj().disk_view, self.first))

        // TODO: miniAllocator can remove means that it's not in lsnauindex.values
    }

    #[inductive(freeze_for_commit)]
    fn freeze_for_commit_inductive(pre: Self, post: Self, lbl: Label, depth: nat, post_journal: LikesJournal::State) {
        reveal( LinkedJournal_v::LinkedJournal::State::next_by );
    }

    #[inductive(internal_mini_allocator_fill)]
    fn internal_mini_allocator_fill_inductive(pre: Self, post: Self, lbl: Label) {
        // hole in dafny proof
        assume(false);  // Dafny had several holes left to fill
    }

    #[inductive(internal_mini_allocator_prune)]
    fn internal_mini_allocator_prune_inductive(pre: Self, post: Self, lbl: Label) {
        // dafny had assume false, yet we don't need a proof here!?
    }

    proof fn invoke_submodule_inv(pre: Self, post: Self)
    requires
        Self::inv(pre),
    ensures
        post.journal.inv(),
    {
        assume(false);  // help, travis -- need access to this result
    }

    #[verifier::spinoff_prover]  // flaky proof
    proof fn discard_old_helper4(pre: Self, post: Self, lbl: Label, post_journal: LikesJournal::State, xaddr: Address, zaddr: Address)
    requires
        Self::inv(pre),
        Self::discard_old(pre, post, lbl, post_journal),
        post.get_tj().disk_view.entries.contains_key(zaddr),
        post.get_tj().seq_start() < post.get_tj().disk_view.entries[zaddr].message_seq.seq_start,
        post.get_tj().freshest_rec.is_Some(),
        zaddr.au != pre.first,
        zaddr.au != post.first,
        xaddr.au == zaddr.au,
        0 <= xaddr.page < zaddr.page,
    ensures
        post.get_tj().disk_view.entries.contains_key(xaddr),
    decreases zaddr.page - xaddr.page
    {
        let pre_dv = pre.get_tj().disk_view;
        let post_dv = post.get_tj().disk_view;
        Self::invoke_submodule_inv(pre, post);
        // Note to Pranav: here's a good example of a deep layer violation!
        let zpaged = post_dv.iptr(Some(zaddr));    // relies on LinkedJournal_Refinement
        assert( zpaged.is_Some() );
        let zpaged = zpaged.unwrap();
        let zlsn = post_dv.entries[zaddr].message_seq.seq_start;
        let ylsn = (zlsn - 1) as nat;
//         assert( post_dv.entries[zaddr].message_seq == zpaged.message_seq );
        assert( post_dv.entries[zaddr].message_seq.seq_start != 0 );
        assert( ylsn < post_dv.entries[zaddr].message_seq.seq_start );
        assert( post.journal.lsn_addr_index.contains_key(zlsn) && post.journal.lsn_addr_index[zlsn]==zaddr ) by {
            assert( post_dv.entries[zaddr].message_seq.contains(zlsn) );
        }
        assert( post.journal.lsn_addr_index.contains_key(zlsn) );
        assert( post.get_tj().seq_start() <= zlsn < post.get_tj().seq_end() ) by {
            reveal(LinkedJournal_v::TruncatedJournal::index_domain_valid);
        }

        assert( post.journal.lsn_addr_index.contains_key(zlsn) );
        assert( post_dv.entries[zaddr].message_seq.seq_start < post.get_tj().seq_end() ) by {
        }
        assert( ylsn < post.get_tj().seq_end() );
        if ylsn < post.get_tj().seq_start() {
            assert( zlsn == post.get_tj().seq_start() );
            assert( false );
        }
        assert( post.get_tj().seq_start() <= ylsn );
        assert( post.get_tj().seq_start() <= ylsn ) by {    // all redundant with prev line
            if ylsn < post.get_tj().seq_start() {
                assert( post.lsn_au_index.contains_key(post_dv.boundary_lsn) );
                assert( post.lsn_au_index[post_dv.boundary_lsn] == zaddr.au );
                assert( false );
            }
            // argument about first
        }

        let yaddr = Address{au: zaddr.au, page: (zaddr.page - 1) as nat};
        let y0lsn = post_dv.entries[yaddr].message_seq.seq_start;

        assert( post.get_tj().seq_start() < y0lsn ) by {
            if y0lsn <= post.get_tj().seq_start() {
                assert( y0lsn <= post_dv.boundary_lsn );
                assert( post_dv.boundary_lsn <= ylsn );

                // TODO(chris): if I replace the two lines above with this single assert, the proof
                // falls apart. That's ... extremely counterintuitive.
                // In fact, if I ADD this line, keeping those above, the proof falls apart!! That's
                // crazy.
                //assert( y0lsn <= post_dv.boundary_lsn <= ylsn );
                // ...maybe it's just flakiness. This proof seems EXTREMELY brittle.

                assert( Self::contiguous_lsns(post.lsn_au_index, y0lsn, post_dv.boundary_lsn, ylsn) );
                assert( y0lsn <= post_dv.boundary_lsn <= ylsn );

                assume(false);  // THIS PROOF IS HELLA FLAKY; address later
                assert( post_dv.entries[yaddr].message_seq.contains(y0lsn) );   //trigger

                assert( post.journal.lsn_addr_index.contains_key(y0lsn) );
                assert( post.journal.lsn_addr_index.dom().contains(y0lsn) );
                assert( post.lsn_au_index.contains_key(y0lsn) );
                assert( post.lsn_au_index.contains_key(ylsn) );
                assert( post.lsn_au_index[y0lsn] == post.lsn_au_index[ylsn] );
                assert( post.lsn_au_index.contains_key(post_dv.boundary_lsn) );
                assert( post.lsn_au_index[post_dv.boundary_lsn] == zaddr.au );
                assert( false );
            }
        }

        //assert( Self::au_page_linked_in_order(pre_dv, Address{au: zaddr.au, page: zaddr.page}) );
        assert( Self::au_page_linked_in_order(pre_dv, zaddr) ); // trigger

        if xaddr != yaddr {
            assert( post.get_tj().seq_start() < y0lsn );
            Self::discard_old_helper4(pre, post, lbl, post_journal, xaddr, yaddr);
        }
    }

    #[inductive(discard_old)]
    fn discard_old_inductive(pre: Self, post: Self, lbl: Label, post_journal: LikesJournal::State) {
        reveal( LikesJournal_v::LikesJournal::State::next );
        reveal( LikesJournal_v::LikesJournal::State::next_by );
        //reveal( LinkedJournal_v::LinkedJournal::State::next );
        reveal( LinkedJournal_v::LinkedJournal::State::next_by );

        Self::invoke_submodule_inv(pre, post);
        assert( post.wf() );
        assert( Self::addr_index_consistent_with_au_index(post.journal.lsn_addr_index, post.lsn_au_index) );
        assert( Self::journal_pages_not_free(post.journal.lsn_addr_index.values(), post.mini_allocator) );
        if post.get_tj().freshest_rec.is_Some() && post.get_tj().freshest_rec.is_None() {
            assert( pre.journal.lsn_addr_index.values().contains(pre.get_tj().freshest_rec.unwrap()) );
            assert( post.journal.lsn_addr_index =~~= map![] );
        }
        assert( Self::mini_allocator_follows_freshest_rec(post.get_tj().freshest_rec, post.mini_allocator) );
        assert forall |lsn1,lsn2,lsn3| Self::contiguous_lsns(post.lsn_au_index, lsn1, lsn2, lsn3) by
        {
            if {
                &&& lsn1 <= lsn2 <= lsn3
                &&& post.lsn_au_index.contains_key(lsn1)
                &&& post.lsn_au_index.contains_key(lsn3)
                &&& post.lsn_au_index[lsn1] == post.lsn_au_index[lsn3]
            } {
                assert( Self::contiguous_lsns(pre.lsn_au_index, lsn1, lsn2, lsn3) );
            }
            assert( Self::contiguous_lsns(post.lsn_au_index, lsn1, lsn2, lsn3) );
        }

        if post.get_tj().freshest_rec.is_Some() {
            assert( Self::valid_first_au(post.get_tj().disk_view, post.first) ) by {
                reveal(LinkedJournal_v::TruncatedJournal::index_domain_valid);
                assume( false ); // TODO defn refactoring broke this
//                assume( Self::valid_first_au(post.get_tj().disk_view, post.first) );    // TODO stronger defn broke this
            }
            let start_lsn = lbl.get_DiscardOld_start_lsn();

            assert forall |addr| ({
                    &&& post.get_tj().disk_view.entries.contains_key(addr)
                    &&& addr.au != post.first
                }) implies #[trigger] Self::au_pages_linked_till_first_in_order(post.get_tj().disk_view, addr) by {

                let lsn = choose |lsn| #![auto] post.journal.lsn_addr_index.contains_key(lsn) && post.journal.lsn_addr_index[lsn] == addr;
                if addr.au == pre.first {
                    assert( Self::contiguous_lsns(pre.lsn_au_index, pre.get_tj().disk_view.boundary_lsn, start_lsn, lsn) );
                    assert( false );
                } else {
                    assert( Self::au_pages_linked_till_first_in_order(pre.get_tj().disk_view, addr) );
                    assert( post.get_tj().index_keys_map_to_valid_entries(post.journal.lsn_addr_index) );
                    post.get_tj().instantiate_index_keys_map_to_valid_entries(post.journal.lsn_addr_index, lsn);
                    assert forall |earlier: Address| earlier.au == addr.au && 0 < earlier.page <= addr.page
                    implies #[trigger] Self::au_page_linked_in_order(post.get_tj().disk_view, earlier) by {
                        //let caddr = Address{au: addr.au, page: earlier.page};
                        let caddr = earlier;
                        let prior_addr = Address{au: caddr.au, page: (caddr.page - 1) as nat};
                        let pre_dv = pre.get_tj().disk_view;
                        let post_dv = post.get_tj().disk_view;
                        let clsn = post_dv.entries[caddr].message_seq.seq_start;
                        let alsn = post_dv.entries[addr].message_seq.seq_start;
                        assert( post.get_tj().seq_start() < alsn ) by {
                            assert( post_dv.entries.contains_key(addr) );
                            assert( post_dv.entries[addr].message_seq.contains(alsn) );
                        }
                        if earlier.page < addr.page {
                            Self::discard_old_helper4(pre, post, lbl, post_journal, caddr, addr);
                        }
                        Self::discard_old_helper4(pre, post, lbl, post_journal, prior_addr, addr);
                        assert( post_dv.decodable(Some(prior_addr)) );
                        assert( Self::au_page_linked_in_order(pre_dv, caddr) );
                        //assert( pre_dv.next(Some(caddr)) == Some(Address{au: addr.au, page: (addr.page - 1) as nat}) );
                        assert( pre_dv.decodable(Some(prior_addr)) );
                        assert( pre_dv.next(Some(caddr)) == Some(prior_addr) );
                        assert( post.get_tj().seq_start() < clsn ) by {
                            assert( post_dv.entries.contains_key(caddr) );
                            assert( post_dv.entries[caddr].message_seq.contains(clsn) );
                        }
                        assert( post_dv.entries.contains_key(caddr) );
                        assert( post_dv.entries[caddr] == pre_dv.entries[caddr] );
                        assert( post_dv.decodable(Some(prior_addr)) );
                        assert( post_dv.next(Some(caddr)) == Some(prior_addr) );
                        //assert( post_dv.next(Some(addr)) == Some(prior_addr) );
                        assert( Self::au_page_linked_in_order(post_dv, caddr) );
                    }
                }
            }
        }

        assert( post.inv() );
    }

    #[inductive(internal_journal_marshal)]
    fn internal_journal_marshal_inductive(pre: Self, post: Self, lbl: Label, cut: LSN, addr: Address, post_linked_journal: LinkedJournal_v::LinkedJournal::State) {
        let discard_msgs = pre.journal.journal.unmarshalled_tail.discard_recent(cut);
        assert( LikesJournal_v::lsn_disjoint(pre.lsn_au_index.dom(), discard_msgs) ) by {
            reveal(LinkedJournal_v::TruncatedJournal::index_domain_valid);
        }
        assume(false);
    }

    // TODO(jonh): this lemma should just be an ensures on build_lsn_au_index_page_walk.
    proof fn build_lsn_au_index_page_walk_consistency(dv: DiskView, root: Pointer)
    requires
        dv.decodable(root),
        dv.acyclic(),
    ensures
        Self::addr_index_consistent_with_au_index(
            dv.build_lsn_addr_index(root),
            Self::build_lsn_au_index_page_walk(dv, root)),
    decreases dv.the_rank_of(root)
    {
        if root.is_Some() {
            Self::build_lsn_au_index_page_walk_consistency(dv, dv.next(root));
        }
    }

    pub open spec fn pointer_is_upstream(dv: DiskView, root: Pointer, first: AU) -> bool
    {
        &&& dv.decodable(root)
        &&& dv.acyclic()
        &&& Self::internal_au_pages_fully_linked(dv, first)
        &&& Self::valid_first_au(dv, first)
        &&& Self::has_unique_lsns(dv)
        &&& root.is_Some() ==> dv.boundary_lsn < dv.entries[root.unwrap()].message_seq.seq_end
    }
    
    // TODO(jonh): this lemma should just be an ensures on build_lsn_au_index_au_walk.
    proof fn build_lsn_au_index_au_walk_consistency(dv: DiskView, root: Pointer, first: AU)
    requires
        Self::pointer_is_upstream(dv, root, first),
    ensures
        Self::addr_index_consistent_with_au_index(
            dv.build_lsn_addr_index(root),
            Self::build_lsn_au_index_au_walk(dv, root, first)),
    decreases dv.the_rank_of(root)
    {
        match root {
            None => { },
            Some(addr) => {
                if addr.au == first {
                    Self::build_lsn_au_index_page_walk_consistency(dv, root);
                }
                else {
                    if root.unwrap().page != 0 {
                        // Walk back a single page, unwinding the Likes index one step.
                        assert( Self::au_page_linked_in_order(dv, root.unwrap()) ); // trigger
                        Self::build_lsn_au_index_au_walk_consistency(dv, dv.next(root), first); // recursive call
                        let bottom = first_page(root);
                        Self::smaller_page_has_smaller_lsns(dv, bottom.unwrap(), root.unwrap());
                    } else {
                        // Recurse this function to turn an AU corner.
                        assert( Self::pointer_is_upstream(dv, dv.next(root), first) );
                        Self::build_lsn_au_index_au_walk_consistency(dv, dv.next(root), first);

                        if dv.entries[root.unwrap()].message_seq.seq_start < dv.boundary_lsn {
                            assert( Self::addr_has_lsn(dv, root.unwrap(), dv.boundary_lsn) );
                            assert( false );
                        }
                    }
                }
            }
        }
    }

    #[inductive(internal_journal_no_op)]
    fn internal_journal_no_op_inductive(pre: Self, post: Self, lbl: Label, post_linked_journal: LinkedJournal_v::LinkedJournal::State) { }

    #[inductive(initialize)]
    fn initialize_inductive(post: Self, journal: LikesJournal::State, image: JournalImage) {
        //assert( post.journal.lsn_au_index = Linked::build_lsn_au_index(image.tj, image.first);
        assume( LikesJournal_v::LikesJournal::State::inv(post.journal) );   // TODO(travis): help!

        let TruncatedJournal{disk_view: dv, freshest_rec: root} = image.tj;
        Self::build_lsn_au_index_au_walk_consistency(dv, root, image.first);
        Self::lemma_aus_hold_contiguous_lsns(image);
    }

    #[inductive(only_advance_likes_journal)]
    fn only_advance_likes_journal_inductive(pre: Self, post: Self, lbl: Label, depth: nat, post_likes_journal: LikesJournal::State) {
        reveal( LikesJournal_v::LikesJournal::State::next );
        reveal( LikesJournal_v::LikesJournal::State::next_by );
        reveal( LinkedJournal_v::LinkedJournal::State::next_by );
    }
    
    // lemmas used by other refinements
    proof fn discard_old_accessible_aus(pre: Self, post: Self, lbl: Label)
    requires
        Self::next(pre, post, lbl),
        lbl.is_DiscardOld(),
    ensures
        post.accessible_aus() == pre.accessible_aus() - lbl.get_DiscardOld_deallocs(),
    {
        assume(false);  // left off
    }

} } // state_machine
} // verus
