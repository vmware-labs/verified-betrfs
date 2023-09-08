// Copyright 2018-2021 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, and University of Washington
// SPDX-License-Identifier: BSD-2-Clause
//
#![allow(unused_imports)]
use builtin::*;
use vstd::prelude::*;

use builtin_macros::*;
use state_machines_macros::state_machine;

use vstd::prelude::*;
use vstd::map::*;
use vstd::math;
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

        // AU of the first journal record, boundarylsn can be found in this AU
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
    pub open spec(checked) fn lsn_au_index_discarding_up_to(lsn_au_index: Map<LSN, AU>, bdy: LSN) -> (out: Map<LSN, AU>)
//     ensures
//         out.len(lsn_au_index),
//         forall |k| out.contains_key(k) :: bdy <= k,
//         forall |k| lsn_au_index.contains_key(k) && bdy <= k ==> out.contains_key(k),
    {
        Map::new(|lsn| lsn_au_index.contains_key(lsn) && bdy <= lsn,
                 |lsn| lsn_au_index[lsn])
    }

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
        forall |page: nat| #![auto] 0 < page <= addr.page ==> Self::au_page_linked_in_order(dv, Address{au: addr.au, page})
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
        assert( Self::au_page_linked_in_order(dv, Address{au: later.au, page: later.page}) );

        //let prior = dv.entries[later].cropped_prior(dv.boundary_lsn);
        let prior = dv.next(Some(later));
        Self::transitive_ranking(dv, root, prior.unwrap(), first);
    }

    #[verifier(decreases_by)]
    pub proof fn build_lsn_au_index_au_walk_helper(dv: DiskView, root: Address, last: LSN, first: AU)
    {
        let prior = dv.entries[root].cropped_prior(dv.boundary_lsn);
        if prior.is_None() { }
        else if prior.unwrap().au == first { }
        else {
            // Nine lines of boilerplate to insert this one line in the right place. :v/
            Self::transitive_ranking(dv, prior.unwrap().first_page(), prior.unwrap(), first);
        }
    }

    pub open spec(checked) fn build_lsn_au_index_au_walk(dv: DiskView, root: Address, last: LSN, first: AU) -> Map<LSN, AU>
    recommends
        dv.decodable(Some(root)),
        dv.acyclic(),
        root.au != first,
        root.page == 0,
        Self::internal_au_pages_fully_linked(dv, first),
    decreases dv.the_rank_of(Some(root))
    {
        decreases_when({
            &&& dv.decodable(Some(root))
            &&& dv.acyclic()
            &&& root.au != first
            &&& root.page == 0
            &&& Self::internal_au_pages_fully_linked(dv, first)
        });
        decreases_by(Self::build_lsn_au_index_au_walk_helper);
        // we jump to the first page of each AU and perform an AU walk skipping over pages in the middle
        let curr_msgs = dv.entries[root].message_seq;
        let update = Self::singleton_index(
            math::max(dv.boundary_lsn as int, curr_msgs.seq_start as int) as nat, last, root.au);
        let prior = dv.entries[root].cropped_prior(dv.boundary_lsn);
        let prior_result =
            if prior.is_None() { map![] }
            else if prior.unwrap().au == first { Self::build_lsn_au_index_page_walk(dv, prior) }
            else {
                //Self::transitive_ranking(dv, prior.unwrap().first_page(), prior.unwrap(), first);
                Self::build_lsn_au_index_au_walk(dv, prior.unwrap().first_page(), curr_msgs.seq_start, first)
            };
        prior_result.union_prefer_right(update)
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
        match tj.freshest_rec {
            None => map![],
            Some(addr) =>
                // if we are looking at address from the first AU, just walk the pages
                if addr.au == first { Self::build_lsn_au_index_page_walk(tj.disk_view, tj.freshest_rec) }
                else {
                    let last = tj.disk_view.entries[addr].message_seq.seq_end;
                    Self::build_lsn_au_index_au_walk(tj.disk_view, addr.first_page(), last, first)
                }
        }
    }

    pub open spec(checked) fn wf_addrs(dv: DiskView) -> bool
    {
        forall |addr| #[trigger] dv.entries.contains_key(addr) ==> addr.wf()
    }

    pub open spec(checked) fn valid_journal_image(image: JournalImage) -> bool
    {
        &&& Self::wf_addrs(image.tj.disk_view)
        &&& Self::internal_au_pages_fully_linked(image.tj.disk_view, image.first)
    }

    init!{ initialize(journal: LikesJournal::State, image: JournalImage) {
        require Self::valid_journal_image(image);
        require LikesJournal::State::initialize(journal, image.tj);
        init journal = journal;
        init lsn_au_index = Self::build_lsn_au_index(image.tj, image.first);
        init first = image.first;
        init mini_allocator = MiniAllocator::empty();
    } }

    //////////////////////////////////////////////////////////////////////////////
    // AllocationJournalRefinement stuff
    //

    pub open spec(checked) fn addr_index_consistent_with_au_index(lsn_addr_index: Map<LSN, Address>, lsn_au_index: Map<LSN, AU>) -> bool
    {
        &&& lsn_addr_index.dom() == lsn_au_index.dom()
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

    pub open spec(checked) fn valid_first_au(dv: DiskView, lsn_au_index: Map<LSN, AU>, first: AU) -> bool
    {
        &&& lsn_au_index.contains_key(dv.boundary_lsn)
        &&& lsn_au_index[dv.boundary_lsn] == first
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
            ==> Self::valid_first_au(self.get_tj().disk_view, self.lsn_au_index, self.first))
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

    proof fn smaller_page_has_smaller_lsns(dv: DiskView, prior: Address, later: Address)
    requires
        dv.wf(),
        prior.au == later.au,
        prior.page < later.page,
        Self::au_pages_linked_till_first_in_order(dv, later),
    ensures
        dv.entries.contains_key(prior),
        dv.entries.contains_key(later),
        dv.entries[prior].message_seq.seq_end <= dv.entries[later].message_seq.seq_start,
    {
        assume(false); // left off porting proof
    }

    proof fn invoke_submodule_inv(pre: Self, post: Self)
    requires
        Self::inv(pre),
    ensures
        post.journal.inv(),
    {
        assume(false);  // help, travis -- need access to this result
    }

    #[inductive(discard_old)]
    fn discard_old_inductive(pre: Self, post: Self, lbl: Label, post_journal: LikesJournal::State) {
        reveal( LikesJournal_v::LikesJournal::State::next );
        reveal( LikesJournal_v::LikesJournal::State::next_by );
        reveal( LinkedJournal_v::LinkedJournal::State::next );
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
            assert( Self::valid_first_au(post.get_tj().disk_view, post.lsn_au_index, post.first) ) by {

                assume(false);  // not sure what's missing, but likes_journal_inv
                reveal(LinkedJournal_v::TruncatedJournal::index_domain_valid);
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
                    assert forall |page| 0 < page <= addr.page
                    implies #[trigger] Self::au_page_linked_in_order(post.get_tj().disk_view, Address{au: addr.au, page}) by {
                        let prior_addr = Address{au: addr.au, page};
                        assert( Self::au_page_linked_in_order(pre.get_tj().disk_view, prior_addr) );
                        assume(false);  // fell apart
                        assert( pre.get_tj().disk_view.next(Some(prior_addr.next_page())) == Some(prior_addr) );
                        assert( pre.get_tj().disk_view.entries.contains_key(prior_addr) );
                        assert( pre.journal.lsn_addr_index.values().contains(prior_addr) );
                        let prior_addr_lsn = choose |prior_addr_lsn| #![auto] pre.journal.lsn_addr_index.contains_key(prior_addr_lsn) && pre.journal.lsn_addr_index[prior_addr_lsn] == prior_addr;
                        assert( pre.get_tj().index_keys_map_to_valid_entries(pre.journal.lsn_addr_index) );
                        //pre.get_tj().instantiate_index_keys_map_to_valid_entries(pre.journal.lsn_addr_index, prior_addr_lsn);

                        if prior_addr_lsn <= start_lsn {
                            Self::smaller_page_has_smaller_lsns(pre.get_tj().disk_view, prior_addr, addr);
                            assert( prior_addr_lsn <= lsn );
                            assert( Self::contiguous_lsns(pre.lsn_au_index, prior_addr_lsn, start_lsn, lsn) );
                            assert( false );
                        }
                        assert( start_lsn < prior_addr_lsn );   // TODO dup delete
                        post.get_tj().instantiate_index_keys_map_to_valid_entries(post.journal.lsn_addr_index, prior_addr_lsn);
                        assert( post.get_tj().disk_view.entries.contains_key(prior_addr) );
                    }
                }
            }
        }

        assert( post.inv() );
    }

    #[inductive(internal_journal_marshal)]
    fn internal_journal_marshal_inductive(pre: Self, post: Self, lbl: Label, cut: LSN, addr: Address, post_linked_journal: LinkedJournal_v::LinkedJournal::State) {
        assume(false);  // Dafny had several holes left to fill
    }

    #[inductive(internal_journal_no_op)]
    fn internal_journal_no_op_inductive(pre: Self, post: Self, lbl: Label, post_linked_journal: LinkedJournal_v::LinkedJournal::State) { }

    #[inductive(initialize)]
    fn initialize_inductive(post: Self, journal: LikesJournal::State, image: JournalImage) {
        //reveal( LikesJournal::State::initialize );
        //LikesJournal::State::initialize_inductive(post.journal);
        assume(false);  // left off
        assert( LikesJournal_v::LikesJournal::State::inv(post.journal) );
        assert( Self::addr_index_consistent_with_au_index(post.journal.lsn_addr_index, post.lsn_au_index) );
        assert( post.get_tj().freshest_rec.is_Some()
            ==> Self::internal_au_pages_fully_linked(post.get_tj().disk_view, post.first) );
        assert( post.inv() );
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
