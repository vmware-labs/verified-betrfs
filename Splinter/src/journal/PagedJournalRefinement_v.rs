// Copyright 2018-2024 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, University of Washington
// SPDX-License-Identifier: BSD-2-Clause

#![allow(unused_imports)]

use builtin::*;

use builtin_macros::*;

use vstd::{calc_macro::*};


use vstd::prelude::*;
use vstd::map::*;
use vstd::seq_lib::*;
use crate::abstract_system::StampedMap_v::LSN;
use crate::abstract_system::MsgHistory_v::*;
use crate::abstract_system::AbstractJournal_v::*;
use crate::journal::PagedJournal_v::*;

verus! {

impl JournalRecord {
    // TODO(jonh): WHY ISN'T THIS written relative to cropped_prior!?
    // I suspect I wrote the dfy version of this before the cropped_prior
    // discipline was done consistently.
    pub open spec /*XXX (checked)*/ fn i(self, boundary_lsn: LSN) -> MsgHistory
    recommends
        self.wf(),
    decreases self
    {
        if self.message_seq.can_discard_to(boundary_lsn)
            { self.message_seq.discard_old(boundary_lsn) } // and don't deref the prior_rec!
        else {
// XXX this doesn't seem to satisfy the corresponding recommends in i_opt.
//             let _ = spec_affirm( (*self.prior_rec).is_some()
//                                 ==> (*self.prior_rec).unwrap().valid(boundary_lsn) );
            Self::i_opt(*self.prior_rec, boundary_lsn).concat(self.message_seq)
        }
    }

    // Not sure why i can't prove this recommends
    pub open spec /*XXX (checked)*/ fn i_opt(ojr: Option<Self>, boundary_lsn: LSN) -> MsgHistory
    recommends
        ojr is Some ==> ojr.unwrap().valid(boundary_lsn),
    decreases ojr
    {
        match ojr {
            None => MsgHistory::empty_history_at(boundary_lsn),
            Some(rec) => rec.i(boundary_lsn)
        }
    }

    // TODO(chris): another 50 lines to do what a single-line 'ensures' on a recursive definition did in Dafny.
    pub proof fn i_lemma(self, boundary_lsn: LSN)
    requires
        self.valid(boundary_lsn),
    ensures ({
        let out = self.i(boundary_lsn);
        &&& out.wf()
        &&& out.seq_start == boundary_lsn
        &&& out.seq_end === self.message_seq.seq_end
        })
    decreases self
    {
        // whole lotta copy-pasted boilerplate :v(
        if self.message_seq.can_discard_to(boundary_lsn)
        {
        }
        else
        {
            let ojr = *self.prior_rec;
            match ojr {
                None => {},
                Some(rec) => {rec.i_lemma(boundary_lsn)},
            }
        }
    }

    pub proof fn i_lemma_forall()
    ensures
        forall |selff: Self, boundary_lsn: LSN|
            selff.valid(boundary_lsn)
            ==>
            ({
            let out = selff.i(boundary_lsn);
            &&& out.wf()
            &&& out.seq_start == boundary_lsn
            &&& out.seq_end === selff.message_seq.seq_end
            })
    {
        assert forall |selff: Self, boundary_lsn: LSN|
            selff.valid(boundary_lsn)
            implies
            ({
            let out = selff.i(boundary_lsn);
            &&& out.wf()
            &&& out.seq_start == boundary_lsn
            &&& out.seq_end === selff.message_seq.seq_end
            }) by {
            selff.i_lemma(boundary_lsn);
        }
    }

    pub proof fn cant_crop(self, bdy: LSN, depth: nat)
    requires
        0 < depth,
        self.can_crop_head_records(bdy, (depth-1) as nat),
        self.crop_head_records(bdy, (depth-1) as nat) is Some,
        self.crop_head_records(bdy, (depth-1) as nat).unwrap().message_seq.can_discard_to(bdy),
    ensures
        !self.can_crop_head_records(bdy, depth+1)
    decreases depth
    {
        Self::opt_rec_crop_head_records_lemma_forall();
        if 1 < depth {
            self.cropped_prior(bdy).unwrap().cant_crop(bdy, (depth-1) as nat);
        }
    }

    pub proof fn crop_head_records_chaining(self, bdy: LSN, depth: nat)
    requires
        0 < depth,
        self.can_crop_head_records(bdy, (depth-1) as nat),
        self.crop_head_records(bdy, (depth-1) as nat) is Some,
        self.can_crop_head_records(bdy, depth),
    ensures
        self.crop_head_records(bdy, (depth-1) as nat).unwrap().cropped_prior(bdy) == self.crop_head_records(bdy, depth),
    decreases depth
    {
        Self::opt_rec_crop_head_records_lemma_forall();
        if 1<depth {
            self.cropped_prior(bdy).unwrap().crop_head_records_chaining(bdy, (depth-1) as nat);
            // Dafny didn't need this trigger
            assert(
                self.crop_head_records(bdy, depth)
                ==
                Self::opt_rec_crop_head_records(self.cropped_prior(bdy), bdy, (depth-1) as nat)
            );
        }
    }

    pub proof fn cropped_subseq_in_interpretation(self, bdy: LSN, depth: nat, msgs: MsgHistory)
    requires
        msgs.wf(),
        self.can_crop_head_records(bdy, depth+1),
        self.can_crop_head_records(bdy, depth),
        self.crop_head_records(bdy, depth) is Some,
        self.crop_head_records(bdy, depth).unwrap().i(bdy).includes_subseq(msgs),
    ensures
        0 < depth ==> self.can_crop_head_records(bdy, (depth-1) as nat),
        self.crop_head_records(bdy, 0).unwrap().i(bdy).includes_subseq(msgs),
    decreases depth
    {
        Self::i_lemma_forall();
        //Self::opt_rec_crop_head_records_lemma_forall(); // TODO(jonh): implicit defn ensures worked in Dafny; wrong trigger here
        if 0 < depth {
            self.can_crop_monotonic(bdy, (depth-1) as nat, depth);
            self.can_crop_more_yields_some(bdy, (depth-1) as nat, depth);
            let self_pre = self.crop_head_records(bdy, (depth-1) as nat).unwrap();
//            assert(!self_pre.message_seq.can_discard_to(bdy)) by {
//                if self_pre.message_seq.can_discard_to(bdy) {
//                    self.cant_crop(bdy, depth);
////                    assert(false);  // contradiction
//                }
//            }
            self.crop_head_records_chaining(bdy, depth);

            // TODO(chris): couldn't trigger forall version successfully, so manual invocation.
            self.crop_head_records_lemma(bdy, (depth-1) as nat);

            self.cropped_subseq_in_interpretation(bdy, (depth-1) as nat, msgs);
        }
    }

    pub proof fn can_cut_more(ojr: Option<JournalRecord>, bdy: LSN, depth: nat)
    requires
        0 < depth,
        Self::opt_rec_can_crop_head_records(ojr, bdy, depth),
    ensures
        Self::opt_rec_can_crop_head_records(ojr, bdy, (depth-1) as nat),
        Self::opt_rec_can_crop_head_records(Self::opt_rec_crop_head_records(ojr, bdy, (depth-1) as nat), bdy, 1),
    decreases depth
    {
        if 1 < depth {
            // TODO(verus): new trigger, uneeded in Dafny. (dozens of lines of debugging behind this discovery)
            assert( ojr.unwrap().can_crop_head_records(bdy, depth) ); 
            // Interestingly Dafny proof had an unecessary call to can_crop_monotonic I removed.
            Self::can_cut_more(*ojr.unwrap().prior_rec, bdy, (depth-1) as nat);
        }
    }
        
    pub proof fn crop_equivalence(ojr: Option<JournalRecord>, bdy: LSN, depth: nat)
    requires
        0 < depth,
        ojr is Some ==> ojr.unwrap().valid(bdy),
        Self::opt_rec_can_crop_head_records(ojr, bdy, (depth-1) as nat),
        Self::opt_rec_can_crop_head_records(ojr, bdy, depth),
    ensures
        Self::opt_rec_can_crop_head_records(Self::opt_rec_crop_head_records(ojr, bdy, (depth-1) as nat), bdy, 1),
        Self::opt_rec_crop_head_records(ojr, bdy, depth) ==
            Self::opt_rec_crop_head_records(Self::opt_rec_crop_head_records(ojr, bdy, (depth-1) as nat), bdy, 1),
    decreases depth
    {
        // HOORAY! This one went through with only syntactic translation, no new triggers and no
        // debugging to get there! That's the first time that has happened...
        if 1 < depth {
            Self::can_cut_more(ojr, bdy, depth);
            ojr.unwrap().can_crop_more_yields_some(bdy, (depth-1) as nat, depth);
            Self::crop_equivalence(*ojr.unwrap().prior_rec, bdy, (depth-1) as nat);
        }
    }

    // This lemma swelled to 58 lines during debugging to find the three new missing calls. :v(
    pub proof fn discard_old_maintains_subseq(ojr: Option<JournalRecord>, old_bdy: LSN, new_bdy: LSN)
    requires
        old_bdy <= new_bdy,
        ojr is None ==> new_bdy == old_bdy,
        ojr is Some ==> new_bdy < ojr.unwrap().message_seq.seq_end,
        ojr is Some ==> ojr.unwrap().valid(old_bdy),
    ensures
        ojr is Some ==> ojr.unwrap().valid(new_bdy),
        Self::i_opt(ojr, old_bdy).includes_subseq(Self::i_opt(Self::discard_old_journal_rec(ojr, new_bdy), new_bdy)),
    decreases ojr
    {
        Self::i_lemma_forall(); // new text; needed a dozen lines of debugging to find it.
        Self::option_new_boundary_valid(ojr, old_bdy, new_bdy);
        if ojr is Some && new_bdy < ojr.unwrap().message_seq.seq_start {
            Self::discard_old_maintains_subseq(*ojr.unwrap().prior_rec, old_bdy, new_bdy);

            let prior = *ojr.unwrap().prior_rec;
            Self::discard_old_journal_rec_ensures(prior, new_bdy);  // new manual invocation of what Dafny did with an ensures-broadcast
            // of the dozens of lines of debugging I wrote, here's one I had to do manually because
            // I didn't have requires on spec(checked) fns.
//            Self::discard_old_journal_rec(prior, new_bdy).unwrap().i_lemma(new_bdy);
            let priornew = Self::i_opt(Self::discard_old_journal_rec(prior, new_bdy), new_bdy);
            priornew.concat_lemma(ojr.unwrap().message_seq);    // new manual invocation of what Dafny did with an ensures-broadcast
        }
    }

    pub proof fn crop_head_maintains_subseq(ojr: Option<JournalRecord>, bdy: LSN, depth: nat)
    requires
        ojr is Some ==> ojr.unwrap().valid(bdy),
        Self::opt_rec_can_crop_head_records(ojr, bdy, depth),
    ensures
        Self::i_opt(ojr, bdy).includes_subseq(Self::i_opt(Self::opt_rec_crop_head_records(ojr, bdy, depth), bdy)),
    decreases depth
    {
        if depth > 0 {
            ojr.unwrap().can_crop_monotonic(bdy, (depth-1) as nat, depth);
            Self::crop_head_maintains_subseq(ojr, bdy, (depth-1) as nat);
            let small = Self::opt_rec_crop_head_records(ojr, bdy, (depth-1) as nat);
            let smaller = Self::opt_rec_crop_head_records(ojr, bdy, depth);
            Self::crop_equivalence(ojr, bdy, depth);

            Self::i_lemma_forall();   // newly required
            assert(small.unwrap().crop_head_records(bdy, 1) == Self::opt_rec_crop_head_records(small.unwrap().cropped_prior(bdy), bdy, 0) );  // trigger, newly required

//            assert( Self::i_opt(small, bdy).includes_subseq(Self::i_opt(smaller, bdy)) );   // trigger (ported from Dafny)
        }
    }

    // This was a 3-line proof in Dafny. It ballooned to 98 lines trying to find the triggers for
    // lemmas I need now that I didn't then. :'v(
    pub proof fn discard_old_defn_interprets(ojr: Option<JournalRecord>, old_lsn: LSN, new_lsn: LSN)
    requires
        ojr is Some ==> ojr.unwrap().valid(old_lsn),
        ojr is Some ==> ojr.unwrap().valid(new_lsn),
        Self::i_opt(ojr, old_lsn).can_discard_to(new_lsn),
    ensures
        Self::i_opt(Self::discard_old_journal_rec(ojr, new_lsn), new_lsn) == Self::i_opt(ojr, old_lsn).discard_old(new_lsn)
    decreases ojr
    {
        if ojr is Some {
            if ojr is Some && new_lsn < ojr.unwrap().message_seq.seq_start {
                Self::discard_old_defn_interprets(*ojr.unwrap().prior_rec, old_lsn, new_lsn);   // recursive call
                (*ojr.unwrap().prior_rec).unwrap().i_lemma(old_lsn);  // new invocation; i_lemma_forall wasn't triggery enough
            }
        }
        assert_maps_equal!(
            Self::i_opt(Self::discard_old_journal_rec(ojr, new_lsn), new_lsn).msgs,
            Self::i_opt(ojr, old_lsn).discard_old(new_lsn).msgs
        ); // new extensionality trigger
    }

    pub proof fn discard_valid(self, old_lsn: LSN, new_lsn: LSN)
    requires
        self.valid(old_lsn),
        old_lsn <= new_lsn < self.message_seq.seq_end,
    ensures
        self.valid(new_lsn),
    decreases self
    {
        if !self.message_seq.can_discard_to(new_lsn) {
            self.prior_rec.unwrap().discard_valid(old_lsn, new_lsn);
        }
    }
}

impl TruncatedJournal {
    pub open spec(checked) fn i(self) -> MsgHistory
    recommends
        self.wf(),
    {
        JournalRecord::i_opt(self.freshest_rec, self.boundary_lsn)
    }

    // YA ensures built into TruncatedJournal.CropHeadRecords
    // used to be free due to auto triggering of what now isopt_rec_crop_head_records_lemma
    pub proof fn crop_head_records_wf_lemma(self, depth: nat)
    requires
        JournalRecord::opt_rec_can_crop_head_records(self.freshest_rec, self.boundary_lsn, depth),
    ensures
        self.crop_head_records(depth).wf(),
    {
        JournalRecord::opt_rec_crop_head_records_lemma(self.freshest_rec, self.boundary_lsn, depth);
    }

    pub proof fn tj_freeze_for_commit(self, frozen: TruncatedJournal, depth: nat)
    requires
        self.wf(),
        self.freeze_for_commit(frozen, depth),
    ensures
        self.i().includes_subseq(frozen.i())
    {
        let ctj = self.crop_head_records(depth);
        if ctj.freshest_rec is Some && frozen.boundary_lsn < ctj.freshest_rec.unwrap().message_seq.seq_end {
            self.freshest_rec.unwrap().crop_head_records_lemma(self.boundary_lsn, depth);   // newly required
            JournalRecord::discard_old_maintains_subseq(ctj.freshest_rec, ctj.boundary_lsn, frozen.boundary_lsn);
        }
        JournalRecord::i_lemma_forall();    // newly required; ~40 lines to discover
        JournalRecord::crop_head_maintains_subseq(self.freshest_rec, self.boundary_lsn, depth);
    }

    // another lemma that was almost free (modulo OptionNewBoundaryValid call) with ensures
    // This might be an interesting example for dealing with "adding just a line of proof, guvna"
    pub proof fn discard_old_defn_wf(self, lsn: LSN)
    requires
        self.wf(),
        self.can_discard_to(lsn),
    ensures self.discard_old_defn(lsn).wf()
    {
        if lsn != self.seq_end() {
            if self.freshest_rec is Some {
                let rec = self.freshest_rec.unwrap();
                rec.discard_valid(self.boundary_lsn, lsn);  // translates OptionNewBoundaryValid
                JournalRecord::discard_old_journal_rec_ensures(self.freshest_rec, lsn);
            }
        }
    }
}

impl PagedJournal::Label {
    pub open spec(checked) fn wf(self) -> bool
    {
        match self {
            PagedJournal::Label::FreezeForCommit{frozen_journal} => frozen_journal.wf(),
            _ => true,
        }
    }

    pub open spec(checked) fn i(self) -> AbstractJournal::Label
    recommends
        self.wf(),
    {
        match self {
            PagedJournal::Label::ReadForRecovery{messages}
                => AbstractJournal::Label::ReadForRecoveryLabel{messages},
            PagedJournal::Label::FreezeForCommit{frozen_journal}
                => AbstractJournal::Label::FreezeForCommitLabel{frozen_journal: frozen_journal.i()},
            PagedJournal::Label::QueryEndLsn{end_lsn}
                => AbstractJournal::Label::QueryEndLsnLabel{end_lsn},
            PagedJournal::Label::Put{messages}
                => AbstractJournal::Label::PutLabel{messages},
            PagedJournal::Label::DiscardOld{start_lsn, require_end}
                => AbstractJournal::Label::DiscardOldLabel{start_lsn, require_end},
            PagedJournal::Label::Internal{}
                => AbstractJournal::Label::InternalLabel{},
        }
    }
}

impl PagedJournal::State {
    pub open spec(checked) fn i(self) -> AbstractJournal::State
    recommends
        self.wf(),
    {
        AbstractJournal::State{journal: self.truncated_journal.i().concat(self.unmarshalled_tail)}
    }

    pub proof fn read_for_recovery_refines(self, post: Self, lbl: PagedJournal::Label, depth: nat)
    requires 
        self.wf(),
        PagedJournal::State::read_for_recovery(self, post, lbl, depth),
    ensures
        post.wf(),
        AbstractJournal::State::next(self.i(), post.i(), lbl.i()),
    {
        // New calls
        JournalRecord::i_lemma_forall(); // superstition
        reveal(AbstractJournal::State::next_by);    // unfortunate defaults
        reveal(AbstractJournal::State::next);

        let ojr = self.truncated_journal.freshest_rec;
        let bdy = self.truncated_journal.boundary_lsn;
        let msgs = lbl.arrow_ReadForRecovery_messages();
        if ojr is Some {
            ojr.unwrap().can_crop_monotonic(bdy, depth, depth+1);
            ojr.unwrap().can_crop_more_yields_some(bdy, depth, depth+1);

            // New explicit call: Ten lines of debugging later, I needed this call:
            ojr.unwrap().crop_head_records_lemma(bdy, depth);

            ojr.unwrap().cropped_subseq_in_interpretation(bdy, depth, msgs);

            // New explicit call: was broadcast from concat
            ojr.unwrap().i(bdy).concat_lemma(self.unmarshalled_tail);
        }

        // New for step witness. Dafny AbstractJournal didn't have a Step.
        assert(AbstractJournal::State::next_by(self.i(), post.i(), lbl.i(), AbstractJournal::Step::read_for_recovery()));
    }

    pub proof fn freeze_for_commit_refines(self, post: Self, lbl: PagedJournal::Label, depth: nat)
    requires 
        self.wf(),  // move to an invariant?
        PagedJournal::State::freeze_for_commit(self, post, lbl, depth),
    ensures
        post.wf(),
        AbstractJournal::State::next(self.i(), post.i(), lbl.i()),
    {
        reveal(AbstractJournal::State::next_by);    // newly required; unfortunate macro defaults
        reveal(AbstractJournal::State::next);    // newly required; unfortunate macro defaults

        self.truncated_journal.tj_freeze_for_commit(lbl->frozen_journal, depth);

        JournalRecord::i_lemma_forall(); // newly required call
        self.truncated_journal.i().concat_lemma(self.unmarshalled_tail);    // newly required call

        assert(AbstractJournal::State::next_by(self.i(), post.i(), lbl.i(), AbstractJournal::Step::freeze_for_commit())); // new witness
    }

    // inv was 'true', so skipping the invariant proof. Would otherwise do it as a state_machine!
    // invariant!

    pub proof fn discard_old_refines(self, post: Self, lbl: PagedJournal::Label)
    requires 
        self.wf(),  // move to an invariant?
        PagedJournal::State::discard_old(self, post, lbl),
    ensures
        post.wf(),
        AbstractJournal::State::next(self.i(), post.i(), lbl.i()),
    {
        reveal(AbstractJournal::State::next_by);    // newly required; unfortunate macro defaults
        reveal(AbstractJournal::State::next);       // newly required; unfortunate macro defaults
        JournalRecord::i_lemma_forall();            // newly required

        let lsn = lbl->start_lsn;
        let tj = self.truncated_journal;
        if lsn < self.unmarshalled_tail.seq_start {
            if tj.freshest_rec is Some && lsn < tj.seq_end() {
                tj.freshest_rec.unwrap().discard_valid(tj.boundary_lsn, lsn);
                tj.discard_old_defn_wf(lsn);    // newly required
            }
            JournalRecord::discard_old_defn_interprets(tj.freshest_rec, tj.boundary_lsn, lsn);
        }

        assert_maps_equal!( post.i().journal.msgs, self.i().journal.discard_old(lbl.i()->start_lsn).msgs );    // newly required extensionality
        assert(AbstractJournal::State::next_by(self.i(), post.i(), lbl.i(), AbstractJournal::Step::discard_old())); // newly required witness
    }

    pub proof fn marshall_refines(self, post: Self, lbl: PagedJournal::Label, cut: LSN)
    requires 
        self.wf(),  // move to an invariant?
        PagedJournal::State::internal_journal_marshal(self, post, lbl, cut),
    ensures
        post.wf(),
        AbstractJournal::State::next(self.i(), post.i(), lbl.i()),
    {
        reveal(AbstractJournal::State::next_by);    // newly required; unfortunate macro defaults
        reveal(AbstractJournal::State::next);       // newly required; unfortunate macro defaults

        assert_maps_equal!( post.i().journal.msgs, self.i().journal.msgs ); // proof kinda got more direct, but ugly extensionality
        JournalRecord::i_lemma_forall();            // newly required
        assert(AbstractJournal::State::next_by(self.i(), post.i(), lbl.i(), AbstractJournal::Step::internal())); // newly required witness
    }

    pub proof fn next_refines(self, post: Self, lbl: PagedJournal::Label)
    requires
        self.wf(),  // move to an invariant?
        PagedJournal::State::next(self, post, lbl),
    ensures
        post.wf(),
        AbstractJournal::State::next(self.i(), post.i(), lbl.i()),
    {
        reveal(PagedJournal::State::next);    // newly required; unfortunate macro defaults
        reveal(PagedJournal::State::next_by);    // newly required; unfortunate macro defaults
        reveal(AbstractJournal::State::next);       // newly required; unfortunate macro defaults
        reveal(AbstractJournal::State::next_by);    // newly required; unfortunate macro defaults
        JournalRecord::i_lemma_forall();

        let step = choose |step| PagedJournal::State::next_by(self, post, lbl, step);
        match step {
            PagedJournal::Step::read_for_recovery(depth) => {
                self.read_for_recovery_refines(post, lbl, depth);
            }
            PagedJournal::Step::freeze_for_commit(depth) => {
                self.freeze_for_commit_refines(post, lbl, depth);
            }
            PagedJournal::Step::query_end_lsn() => {
                assert(AbstractJournal::State::next_by(self.i(), post.i(), lbl.i(), AbstractJournal::Step::observe_fresh_journal())); // new witness
            }
            PagedJournal::Step::put() => {
                assert_maps_equal!( post.i().journal.msgs, self.i().journal.concat(lbl.i().arrow_PutLabel_messages()).msgs );    // newly required extensionality; this branch used to be a freebie.
                assert(AbstractJournal::State::next_by(self.i(), post.i(), lbl.i(), AbstractJournal::Step::put())); // new witness
            }
            PagedJournal::Step::discard_old() => {
                self.discard_old_refines(post, lbl);
            }
            PagedJournal::Step::internal_journal_marshal(cut) => {
                self.marshall_refines(post, lbl, cut);
            }
            PagedJournal::Step::internal_no_op() => {
                //assert_maps_equal!( post.i().journal.msgs, self.i().journal.msgs );    // newly required extensionality; this branch used to be a freebie.
                assert(AbstractJournal::State::next_by(self.i(), post.i(), lbl.i(), AbstractJournal::Step::internal())); // new witness
            }
            _ => { assert(false); } // dummy_to_use_type_params boilerplate
        }
    }

    pub proof fn init_refines(self, truncated_journal: TruncatedJournal) 
    requires PagedJournal::State::initialize(self, truncated_journal)
    ensures AbstractJournal::State::initialize(self.i(), self.i().journal)
    {
        JournalRecord::i_lemma_forall();
    }
}

}//verus
