// Copyright 2018-2024 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, University of Washington
// SPDX-License-Identifier: BSD-2-Clause

#[allow(unused_imports)]
use builtin::*;

use builtin_macros::*;
use state_machines_macros::state_machine;

use vstd::prelude::*;
use crate::abstract_system::StampedMap_v::LSN;
use crate::abstract_system::MsgHistory_v::*;

verus! {

pub struct JournalRecord {
    pub message_seq: MsgHistory,
    pub prior_rec: Box<Option<JournalRecord>>,
}

impl JournalRecord {
    pub open spec(checked) fn wf(self) -> bool
    decreases self
    {
        &&& self.message_seq.wf()
        &&& (*self.prior_rec) is Some ==> {
            &&& self.prior_rec.unwrap().wf()
            &&& self.prior_rec.unwrap().message_seq.can_concat(self.message_seq)
            }
    }

    pub open spec(checked) fn valid(self, boundary_lsn: LSN) -> bool
    decreases self
    {
        &&& self.wf()
        &&& boundary_lsn < self.message_seq.seq_end
        &&& {
            ||| self.message_seq.can_discard_to(boundary_lsn)
            ||| ((*self.prior_rec) is Some && self.prior_rec.unwrap().valid(boundary_lsn))
            }
    }

    pub proof fn new_boundary_valid(self, old_lsn: LSN, new_lsn: LSN)
    requires
        self.valid(old_lsn),
        old_lsn <= new_lsn,
        new_lsn < self.message_seq.seq_end,
    ensures
        self.valid(new_lsn),
    decreases self
    {
        if new_lsn < self.message_seq.seq_start {
            self.prior_rec.get_Some_0().new_boundary_valid(old_lsn, new_lsn);
        }
    }

    pub open spec(checked) fn cropped_prior(self, boundary_lsn: LSN) -> Option<JournalRecord>
    {
        if self.message_seq.seq_start <= boundary_lsn { None } else { *self.prior_rec }
    }

    pub open spec(checked) fn can_crop_head_records(self, boundary_lsn: LSN, depth: nat) -> bool
    decreases depth, 0nat
    {
        &&& self.valid(boundary_lsn)
        &&& if depth == 0 { true }
            else {
                Self::opt_rec_can_crop_head_records(
                    self.cropped_prior(boundary_lsn), boundary_lsn, (depth-1) as nat)
            }
    }

    pub open spec(checked) fn opt_rec_can_crop_head_records(ojr: Option<JournalRecord>, boundary_lsn: LSN, depth: nat) -> bool
        decreases depth, 1nat
    {
        match ojr {
            None => depth==0,
            Some(rec) => rec.can_crop_head_records(boundary_lsn, depth),
        }
    }

    pub open spec(checked) fn crop_head_records(self, boundary_lsn: LSN, depth: nat) -> Option<JournalRecord>
    recommends
        self.can_crop_head_records(boundary_lsn, depth)
    decreases depth, 0nat
    {
        // < case can't happen, but need to mention it to get termination.
        if depth == 0 { Some(self) }
        else {
            Self::opt_rec_crop_head_records(self.cropped_prior(boundary_lsn), boundary_lsn, (depth-1) as nat)
        }
    }

    pub open spec(checked) fn opt_rec_crop_head_records(ojr: Option<JournalRecord>, boundary_lsn: LSN, depth: nat) -> (out: Option<JournalRecord>)
    recommends
        Self::opt_rec_can_crop_head_records(ojr, boundary_lsn, depth),
    // ensures no longer available; becomes lemma
//    ensures
//        out is Some ==> out.unwrap().valid(boundary_lsn),
    decreases depth, 1nat
    {
        match ojr {
            None => None,
            Some(rec) => rec.crop_head_records(boundary_lsn, depth)
        }
    }

    // NB this entire 50-line monstrosity was a single 'ensures' line in Dafny.
    pub proof fn crop_head_records_lemma(self, boundary_lsn: LSN, depth: nat)
    requires
        self.can_crop_head_records(boundary_lsn, depth),
    ensures ({
        let out = self.crop_head_records(boundary_lsn, depth);
        out is Some ==> out.unwrap().valid(boundary_lsn)
    })
    decreases depth, 0nat
    {
        if depth!=0 {
            Self::opt_rec_crop_head_records_lemma(self.cropped_prior(boundary_lsn), boundary_lsn, (depth-1) as nat);
        }
    }

    pub proof fn opt_rec_crop_head_records_lemma(ojr: Option<JournalRecord>, boundary_lsn: LSN, depth: nat)
    requires
        Self::opt_rec_can_crop_head_records(ojr, boundary_lsn, depth),
    ensures ({
        let out = Self::opt_rec_crop_head_records(ojr, boundary_lsn, depth);
        out is Some ==> out.unwrap().valid(boundary_lsn)
    })
    decreases depth, 1nat
    {
        match ojr {
            None => {}
            Some(rec) => {
                if ojr is Some {
                    rec.crop_head_records_lemma(boundary_lsn, depth);
                }
            }
        }
    }

    // TODO(jonh): when broadcast_forall is available, use it above.
    // TODO(jonh): and this trigger isn't triggery enough for my taste; see Refinement file
    // explicit invocations of the non-forall version of this lemma.
    pub proof fn opt_rec_crop_head_records_lemma_forall()
    ensures
        forall|ojr: Option<JournalRecord>, boundary_lsn: LSN, depth: nat|
            Self::opt_rec_can_crop_head_records(ojr, boundary_lsn, depth)
            ==>
            (#[trigger] Self::opt_rec_crop_head_records(ojr, boundary_lsn, depth)) is Some ==> Self::opt_rec_crop_head_records(ojr, boundary_lsn, depth).unwrap().valid(boundary_lsn),
    {
        assert forall |ojr: Option<JournalRecord>, boundary_lsn: LSN, depth: nat|
            Self::opt_rec_can_crop_head_records(ojr, boundary_lsn, depth)
            implies
            (#[trigger] Self::opt_rec_crop_head_records(ojr, boundary_lsn, depth)) is Some ==> Self::opt_rec_crop_head_records(ojr, boundary_lsn, depth).unwrap().valid(boundary_lsn) by {
            Self::opt_rec_crop_head_records_lemma(ojr, boundary_lsn, depth);
        }
    }

    pub proof fn can_crop_monotonic(self, boundary_lsn: LSN, depth: nat, more: nat)
    requires
        depth < more,
        self.can_crop_head_records(boundary_lsn, more)
    ensures
        self.can_crop_head_records(boundary_lsn, depth)
    decreases depth
    {
        if 0<depth {
            self.cropped_prior(boundary_lsn).get_Some_0().can_crop_monotonic(boundary_lsn, (depth-1) as nat, (more-1) as nat);
        }
    }

    pub proof fn can_crop_more_yields_some(self, boundary_lsn: LSN, depth: nat, more: nat)
    requires
        0 <= depth < more,
        self.can_crop_head_records(boundary_lsn, more)
    ensures
        //self.can_crop_head_records(boundary_lsn, depth) // 
        self.crop_head_records(boundary_lsn, depth) is Some,
    decreases depth
    {
        self.can_crop_monotonic(boundary_lsn, depth, more);
        if 0<depth {
//          // TODO(chris): not enough fuel for mutual recursion? This is painful wrt dafny
//          // TODO(jonh): expain this to andrea
//            assert(Self::opt_rec_can_crop_head_records(self.cropped_prior(boundary_lsn), boundary_lsn, (more-1) as nat));
            self.cropped_prior(boundary_lsn).get_Some_0().can_crop_more_yields_some(boundary_lsn, (depth-1) as nat, (more-1) as nat);
//          // TODO(chris): not enough fuel for mutual recursion? This is painful wrt dafny
//            assert(Self::opt_rec_crop_head_records(self.cropped_prior(boundary_lsn), boundary_lsn, (depth-1) as nat) is Some);
        }
    }
        
    pub open spec /*XXX (checked)*/ fn message_seq_after_crop(self, boundary_lsn: LSN, depth: nat) -> MsgHistory
    recommends
        self.valid(boundary_lsn),
        self.can_crop_head_records(boundary_lsn, depth+1)
    {
        //XXX self.can_crop_more_yields_some(boundary_lsn, depth, depth+1);
        let chrms = self.crop_head_records(boundary_lsn, depth).get_Some_0().message_seq;
        let _ = spec_affirm(chrms.wf());
        chrms.maybe_discard_old(boundary_lsn)
    }

    pub proof fn option_new_boundary_valid(ojr: Option<JournalRecord>, old_lsn: LSN, new_lsn: LSN)
    requires
    // jonh has decided that the match form is harder to read than the dafny
    // test-and-dereference style. In dafny form, ==> vs && is sitting right in
    // front of you. In match form, they're encoded in the 'default' arm of the
    // match. Misreading that has caused me some headaches already.
//        match ojr { Some(rec) => rec.valid(old_lsn), _ => true }
        ojr is Some ==> ojr.unwrap().valid(old_lsn),
        ojr is Some ==> new_lsn < ojr.unwrap().message_seq.seq_end,
        old_lsn <= new_lsn,
    ensures
        ojr is Some ==> ojr.unwrap().valid(new_lsn)
    {
        if ojr is Some {
            ojr.unwrap().new_boundary_valid(old_lsn, new_lsn);
        }
    }

    pub open spec(checked) fn discard_old_journal_rec(ojr: Option<JournalRecord>, lsn: LSN) -> (out: Option<JournalRecord>)
    recommends
        ojr is Some ==> ojr.unwrap().valid(lsn),
    // ensures
    //     out is Some ==> out.unwrap().valid(lsn),
    decreases ojr
    {
        match ojr {
            None => None,
            Some(rec) => {
                let prior_rec =
                    if rec.message_seq.seq_start <= lsn { None }
                    else { Self::discard_old_journal_rec(*rec.prior_rec, lsn) };
                Some(JournalRecord{message_seq: rec.message_seq, prior_rec: Box::new(prior_rec)})
            }
        }
    }

    pub proof fn discard_old_journal_rec_ensures(ojr: Option<JournalRecord>, lsn: LSN)
    requires
        ojr is Some ==> ojr.unwrap().valid(lsn),
    ensures ({
        let out = Self::discard_old_journal_rec(ojr, lsn);
        out is Some ==> out.unwrap().valid(lsn)
        })
    decreases ojr
    {
        match ojr {
            None => { }
            Some(rec) => {
                if lsn < rec.message_seq.seq_start {
                    Self::discard_old_journal_rec_ensures(*rec.prior_rec, lsn);
                }
            }
        }
    }
}

// A TruncatedJournal is some long chain but which we ignore beyond the boundaryLSN
// (because we have a map telling us that part of the history).
// In the refinement layer below, we'll have some situations where the disk has extra
// journal records, but we'll ignore them in the refinement (since we never read them)
// and instead supply a None? for the interpretation at this layer.
// That's what keeps us out of trouble when those un-read pages get reclaimed -- we don't
// want to have to say we can interpret them.
pub struct TruncatedJournal {
    pub boundary_lsn: LSN,  // exclusive: lsns <= boundaryLSN are discarded
    pub freshest_rec: Option<JournalRecord>,
}

impl TruncatedJournal {
    pub open spec(checked) fn prior(self) -> TruncatedJournal
    recommends
        self.freshest_rec is Some,
    {
        TruncatedJournal{
            boundary_lsn: self.boundary_lsn,
            freshest_rec: *self.freshest_rec.unwrap().prior_rec }
    }

    pub open spec(checked) fn wf(self) -> bool {
        &&& self.freshest_rec is Some ==> self.freshest_rec.unwrap().valid(self.boundary_lsn)
    }

    pub open spec(checked) fn is_empty(self) -> bool
    recommends
        self.wf(),
    {
        self.freshest_rec is None
    }

    pub open spec(checked) fn seq_end(self) -> LSN
    recommends
        self.wf(),
    {
        if self.freshest_rec is Some { self.freshest_rec.unwrap().message_seq.seq_end }
        else { self.boundary_lsn }
    }

    pub open spec(checked) fn seq_start(self) -> LSN
    recommends
        self.wf(),
    {
        self.boundary_lsn
    }

    pub open spec(checked) fn can_discard_to(self, lsn: LSN) -> bool
    recommends
        self.wf(),
    {
        self.seq_start() <= lsn <= self.seq_end()
    }

    pub open spec /*XXX(checked)*/ fn discard_old_defn(self, lsn: LSN) -> (out: TruncatedJournal)
    recommends
        self.wf(),
        self.can_discard_to(lsn),
    //ensures out.wf()
    {
        TruncatedJournal{
            boundary_lsn: lsn,
            freshest_rec:
                if self.seq_end() == lsn { None }
                else {
                    // XXX option_new_boundary_valid(self.freshest_rec, lsn);
                    JournalRecord::discard_old_journal_rec(self.freshest_rec, lsn)
                }
        }
    }

    // msgs appears as the (boundary-truncated) contents of the i'th entry in the
    // chain of JournalRecords
    pub open spec(checked) fn has_messages_at_depth(self, msgs: MsgHistory, depth: nat) -> bool
    recommends
        self.wf(),
        msgs.wf(),
    {
        &&& self.freshest_rec is Some
        &&& self.freshest_rec.unwrap().can_crop_head_records(self.boundary_lsn, depth+1)
        &&& self.freshest_rec.unwrap().message_seq_after_crop(self.boundary_lsn, depth) == msgs
    }

    pub open spec(checked) fn append_record(self, msgs: MsgHistory) -> (out: TruncatedJournal)
    recommends
        self.wf(),
        msgs.wf(),
    {
        TruncatedJournal{
            freshest_rec: Some(JournalRecord{message_seq: msgs, prior_rec: Box::new(self.freshest_rec)}),
            ..self}
    }

    pub open spec(checked) fn can_crop(self, depth: nat) -> bool {
        JournalRecord::opt_rec_can_crop_head_records(self.freshest_rec, self.boundary_lsn, depth)
    }

    pub open spec(checked) fn crop_head_records(self, depth: nat) -> (out: TruncatedJournal)
    recommends
        self.can_crop(depth),
    // ensures out.wf()
    {
        TruncatedJournal{
            freshest_rec: JournalRecord::opt_rec_crop_head_records(self.freshest_rec, self.boundary_lsn, depth),
            ..self}
    }

    // replaces missing spec(checked) ensures
    pub proof fn crop_head_records_ensures(self, depth: nat)
    requires
        self.wf(),
        self.can_crop(depth),
    ensures
        self.crop_head_records(depth).wf(),
    {
        if 0 < depth {
            self.freshest_rec.unwrap().crop_head_records_lemma(self.boundary_lsn, depth);   // typcial infuriating missing spec(checked) ensures
        }
    }

    pub open spec /*XXX(checked)*/ fn freeze_for_commit(self, frozen_journal: TruncatedJournal, depth: nat) -> bool
    recommends
        self.wf(),
    {
        &&& frozen_journal.wf()
        &&& JournalRecord::opt_rec_can_crop_head_records(self.freshest_rec, self.boundary_lsn, depth)
        // XXX self.crop_head_records_ensures(depth)
        &&& self.crop_head_records(depth).can_discard_to(frozen_journal.boundary_lsn)
        &&& frozen_journal == self.crop_head_records(depth).discard_old_defn(frozen_journal.boundary_lsn)
    }

}

pub open spec(checked) fn mkfs() -> (out: TruncatedJournal)
// ensures out.wf()
{
    TruncatedJournal{boundary_lsn: 0, freshest_rec: None}
}

/////////////////////////////////////////////////////////////////////////////
// EphemeralJournal is an TruncatedJournal with an extra unmarshalledTail
// field to represent entries we have collected in memory but not marhsalled
// into a JournalRecord yet.


state_machine!{ PagedJournal {
    fields {
        pub truncated_journal: TruncatedJournal,
        pub unmarshalled_tail: MsgHistory,
    }

    pub open spec(checked) fn wf(self) -> bool {
        &&& self.truncated_journal.wf()
        &&& self.unmarshalled_tail.wf()
        &&& self.truncated_journal.seq_end() == self.unmarshalled_tail.seq_start
    }

    pub open spec(checked) fn seq_start(self) -> LSN
    recommends
        self.wf(),
    {
        self.truncated_journal.boundary_lsn
    }

    pub open spec(checked) fn seq_end(self) -> LSN
    recommends
        self.wf(),
    {
        self.unmarshalled_tail.seq_end
    }

    pub enum Label
    {
        ReadForRecovery{messages: MsgHistory},
        FreezeForCommit{frozen_journal: TruncatedJournal},
        QueryEndLsn{end_lsn: LSN},
        Put{messages: MsgHistory},
        DiscardOld{start_lsn: LSN, require_end: LSN},
        Internal{},   // Local No-op label
    }

    transition!{ read_for_recovery(lbl: Label, depth: nat) {
        require pre.wf();
        require lbl is ReadForRecovery;
        require lbl.arrow_ReadForRecovery_messages().wf();
        require pre.truncated_journal.has_messages_at_depth(lbl.arrow_ReadForRecovery_messages(), depth);  // label subseq appears in committed pages

        // We don't bother allowing you to "find" the msgs in unmarshalledTail,
        // since the includes operation is only relevant during recovery time,
        // during which the unmarshalledTail is kept empty.
        // (I mean, we COULD allow Puts during that time, but why bother?)
    }}

    transition!{ freeze_for_commit(lbl: Label, depth: nat) {
        require lbl is FreezeForCommit;
        require pre.truncated_journal.freeze_for_commit(lbl->frozen_journal, depth);
    }}

    transition!{ query_end_lsn(lbl: Label) {
        require lbl is QueryEndLsn;
        require lbl->end_lsn == pre.seq_end();
    }}

    /////////////////////////////////////////////////////////////////////////////
    // implementation of JournalIfc obligations

    transition!{ put(lbl: Label) {
        require lbl is Put;
        let msgs = lbl.arrow_Put_messages();
        require msgs.wf();
        require msgs.seq_start == pre.seq_end();
        update unmarshalled_tail = pre.unmarshalled_tail.concat(msgs);
    }}
    
    transition!{ discard_old(lbl: Label) {
        require lbl is DiscardOld;
        let lsn = lbl->start_lsn;
        require pre.seq_start() <= lsn <= pre.seq_end();
        require pre.seq_end() == lbl->require_end;
        // in the Dafny version, we had an outer if around the updates. Here we have to duplicate
        // the if condition.
        update unmarshalled_tail =
            if pre.unmarshalled_tail.seq_start <= lsn
            { pre.unmarshalled_tail.discard_old(lsn) }
            else { pre.unmarshalled_tail };
        update truncated_journal =
            if pre.unmarshalled_tail.seq_start <= lsn
            { TruncatedJournal{boundary_lsn: lsn, freshest_rec: None} }
            else { pre.truncated_journal.discard_old_defn(lsn) };

      // NB the then-branches above are goofy -- the policy we've expressed in
      // CoordinationSystem only ever calls this function from
      // CommitComplete, when we've learned that some part of the journal
      // is persistent. No way that could gobble up any of the unmarshalled
      // tail! But we write it out for completeness. (But could have simply
      // excluded this case via an enabling condition, and the lower
      // refinement layers wouldn't have objected.)
    }}

    transition!{ internal_journal_marshal(lbl: Label, cut: LSN) {
        require lbl is Internal;
        require pre.unmarshalled_tail.seq_start < cut;  // Can't marshall nothing.
        require pre.unmarshalled_tail.can_discard_to(cut);
        let marshalled_msgs = pre.unmarshalled_tail.discard_recent(cut);
        update truncated_journal = pre.truncated_journal.append_record(marshalled_msgs);
        update unmarshalled_tail = pre.unmarshalled_tail.discard_old(cut);
    }}

    transition!{ internal_no_op(lbl: Label) {
        require lbl is Internal;
    }}

    init!{ initialize(truncated_journal: TruncatedJournal) {
        require truncated_journal.wf();
        init truncated_journal = truncated_journal;
        init unmarshalled_tail = MsgHistory::empty_history_at(truncated_journal.seq_end());
    }}

}}   // state_machine

}   // verus