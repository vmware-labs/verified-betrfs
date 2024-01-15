// Copyright 2018-2023 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, University of Washington
// SPDX-License-Identifier: BSD-2-Clause
#[allow(unused_imports)]
use builtin::*;

use builtin_macros::*;
use state_machines_macros::state_machine;

use crate::abstract_system::StampedMap_v::*;
use crate::abstract_system::MsgHistory_v::*;

verus! {

// An AbstractJournal is an abstract view of a, well, journal. It logs
// a set of operations, which should eventually be compacted and applied
// to a map. (The state of an AbstractJournal is just a MsgHistory).
state_machine!{ AbstractJournal {
    fields {
        /// The log of messages this AbstractJournal contains.
        pub journal: MsgHistory
    }

    pub open spec(checked) fn wf(self) -> bool
    {
      self.journal.wf()
    }

    #[is_variant]  // TODO: verus! should always make enum variants
    pub enum Label{
        ReadForRecoveryLabel{ messages: MsgHistory },
        FreezeForCommitLabel{ frozen_journal: MsgHistory},
        QueryEndLsnLabel{ end_lsn: LSN },
        PutLabel{ messages: MsgHistory },
        DiscardOldLabel{ start_lsn: LSN, require_end: LSN},
        // TODO(jonh): see corresonding todo in dafny "datatype TransitionLabel"
        InternalLabel,
    }

    pub open spec(checked) fn can_end_at(self, lsn: LSN) -> bool {
        self.journal.seq_end == lsn
    }

    init!{ 
        initialize(persistent_journal: MsgHistory) {
            require persistent_journal.wf();
            init journal = persistent_journal;
        }
    }

    // Read a section of the journal. Transition asserts that the
    // MsgHistory in the label matches an slice of the journal
    // (i.e.: it corresponds to a valid read rather than making
    // stuff up)
    transition!{
        read_for_recovery(lbl: Label) {
            require pre.wf();
            require lbl.is_ReadForRecoveryLabel();
            // TODO(verus): it would be nice to have a get_messages() accessor
            require pre.journal.includes_subseq(lbl.get_ReadForRecoveryLabel_messages());
        }
    }

    transition!{
        freeze_for_commit(lbl: Label) {
            require pre.wf();
            require lbl.is_FreezeForCommitLabel();
            require lbl.get_FreezeForCommitLabel_frozen_journal().wf();
            require pre.journal.includes_subseq(lbl.get_FreezeForCommitLabel_frozen_journal());
        }
    }

    transition!{
        observe_fresh_journal(lbl: Label) {
            require pre.wf();
            require lbl.is_QueryEndLsnLabel();
            require pre.can_end_at(lbl.get_QueryEndLsnLabel_end_lsn());
        }
    }

    transition!{
        put(lbl: Label) {
            require pre.wf();
            require lbl.is_PutLabel();
            require pre.journal.seq_end == lbl.get_PutLabel_messages().seq_start;
            update journal = pre.journal.concat(lbl.get_PutLabel_messages());
        }
    }

    transition!{
        discard_old(lbl: Label) {
            require pre.wf();
            require lbl.is_DiscardOldLabel();
            require pre.journal.seq_end == lbl.get_DiscardOldLabel_require_end();
            require pre.journal.can_discard_to(lbl.get_DiscardOldLabel_start_lsn());
            update journal = pre.journal.discard_old(lbl.get_DiscardOldLabel_start_lsn());
        }
    }

    transition!{
        internal(lbl: Label) {
            require pre.wf();
            require lbl.is_InternalLabel();
        }
    }
}}

}
