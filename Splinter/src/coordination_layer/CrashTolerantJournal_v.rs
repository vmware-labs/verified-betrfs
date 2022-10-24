#[allow(unused_imports)]
use builtin::*;

use builtin_macros::*;
use state_machines_macros::state_machine;
#[allow(unused_imports)]
use crate::pervasive::{map::*};

use crate::spec::Option_t::*;
use crate::coordination_layer::StampedMap_v::*;
use crate::coordination_layer::MessageHistory_v::*;
use crate::coordination_layer::AbstractJournal_v::*;

verus! {

pub type StoreImage = MsgHistory;

// TODO: Could use option types? But they are not supported in verus
#[is_variant]
pub enum Ephemeral {
    Unknown,
    Known{ v: AbstractJournal::State },
}

state_machine!{ CrashTolerantJournal {
    fields { 
        pub persistent: StoreImage,
        pub ephemeral: Ephemeral,
        pub in_flight: Option<StoreImage>
    }

    init!{
        Init() {
            init persistent = MsgHistory{ msgs: Map::empty(), seq_start: 0, seq_end: 0};
            init ephemeral = Ephemeral::Unknown;
            init in_flight = Option::None;
        }
    }

    #[is_variant]  // TODO: verus! should always make enum variants
    pub enum Label{
        LoadEphemeralFromPersistentLabel,
        ReadForRecoveryLabel{ records: MsgHistory },
        QueryEndLsnLabel{ end_lsn: LSN },
        PutLabel{ records: MsgHistory },
        InternalLabel,
        QueryLsnPersistenceLabel{ sync_lsn: LSN },
        CommitStartLabel{ new_boundary_lsn: LSN, max_lsn: LSN },
        CommitCompleteLabel{ require_end: LSN },
        CrashLabel,
    }

    transition!{
        load_ephemeral_from_persistent(lbl: Label, new_journal: AbstractJournal::State, journal_config: AbstractJournal::Config) {
            require lbl.is_LoadEphemeralFromPersistentLabel();
            require pre.ephemeral.is_Unknown();
            require journal_config === AbstractJournal::Config::Init(pre.persistent);
            require AbstractJournal::State::init_by(new_journal, journal_config);
            update ephemeral = Ephemeral::Known{ v: new_journal };
        }
    }

    transition!{
        read_for_recovery(lbl: Label, new_journal: AbstractJournal::State, journal_step: AbstractJournal::Step) {
            require lbl.is_ReadForRecoveryLabel();
            require pre.ephemeral.is_Known();
            // TODO(verus): This seems very redundant with transition labels?
            require journal_step === AbstractJournal::Step::read_for_recovery();
            require AbstractJournal::State::next_by(
                pre.ephemeral.get_Known_v(), 
                new_journal, 
                AbstractJournal::Label::ReadForRecoveryLabel{ messages: lbl.get_ReadForRecoveryLabel_records() },
                journal_step
            );
            update ephemeral = Ephemeral::Known{ v: new_journal };
        }
    }

    transition!{
        query_end_lsn(lbl: Label, new_journal: AbstractJournal::State, journal_step: AbstractJournal::Step) {
            require lbl.is_QueryEndLsnLabel();
            require pre.ephemeral.is_Known();
            require journal_step === AbstractJournal::Step::observe_fresh_journal();
            require AbstractJournal::State::next_by(
                pre.ephemeral.get_Known_v(), 
                new_journal, 
                AbstractJournal::Label::QueryEndLsnLabel{ end_lsn: lbl.get_QueryEndLsnLabel_end_lsn() },
                journal_step
            );
            update ephemeral = Ephemeral::Known{ v: new_journal };
        }
    }

    transition!{
        put(lbl: Label, new_journal: AbstractJournal::State, journal_step: AbstractJournal::Step) {
            require lbl.is_PutLabel();
            require pre.ephemeral.is_Known();
            require journal_step === AbstractJournal::Step::put();
            require AbstractJournal::State::next_by(
                pre.ephemeral.get_Known_v(), 
                new_journal, 
                AbstractJournal::Label::PutLabel{ messages: lbl.get_PutLabel_records() },
                journal_step
            );
            update ephemeral = Ephemeral::Known{ v: new_journal };
        }
    }

    transition!{
        internal(lbl: Label, new_journal: AbstractJournal::State, journal_step: AbstractJournal::Step) {
            require lbl.is_InternalLabel();
            require pre.ephemeral.is_Known();
            require journal_step === AbstractJournal::Step::internal();
            require AbstractJournal::State::next_by(
                pre.ephemeral.get_Known_v(), 
                new_journal, 
                AbstractJournal::Label::InternalLabel,
                journal_step
            );
            update ephemeral = Ephemeral::Known{ v: new_journal };
        }
    }

    transition!{
        query_lsn_persistence(lbl: Label) {
            require lbl.is_QueryLsnPersistenceLabel();
            require lbl.get_QueryLsnPersistenceLabel_sync_lsn() <= pre.persistent.seq_end;
        }
    }

    transition!{
        commit_start(lbl: Label, frozen_journal: StoreImage, new_journal: AbstractJournal::State, journal_step: AbstractJournal::Step) {
            require lbl.is_CommitStartLabel();
            require pre.ephemeral.is_Known();
            // Can't start a commit if one is in-flight, or we'd forget to maintain the
            // invariants for the in-flight one.
            require pre.in_flight.is_None();

            // Frozen journal stitches to frozen map
            require frozen_journal.seq_start == lbl.get_CommitStartLabel_new_boundary_lsn();

            // Journal doesn't go backwards
            require pre.persistent.seq_end <= frozen_journal.seq_end;

            // There should be no way for the frozen journal to have passed the ephemeral map!
            require frozen_journal.seq_start <= lbl.get_CommitStartLabel_max_lsn();
            require journal_step === AbstractJournal::Step::freeze_for_commit();
            require AbstractJournal::State::next_by(
                pre.ephemeral.get_Known_v(), 
                new_journal, 
                AbstractJournal::Label::FreezeForCommitLabel{ frozen_journal: frozen_journal},
                journal_step
            );
            update ephemeral = Ephemeral::Known{ v: new_journal };
            update in_flight = Option::Some(frozen_journal);
        }
    }

    transition!{
        commit_complete(lbl: Label, new_journal: AbstractJournal::State, journal_step: AbstractJournal::Step) {
            require lbl.is_CommitCompleteLabel();
            require pre.ephemeral.is_Known();
            require pre.in_flight.is_Some();
            require journal_step === AbstractJournal::Step::discard_old();
            require AbstractJournal::State::next_by(
                pre.ephemeral.get_Known_v(), 
                new_journal, 
                AbstractJournal::Label::DiscardOldLabel{ 
                    start_lsn: pre.in_flight.get_Some_0().seq_start, 
                    require_end: lbl.get_CommitCompleteLabel_require_end()
                },
                journal_step
            );
            update persistent = pre.in_flight.get_Some_0();
            update ephemeral = Ephemeral::Known{ v: new_journal };
            update in_flight = Option::None;
        }
    }

    transition!{
        crash(lbl: Label) {
            require lbl.is_CrashLabel();
            update ephemeral = Ephemeral::Unknown;
            update in_flight = Option::None;
        }
    }
}}
}