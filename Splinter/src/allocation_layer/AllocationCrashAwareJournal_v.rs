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
use crate::allocation_layer::AllocationJournal_v::*;

verus!{
  pub type StoreImage = JournalImage;

  #[is_variant]
  pub enum Ephemeral
  {
    Unknown,
    Known{v: AllocationJournal::State}
  }

  impl Ephemeral {
    pub open spec(checked) fn wf(self) -> bool
    {
      self is Known ==> self.get_Known_v().wf()
    }
  }

  state_machine!{AllocationCrashAwareJournal{
    fields {
      pub persistent: StoreImage,
      pub ephemeral: Ephemeral,
      pub inflight: Option<StoreImage>
    }

    init!{
      initialize() {
          init persistent = JournalImage::empty();
          init ephemeral = Ephemeral::Unknown;
          init inflight = Option::None;
      }
    }

    #[is_variant]
    pub enum Label
    {
        LoadEphemeralFromPersistent,
        ReadForRecovery{ records: MsgHistory },
        QueryEndLsn{ end_lsn: LSN },
        Put{ records: MsgHistory },
        Internal{allocs: Set<AU>, deallocs: Set<AU>},
        QueryLsnPersistence{ sync_lsn: LSN },
        CommitStart{ new_boundary_lsn: LSN, max_lsn: LSN },
        CommitComplete{ require_end: LSN, discarded: Set<AU> },
        Crash,
    }

    transition!{
        load_ephemeral_from_persistent(lbl: Label, new_journal: AllocationJournal::State, journal_config: AllocationJournal::Config) {
            require lbl.is_LoadEphemeralFromPersistent();
            require pre.ephemeral.is_Unknown();
            require journal_config === AllocationJournal::Config::initialize(new_journal.journal, pre.persistent);
            require AllocationJournal::State::init_by(new_journal, journal_config);
            update ephemeral = Ephemeral::Known{ v: new_journal };
        }
    }

    transition!{
        read_for_recovery(lbl: Label) {
            require lbl.is_ReadForRecovery();
            require pre.ephemeral.is_Known();
            require AllocationJournal::State::next(
                pre.ephemeral.get_Known_v(), 
                pre.ephemeral.get_Known_v(), 
                AllocationJournal::Label::ReadForRecovery{ messages: lbl.get_ReadForRecovery_records() }
            );
        }
    }

    transition!{
        query_end_lsn(lbl: Label) {
            require lbl.is_QueryEndLsn();
            require pre.ephemeral.is_Known();
            require AllocationJournal::State::next(
                pre.ephemeral.get_Known_v(), 
                pre.ephemeral.get_Known_v(), 
                AllocationJournal::Label::QueryEndLsn{ end_lsn: lbl.get_QueryEndLsn_end_lsn() },
            );
        }
    }

    transition!{
        put(lbl: Label, new_journal: AllocationJournal::State) {
            require lbl.is_Put();
            require pre.ephemeral.is_Known();
            require AllocationJournal::State::next(
                pre.ephemeral.get_Known_v(), 
                new_journal, 
                AllocationJournal::Label::Put{ messages: lbl.get_Put_records() },
            );
            update ephemeral = Ephemeral::Known{ v: new_journal };
        }
    }

    transition!{
        internal(lbl: Label, new_journal: AllocationJournal::State) {
            require lbl.is_Internal();
            require pre.ephemeral.is_Known();
            require AllocationJournal::State::next(
                pre.ephemeral.get_Known_v(), 
                new_journal, 
                AllocationJournal::Label::InternalAllocations{allocs: lbl.get_Internal_allocs(), deallocs: lbl.get_Internal_deallocs() }
            );
            update ephemeral = Ephemeral::Known{ v: new_journal };
        }
    }

    transition!{
        query_lsn_persistence(lbl: Label) {
            require lbl.is_QueryLsnPersistence();
            require lbl.get_QueryLsnPersistence_sync_lsn() <= pre.persistent.tj.seq_end();
        }
    }

    transition!{
        commit_start(lbl: Label, frozen_journal: StoreImage, new_journal: AllocationJournal::State) {
            require lbl.is_CommitStart();
            require pre.ephemeral.is_Known();
            // Can't start a commit if one is in-flight, or we'd forget to maintain the
            // invariants for the in-flight one.
            require pre.inflight.is_None();
            // Frozen journal stitches to frozen map
            require frozen_journal.tj.seq_start() == lbl.get_CommitStart_new_boundary_lsn();
            // Journal doesn't go backwards
            require pre.persistent.tj.seq_end() <= frozen_journal.tj.seq_end();
            // There should be no way for the frozen journal to have passed the ephemeral map!
            require frozen_journal.tj.seq_start() <= lbl.get_CommitStart_max_lsn();
            require AllocationJournal::State::next(
                pre.ephemeral.get_Known_v(), 
                new_journal, 
                AllocationJournal::Label::FreezeForCommit{ frozen_journal: frozen_journal},
            );
            update ephemeral = Ephemeral::Known{ v: new_journal };
            update inflight = Option::Some(frozen_journal);
        }
    }

    transition!{
        commit_complete(lbl: Label, new_journal: AllocationJournal::State) {
            require lbl.is_CommitComplete();
            require pre.ephemeral.is_Known();
            require pre.inflight.is_Some();

            require AllocationJournal::State::next(
                pre.ephemeral.get_Known_v(), 
                new_journal, 
                AllocationJournal::Label::DiscardOld{ 
                    start_lsn: pre.inflight.get_Some_0().tj.seq_start(), 
                    require_end: lbl.get_CommitComplete_require_end(),
                    deallocs: lbl.get_CommitComplete_discarded(),
                },
            );
            
            // Watch the `update` keyword!
            update persistent = pre.inflight.get_Some_0();
            update ephemeral = Ephemeral::Known{ v: new_journal };
            update inflight = Option::None;
        }
    }

    transition!{
        crash(lbl: Label) {
            require lbl.is_Crash();
            update ephemeral = Ephemeral::Unknown;
            update in_flight = Option::None;
        }
    }

  }} // state_machine
} // verus