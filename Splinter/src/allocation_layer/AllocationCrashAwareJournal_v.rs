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
        CommitComplete{ require_end: LSN },
        Crash,
    }

    transition!{
        load_ephemeral_from_persistent(lbl: Label, new_journal: AllocationJournal::State, journal_config: AllocationJournal::Config) {
            require lbl.is_LoadEphemeralFromPersistent();
            require pre.ephemeral.is_Unknown();
            // likes journal state?
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

  }} // state_machine
} // verus