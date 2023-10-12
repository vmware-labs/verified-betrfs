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
use vstd::map_lib::*;
use crate::abstract_system::StampedMap_v::LSN;
use crate::abstract_system::MsgHistory_v::*;
use crate::disk::GenericDisk_v::*;
use crate::disk::GenericDisk_v::AU;
use crate::journal::LinkedJournal_v::*;
use crate::allocation_layer::AllocationJournal_v::*;
use crate::allocation_layer::MiniAllocator_v::*;

verus!{
pub struct StoreState {
    pub freshest_rec: Pointer,  // from LinkedJournal::TruncatedJournal
    pub first: AU,              // from AllocationJournal::State
    pub dom: Set<Address>       // domain of the store image
}

impl StoreState {
    pub open spec(checked) fn empty() -> Self {
        StoreState {
            freshest_rec: None,
            first: 0,
            dom: Set::empty(),
        }
    }
}

pub struct EphemeralState {
    pub image_state: StoreState,
    pub unmarshalled_tail: MsgHistory,  // from LinkedJournal::State
    pub lsn_au_index: Map<LSN, AU>,     // from AllocationJournal::State
    pub mini_allocator: MiniAllocator,  // from AllocationJournal::State
}

#[is_variant]
pub enum Ephemeral
{
    Unknown,
    Known{ v: EphemeralState }
}

state_machine!{AllocationCrashAwareJournal{
    fields {
        pub ephemeral: Ephemeral,
        pub persistent: StoreState,
        pub inflight: Option<StoreState>,
        pub diskview: Map<Address, JournalRecord>,
    }

    init!{
        initialize() {
            init persistent = StoreState::empty();
            init ephemeral = Ephemeral::Unknown;
            init inflight = Option::None;
            init diskview = Map::empty();
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

  }} // state_machine
} // verus