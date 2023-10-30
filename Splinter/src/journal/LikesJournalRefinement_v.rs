// Copyright 2018-2021 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, and University of Washington
// SPDX-License-Identifier: BSD-2-Clause
//
#![allow(unused_imports)]
use builtin::*;

use builtin_macros::*;
use state_machines_macros::state_machine;

use vstd::prelude::*;
use crate::abstract_system::StampedMap_v::LSN;
use crate::abstract_system::MsgHistory_v::*;
use crate::disk::GenericDisk_v::*;
use crate::journal::LinkedJournal_v;
use crate::journal::LinkedJournal_v::{LinkedJournal, DiskView, TruncatedJournal};
use crate::journal::LikesJournal_v;
use crate::journal::LikesJournal_v::*;

verus!{

impl LikesJournal::Step {
    // proof fn i(self) -> LinkedJournal::Step {
    //     match self {
    //         Self::read_for_recovery() =>
    //             LinkedJournal::Step::read_for_recovery(depth),
    //         Self::freeze_for_commit(depth) =>
    //             LinkedJournal::Step::freeze_for_commit(depth),
    //         Self::query_end_lsn() =>
    //             LinkedJournal::Step::query_end_lsn(),
    //         Self::put(_new_journal) =>
    //             LinkedJournal::Step::put(),
    //         Self::discard_old() =>
    //             LinkedJournal::Step::discard_old(),
    //         Self::internal_journal_marshal(cut, addr, _new_journal) =>
    //             LinkedJournal::Step::internal_journal_marshal(cut, addr),
    //         Self::internal_no_op() =>
    //             LinkedJournal::Step::internal_journal_no_op(),
    //         _ => arbitrary(),   // TODO(travis): wart on the state machine language
    //     }
    // }
}

impl DiskView {
}

// The thrilling climax, the actual proof goal we want to use in lower
// refinement layers.
impl LikesJournal::State {
}


} // verus!
