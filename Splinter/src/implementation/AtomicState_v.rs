// Copyright 2018-2024 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, University of Washington
// SPDX-License-Identifier: BSD-2-Clause
use vstd::{prelude::*};
//use vstd::pervasive::print_u64;
use crate::spec::MapSpec_t::*;
use crate::spec::FloatingSeq_t::*;
use crate::spec::AsyncDisk_t::*;
use crate::implementation::DiskLayout_v::*;

verus! {

pub enum RecoveryState {
    // Haven't done anything; don't know anything. Better not handle user IO.
    Begin,
    // We've sent the superblock read request; better not send any more! Still can't do user IO.
    AwaitingSuperblock,
    // System can now operate
    RecoveryComplete,
}

#[verifier::ext_equal]
pub struct AtomicState {
    pub recovery_state: RecoveryState,

    pub history: FloatingSeq<PersistentState>,

    // tells us what syncs can be replied
    pub persistent_version: nat,

    // tells us what we can bump persistent_version when the disk response comes back.
    pub in_flight_version: Option<nat>,
}

pub enum DiskEventLabel{
    InitiateRecovery{},
    CompleteRecovery{rawPage: RawPage},
    ExecuteSyncBegin{},
    ExecuteSyncEnd{},
}

impl AtomicState {
    // this is process init, which should do filesystem recovery before operation
    pub open spec fn init() -> Self
    {
        AtomicState{
            recovery_state: RecoveryState::Begin,
            history: arbitrary(),
            persistent_version: arbitrary(),  // unknown
            in_flight_version: arbitrary(),
        }
    }

    pub open spec fn map_transition(pre: Self, post: Self, map_lbl: MapSpec::Label) -> bool
    {
        &&& pre.recovery_state is RecoveryComplete
        // new thing appends no more than one map
        &&& pre.history.len() <= post.history.len() <= pre.history.len() + 1
        // new thing appends to the history
        &&& post.history.get_prefix(pre.history.len()) == pre.history
        &&& MapSpec::State::next(pre.history.last().appv, post.history.last().appv, map_lbl)
    }

    pub open spec fn initiate_recovery(pre: Self, post: Self, disk_lbl: AsyncDisk::Label, disk_req_id: ID) -> bool
    {
        // Haven't started operating yet
        &&& pre.recovery_state is Begin
        &&& disk_lbl == AsyncDisk::Label::DiskOps{
            requests: Map::empty().insert(disk_req_id, DiskRequest::ReadReq{from: superblock_addr() }),
            responses: Map::empty()
            }
        &&& post == Self{ recovery_state: RecoveryState::AwaitingSuperblock, ..pre }
    }

    pub open spec fn complete_recovery(pre: Self, post: Self, disk_lbl: AsyncDisk::Label, disk_req_id: ID, rawPage: RawPage) -> bool
    {
        // &&& pre.recovery_state is AwaitingSuperblock // can prove this by invariant
        &&& disk_lbl == AsyncDisk::Label::DiskOps{
            requests: Map::empty(),
            responses: Map::empty().insert(disk_req_id, DiskResponse::ReadResp{from: superblock_addr(), data: rawPage }),
            }
        &&& {
            let superblock = spec_unmarshall(rawPage);
            post == Self{
                recovery_state: RecoveryState::RecoveryComplete,
                history: FloatingSeq::new(superblock.version_index, superblock.version_index+1, |i| superblock.state),
                in_flight_version: None,
                persistent_version: superblock.version_index,
            }
        }
    }

    pub open spec fn execute_sync_begin(pre: Self, post: Self, disk_lbl: AsyncDisk::Label, disk_req_id: ID) -> bool
    {
        let version_index = (pre.history.len() - 1) as nat;
        let rawPage = spec_marshall(Superblock{version_index, state: pre.history.last()});
        &&& pre.recovery_state is RecoveryComplete
        &&& pre.in_flight_version is None
        &&& disk_lbl == AsyncDisk::Label::DiskOps{
            requests: Map::empty().insert(disk_req_id, DiskRequest::WriteReq{to: superblock_addr(), data: rawPage }),
            responses: Map::empty()
            }
        &&& post == Self{ in_flight_version: Some(version_index), .. pre }
    }

    pub open spec fn execute_sync_end(pre: Self, post: Self, disk_lbl: AsyncDisk::Label, disk_req_id: ID) -> bool
    {
        &&& pre.recovery_state is RecoveryComplete
        // &&& pre.in_flight_version is Some // provable
        &&& disk_lbl == AsyncDisk::Label::DiskOps{
            requests: Map::empty(),
            responses: Map::empty().insert(disk_req_id, DiskResponse::WriteResp{to: superblock_addr()}),
        }
        &&& {
            let new_persistent_version = pre.in_flight_version->0;
            &&& post == Self{
                recovery_state: RecoveryState::RecoveryComplete,
                history: pre.history.get_suffix(new_persistent_version as int),
                in_flight_version: None,
                persistent_version: new_persistent_version,
            }
        }
    }

    pub open spec fn disk_transition(pre: Self, post: Self, disk_event_lbl: DiskEventLabel, disk_lbl: AsyncDisk::Label, disk_req_id: ID) -> bool
    {
        match disk_event_lbl {
            DiskEventLabel::InitiateRecovery{} => Self::initiate_recovery(pre, post, disk_lbl, disk_req_id),
            DiskEventLabel::CompleteRecovery{rawPage} => Self::complete_recovery(pre, post, disk_lbl, disk_req_id, rawPage),
            DiskEventLabel::ExecuteSyncBegin{} => Self::execute_sync_begin(pre, post, disk_lbl, disk_req_id),
            DiskEventLabel::ExecuteSyncEnd{} => Self::execute_sync_end(pre, post, disk_lbl, disk_req_id),
        }
    }

    pub open spec fn wf(self) -> bool {
        self.recovery_state is RecoveryComplete ==> {
            &&& self.history.is_active(self.history.len()-1)
            &&& forall |i| #[trigger] self.history.is_active(i) ==> self.history[i].appv.invariant()
        }
    }

    pub open spec fn mapspec(self) -> MapSpec::State {
        self.history.last().appv
    }
}

}//verus!
