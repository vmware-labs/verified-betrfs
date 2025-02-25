#[allow(unused_imports)]    // lost in erasure
use builtin::*;
use vstd::prelude::*;

use crate::spec::AsyncDisk_t::*;
use crate::spec::MapSpec_t::*;
use crate::trusted::ProgramModelTrait_t::*;
use crate::implementation::DiskLayout_v::*;
use crate::implementation::AtomicState_v::*;

verus!{

pub struct ConcreteProgramModel {
    pub state: AtomicState,
}

impl ConcreteProgramModel {
    // TODO: this is stupid, AtomicState::disk_transition by itself does not trigger
    pub open spec fn valid_disk_transition(pre: Self, post: Self, info: ProgramDiskInfo) -> bool
    {
        exists |disk_event| AtomicState::disk_transition(
            pre.state, post.state, disk_event, info.reqs, info.resps)
    }
}

impl ProgramModelTrait for ConcreteProgramModel {
    open spec fn is_mkfs(disk: DiskModel) -> bool
    {
        &&& mkfs(disk.content)
        &&& disk.requests == Map::<ID, DiskRequest>::empty()
        &&& disk.responses == Map::<ID, DiskResponse>::empty()
    }

    open spec fn init(pre: Self) -> bool
    {
        &&& pre.state == AtomicState::init()
    }

    open spec fn next(pre: Self, post: Self, lbl: ProgramLabel) -> bool
    {
        match lbl {
            ProgramLabel::UserIO{op} => {
                match op {
                    ProgramUserOp::Execute{req, reply} => {
                        // translate it into the other request and reply
                        AtomicState::map_transition(pre.state, post.state, req, reply)
                    },
                    ProgramUserOp::AcceptSyncRequest{sync_req_id} => {
                        AtomicState::accept_sync_request(pre.state, post.state, sync_req_id)
                    },
                    ProgramUserOp::DeliverSyncReply{sync_req_id} => {
                        AtomicState::deliver_sync_reply(pre.state, post.state, sync_req_id)
                    },
                }
            },
            ProgramLabel::DiskIO{info} => {
                ConcreteProgramModel::valid_disk_transition(pre, post, info)
                // NOTE: I think we want this but this is causing flaky proofs
                // where we can't show next event though there is a witness for disk_event
                // exists |disk_event| #[trigger] AtomicState::disk_transition(
                //     pre.state, post.state, disk_event, info.reqs, info.resps)
            },
            ProgramLabel::Internal{} => { 
                AtomicState::internal_transitions(pre.state, post.state)
            }, // no internal op on atomic state yet
        }
    }
}
}
