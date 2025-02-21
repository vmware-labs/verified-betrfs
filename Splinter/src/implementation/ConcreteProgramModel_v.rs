#[allow(unused_imports)]    // lost in erasure
use builtin::*;
use vstd::prelude::*;

// use crate::trusted::KVStoreTokenized_v::KVStoreTokenized;
use crate::spec::SystemModel_t::*;
use crate::implementation::DiskLayout_v::*;
use crate::implementation::AtomicState_v::*;

verus!{

pub struct ConcreteProgramModel {
    pub state: AtomicState,
    // pub state: KVStoreTokenized::State,
}

impl ConcreteProgramModel {
}

impl ProgramModel for ConcreteProgramModel {
    open spec fn is_mkfs(disk: DiskModel) -> bool
    {
        &&& mkfs(disk.content)
        &&& disk.requests.is_empty()
        &&& disk.responses.is_empty()
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
                        AtomicState::map_transition(pre.state, post.state, req, reply)
                    },
                    ProgramUserOp::AcceptSyncRequest{sync_req_id, version} => {
                        AtomicState::valid_sync_request(pre.state, post.state, version)
                    },
                    ProgramUserOp::DeliverSyncReply{sync_req_id, version} => {
                        AtomicState::valid_sync_reply(pre.state, post.state, version)
                    },
                }
            },
            ProgramLabel::DiskIO{info} => {
                exists |disk_event| AtomicState::disk_transition(
                    pre.state, post.state, disk_event, info.reqs, info.resps)
            },
            ProgramLabel::Internal{} => { 
                AtomicState::internal_transitions(pre.state, post.state)
            }, // no internal op on atomic state yet
        }
    }
}
}
