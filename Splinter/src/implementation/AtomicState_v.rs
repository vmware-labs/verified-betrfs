// Copyright 2018-2024 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, University of Washington
// SPDX-License-Identifier: BSD-2-Clause
use vstd::{prelude::*};
use vstd::{multiset::*};

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

pub struct InflightInfo {
    pub version: nat,
    pub req_id: ID,
}

#[verifier::ext_equal]
pub struct AtomicState {
    pub recovery_state: RecoveryState,

    pub history: FloatingSeq<PersistentState>,

    // tells us what syncs can be replied
    pub persistent_version: nat,

    // tells us what we can bump persistent_version when the disk response comes back.
    pub in_flight: Option<InflightInfo>,

    // maps each syncreq id with a version
    pub sync_req_map: Map<SyncReqId, nat>, 
}

pub enum DiskEvent{
    InitiateRecovery{req_id: ID},
    CompleteRecovery{req_id: ID, raw_page: RawPage},
    ExecuteSyncBegin{req_id: ID},
    ExecuteSyncEnd{},
}

pub open spec fn valid_request_reply_pair(req: Request, reply: Reply) -> bool 
{
    &&& req.id == reply.id
    &&& req.input is QueryInput <==> reply.output is QueryOutput
    &&& req.input is PutInput <==> reply.output is PutOutput
    &&& req.input is NoopInput <==> reply.output is NoopOutput
}

pub open spec(checked) fn to_map_label(req: Request, reply: Reply) -> MapSpec::Label 
    recommends valid_request_reply_pair(req, reply)
{
    let input = req.input;
    let output = reply.output;
    match req.input {
        Input::QueryInput{..} => { MapSpec::Label::Query {input, output} },
        Input::PutInput{..} => { MapSpec::Label::Put {input, output} },
        Input::NoopInput{} => { MapSpec::Label::Noop {input, output} },
    }
}

impl AtomicState {
    pub open spec fn wf(self) -> bool {
        self.recovery_state is RecoveryComplete ==> {
            &&& self.history.is_active(self.history.len()-1)
            &&& forall |i| #[trigger] self.history.is_active(i) ==> self.history[i].appv.invariant()
            &&& self.in_flight is Some ==> {
                self.history.is_active(self.in_flight.unwrap().version as int)
            }
            // &&& self.history.is_active(self.persistent_version as int)
            &&& self.history.first_active_index() == self.persistent_version
        }
    }

    // this is process init, which should do filesystem recovery before operation
    pub open spec fn init() -> Self
    {
        AtomicState{
            recovery_state: RecoveryState::Begin,
            history: arbitrary(),
            persistent_version: arbitrary(),  // unknown
            in_flight: arbitrary(),
            sync_req_map: arbitrary(),
        }
    }

    pub open spec fn map_transition(pre: Self, post: Self, req: Request, reply: Reply) -> bool
    {
        &&& pre.client_ready()
        // new thing appends no more than one map
        &&& pre.history.len() <= post.history.len() <= pre.history.len() + 1
        // new thing appends to the history
        &&& post.history.get_prefix(pre.history.len()) == pre.history

        &&& valid_request_reply_pair(req, reply)
        &&& MapSpec::State::next(pre.mapspec(), post.mapspec(), to_map_label(req, reply))
        &&& post == Self{ history: post.history, ..pre }
    }

    pub open spec fn accept_sync_request(pre: Self, post: Self, sync_req_id: SyncReqId) -> bool
    {
        &&& pre.client_ready()
        // &&& !pre.sync_req_map.contains_key(sync_req_id) // true by system invariant
        &&& post == Self{
            sync_req_map: pre.sync_req_map.insert(sync_req_id, (pre.history.len() - 1) as nat),
            ..pre
        }
    }

    pub open spec fn deliver_sync_reply(pre: Self, post: Self, sync_req_id: SyncReqId) -> bool
    {
        &&& pre.client_ready()
        &&& pre.sync_req_map.contains_key(sync_req_id)
            ==> pre.sync_req_map[sync_req_id] <=  pre.history.first_active_index()
        &&& post == Self{
            sync_req_map: pre.sync_req_map.remove(sync_req_id),
            ..pre
        }
    }

    pub open spec fn initiate_recovery(pre: Self, post: Self, reqs: Multiset<(ID, DiskRequest)>, resps: Multiset<(ID, DiskResponse)>, req_id: ID) -> bool
    {
        // Haven't started operating yet
        &&& pre.recovery_state is Begin
        // NOTE: ignores id for now cause we don't use it yet
        &&& reqs == Multiset::empty().insert((req_id, DiskRequest::ReadReq{from: spec_superblock_addr()}))
        &&& resps.is_empty()
        &&& post == Self{ recovery_state: RecoveryState::AwaitingSuperblock, ..pre }
    }

    pub open spec fn complete_recovery(pre: Self, post: Self, reqs: Multiset<(ID, DiskRequest)>, resps: Multiset<(ID, DiskResponse)>, req_id: ID, raw_page: RawPage) -> bool
    {
        &&& pre.recovery_state is AwaitingSuperblock // can prove this by invariant
        &&& reqs.is_empty()
        &&& resps == Multiset::empty().insert((req_id, DiskResponse::ReadResp{data: raw_page}))
        // &&& valid_checksum(raw_page)
        &&& {
            let superblock = spec_unmarshall(raw_page);
            post == Self{
                recovery_state: RecoveryState::RecoveryComplete,
                history: singleton_floating_seq(superblock.version_index, superblock.store.appv.kmmap),
                in_flight: None,
                persistent_version: superblock.version_index,
                sync_req_map: Map::empty(),
            }
        }
    }

    pub open spec fn execute_sync_begin(pre: Self, post: Self, reqs: Multiset<(ID, DiskRequest)>, resps: Multiset<(ID, DiskResponse)>, req_id: ID) -> bool
    {
        let sb = pre.ephemeral_sb();
        let inflight_info = InflightInfo{version: sb.version_index, req_id: req_id};

        &&& pre.client_ready()
        &&& pre.in_flight is None

        &&& reqs == Multiset::singleton((
            req_id, DiskRequest::WriteReq{to: spec_superblock_addr(), data: spec_marshall(sb)}
        ))
        &&& resps.is_empty()

        &&& post == Self{ in_flight: Some(inflight_info), .. pre }
    }

    pub open spec fn execute_sync_end(pre: Self, post: Self, reqs: Multiset<(ID, DiskRequest)>, resps: Multiset<(ID, DiskResponse)>) -> bool
    {
        &&& pre.client_ready()
        &&& pre.in_flight is Some 
        &&& reqs.is_empty()
        &&& resps == Multiset::singleton((pre.in_flight.unwrap().req_id, DiskResponse::WriteResp{}))

        &&& {
            let new_persistent_version = pre.in_flight.unwrap().version;
            &&& post == Self{
                recovery_state: RecoveryState::RecoveryComplete,
                history: pre.history.get_suffix(new_persistent_version as int),
                in_flight: None,
                persistent_version: new_persistent_version,
                ..pre
            }
        }
    }

    pub open spec fn disk_transition(pre: Self, post: Self, disk_event: DiskEvent, reqs: Multiset<(ID, DiskRequest)>, resps: Multiset<(ID, DiskResponse)>) -> bool
    {
        match disk_event {
            DiskEvent::InitiateRecovery{req_id} => Self::initiate_recovery(pre, post, reqs, resps, req_id),
            DiskEvent::CompleteRecovery{req_id, raw_page} => Self::complete_recovery(pre, post, reqs, resps, req_id, raw_page),
            DiskEvent::ExecuteSyncBegin{req_id} => Self::execute_sync_begin(pre, post, reqs, resps, req_id),
            DiskEvent::ExecuteSyncEnd{} => Self::execute_sync_end(pre, post, reqs, resps),
        }
    }

    pub closed spec fn disk_transition_system_assumptions(disk_event: DiskEvent) -> bool
    {
        match disk_event {
            DiskEvent::CompleteRecovery{req_id, raw_page} => {
                // remember that superblock invariant survives disk
                let superblock = spec_unmarshall(raw_page);
                superblock.store.appv.invariant()
            },
            _ => { true },
        }
    }

    // NOTE: silly internal op for now
    pub open spec fn internal_transitions(pre: Self, post: Self) -> bool
    {
        &&& pre == post 
        &&& pre.client_ready()
    }

    pub open spec fn mapspec(self) -> MapSpec::State {
        self.history.last().appv
    }

    pub open spec fn client_ready(self) -> bool
    {
        self.recovery_state is RecoveryComplete
    }

    pub open spec(checked) fn sb_at(self, v: int) -> Superblock
    recommends
        self.client_ready(),
        self.history.is_active(v),
    {
        Superblock{version_index: v as nat, store: self.history.get(v)}
    }

    pub open spec(checked) fn ephemeral_sb(self) -> Superblock
    recommends
        self.client_ready(),
        0 < self.history.len(),
        self.history.is_active(self.history.len()-1),
    {
        self.sb_at(self.history.len()-1)
    }

    pub open spec(checked) fn in_flight_sb(self) -> Superblock
    recommends
        self.wf(),
        self.client_ready(),
        self.in_flight is Some,
    {
        self.sb_at(self.in_flight.unwrap().version as int)
    }

    pub open spec(checked) fn persistent_sb(self) -> Superblock
    recommends
        self.wf(),
        self.client_ready(),
    {
        self.sb_at(self.persistent_version as int)
    }
}

}//verus!
