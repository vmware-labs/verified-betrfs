// Copyright 2018-2024 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, University of Washington
// SPDX-License-Identifier: BSD-2-Clause

#![allow(unused_imports)]
use builtin::*;

use builtin_macros::*;
use state_machines_macros::state_machine;
use vstd::prelude::*;
use vstd::{map::*, seq::*, bytes::*, set::*, multiset::*};

use crate::spec::AsyncDisk_t::*;
use crate::spec::MapSpec_t::{ID, SyncReqId, Request, Reply};
use crate::spec::MapSpec_t::{AsyncMap, CrashTolerantAsyncMap};
// TODO: move this somewhere else? or we can use disk lbl instead
use crate::implementation::MultisetMapRelation_v::*; 

verus!{

pub type DiskModel = AsyncDisk::State;
pub type DiskLabel = AsyncDisk::Label;

pub enum ProgramUserOp{
    // add sync to request 
    // async operations with application clients
    // AcceptRequest{req: Request},
    // DeliverReply{reply: Reply},

    // declares the linearization point of each operation
    Execute{req: Request, reply: Reply},

    // to know what sync means we need to give sync a version
    // program handling application client requested sync request
    AcceptSyncRequest{ sync_req_id: SyncReqId, version: nat },
    DeliverSyncReply{ sync_req_id: SyncReqId, version: nat },
}

pub struct ProgramDiskInfo{
    // pub disk_event: DiskEvent, 
    pub reqs: Multiset<(ID, DiskRequest)>, 
    pub resps: Multiset<(ID, DiskResponse)>,
}

// Auditor defines externally visible actions that can be taken by a program model
// TODO: should we rename UserIO?
pub enum ProgramLabel{
    UserIO{op: ProgramUserOp},

    // captures program's interaction with the disk model,
    // e.g. loading/flushing/evicting cache pages
    DiskIO{info: ProgramDiskInfo},

    // program internal operation, no externally visible actions
    Internal{},
}

pub trait ProgramModel : Sized {
    spec fn is_mkfs(disk: DiskModel) -> bool;
    spec fn init(pre: Self) -> bool;
    spec fn next(pre: Self, post: Self, lbl: ProgramLabel) -> bool;
}

// Crash Tolerant System Model defined by the auditor,
// consists of an auditor defined disk model and a implementer provided program model
state_machine!{ SystemModel<T: ProgramModel> {
    fields {
        // program is simply an application I/O and disk I/O driver wih proof obligations
        pub program: T,
        // trusted disk model
        pub disk: DiskModel,

        // TODO: keeping these queues as multiset bc it aligns closer to the actual tokenized impl,
        // is that a sensible decision?
        pub requests: Multiset<Request>,
        pub replies: Multiset<Reply>,
        // TODO: nat driven by program
        pub sync_requests: Multiset<(SyncReqId, nat)>,
    }

    // Crash Tolerance is driven by the program, system model merely serves to orchestrate
    // and restricts interactions between program, application clients, and the disk
    pub enum Label
    {
        AcceptRequest{ req: Request },
        DeliverReply{ reply: Reply },

        // program model for enabling replies to user request
        // expose this to enforce correspondance 
        ProgramUIOp{ op: ProgramUserOp },
        // program driven disk ops
        ProgramDiskOp{ info: ProgramDiskInfo },
        // program internal op
        ProgramInternal,
        // disk internal op
        DiskInternal,
        // full system crashes
        Crash,
        Noop,

        // NOTE: 
        // Sync isn't included as a system model label because 
        // the actual sync point is driven by the program model
    }

    init!{ initialize(program: T, disk: DiskModel) {
        require T::is_mkfs(disk);
        require T::init(program);

        init program = program;
        init disk = disk;
        init requests = Multiset::empty();
        init replies = Multiset::empty();
        init sync_requests = Multiset::empty();
    }}

    pub open spec fn fresh_id(self, id: ID) -> bool
    {
        &&& forall |req| #[trigger] self.requests.contains(req) ==> req.id != id
        &&& forall |resp| #[trigger] self.replies.contains(resp) ==> resp.id != id
        &&& forall |sync_req| #[trigger] self.sync_requests.contains(sync_req) ==> sync_req.0 != id
    }

    // implemented by auditor's clientapi_t::accept_request
    transition!{ accept_request(lbl: Label) {
        require lbl is AcceptRequest;
        require pre.fresh_id(lbl->req.id); 
        update requests = pre.requests.insert(lbl->req);
    }}

    // implemented by auditor's clientapi_t::send_reply
    transition!{ deliver_reply(lbl: Label) {
        require lbl is DeliverReply;
        require pre.replies.contains(lbl->reply);
        update replies = pre.replies.remove(lbl->reply);
    }}

    transition!{ program_execute(lbl: Label, new_program: T) {
        require lbl is ProgramUIOp;
        require lbl->op is Execute;

        // new program must be a valid step
        require pre.requests.contains(lbl->op->req);
        require T::next(pre.program, new_program, ProgramLabel::UserIO{op: lbl->op});

        update program = new_program;
        update replies = pre.replies.insert(lbl->op->reply);
    }}

    // TODO: the timing of accept_sync req affect the response 
    // the auditor half promises the sync_req_id but version is restricted by the program
    transition!{ program_accept_sync(lbl: Label, new_program: T) {
        require lbl is ProgramUIOp;
        require let ProgramUserOp::AcceptSyncRequest{sync_req_id, version} = lbl->op;
        require pre.fresh_id(sync_req_id); // promised by accept_request

        require T::next(pre.program, new_program, ProgramLabel::UserIO{op: lbl->op});

        update program = new_program;
        update sync_requests = pre.sync_requests.insert((sync_req_id, version));
    }}

    transition!{ program_reply_sync(lbl: Label) {
        require lbl is ProgramUIOp;
        require let ProgramUserOp::DeliverSyncReply{sync_req_id, version} = lbl->op;
        require pre.sync_requests.contains((sync_req_id, version));

        // since there is explicit program step that enables a reply generation
        // we couple the delivery of sync reply with a program step that checks for 
        // whether a reply can be delivered
        require T::next(pre.program, pre.program, ProgramLabel::UserIO{op: lbl->op});
        update sync_requests = pre.sync_requests.remove((sync_req_id, version));
    }}

    // generating the label is equivalent to actually sending the disk ops
    // it doesn't matter if the requests have been submitted to the disk driver yet
    transition!{ program_disk(lbl: Label, new_program: T, new_disk: DiskModel) {
        require lbl is ProgramDiskOp;

        let disk_lbl = DiskLabel::DiskOps{
            requests: multiset_to_map(lbl->info.reqs),
            responses: multiset_to_map(lbl->info.resps),
        };

        require T::next(pre.program, new_program, ProgramLabel::DiskIO{info: lbl->info});
        require DiskModel::next(pre.disk, new_disk, disk_lbl);

        update program = new_program;
        update disk = new_disk;
    }}

    transition!{ program_internal(lbl: Label, new_program: T) {
        require lbl is ProgramInternal;
        require T::next(pre.program, new_program, ProgramLabel::Internal{});        
        update program = new_program;
    }}

    transition!{ disk_internal(lbl: Label, new_disk: DiskModel) {
        require lbl is DiskInternal;
        require DiskModel::next(pre.disk, new_disk, DiskLabel::Internal{});
        update disk = new_disk;
    }}

    transition!{ crash(lbl: Label, new_program: T, new_disk: DiskModel) {
        require lbl is Crash;
        require T::init(new_program); 
        require DiskModel::next(pre.disk, new_disk, DiskLabel::Crash{});

        update program = new_program;
        update disk = new_disk;
        update requests = Multiset::empty();
        update replies = Multiset::empty();
        update sync_requests = Multiset::empty();
    }}

    transition!{ noop(lbl: Label) {
        require lbl is Noop;
    }}
}}

pub open spec fn externally_visible(ctam_lbl: CrashTolerantAsyncMap::Label) -> bool
{
    ||| ctam_lbl is OperateOp && (ctam_lbl->base_op is RequestOp || ctam_lbl->base_op is ReplyOp)
    ||| ctam_lbl is ReqSyncOp
    ||| ctam_lbl is ReplySyncOp
}
// visible ctam op

impl SystemModel::Label {
    pub open spec fn label_correspondence(self, ctam_lbl: CrashTolerantAsyncMap::Label) -> bool
    {
        // TODO: correspondance only with external communication or 
        // also on execute, crash? if we hide a crash state refinement to 
        // something else, are we allowing a system that crashes to somehow
        // remember its state as non crash?
        match self {
            Self::AcceptRequest{req} => {
                ctam_lbl == CrashTolerantAsyncMap::Label::OperateOp{
                    base_op: AsyncMap::Label::RequestOp{req} }
            },
            Self::DeliverReply{reply} => {
                ctam_lbl == CrashTolerantAsyncMap::Label::OperateOp{
                    base_op: AsyncMap::Label::ReplyOp{reply} }
            },
            Self::ProgramUIOp{op} => {
                match op {
                    ProgramUserOp::AcceptSyncRequest{sync_req_id, version} => {
                        ctam_lbl == CrashTolerantAsyncMap::Label::ReqSyncOp{sync_req_id}
                    },
                    ProgramUserOp::DeliverSyncReply{sync_req_id, version} => {
                        ctam_lbl == CrashTolerantAsyncMap::Label::ReplySyncOp{sync_req_id}
                    },
                    _ => { !externally_visible(ctam_lbl) }
                }
            },
            // Self::Crash => {
            //     ctam_lbl == CrashTolerantAsyncMap::Label::CrashOp{}
            // },
            _ => { !externally_visible(ctam_lbl) },
        }
    }
}

pub trait RefinementObligation {
    type Model: ProgramModel;

    spec fn inv(model: SystemModel::State<Self::Model>) -> bool;
    
    spec fn i(model: SystemModel::State<Self::Model>) -> (ctam: CrashTolerantAsyncMap::State);

    spec fn i_lbl(pre: SystemModel::State<Self::Model>, post: SystemModel::State<Self::Model>, lbl: SystemModel::Label) -> (ctam_lbl: CrashTolerantAsyncMap::Label);

    // restrict i_lbl result to ensure app label correspondence 
    proof fn i_lbl_valid(pre: SystemModel::State<Self::Model>, post: SystemModel::State<Self::Model>, lbl: SystemModel::Label, ctam_lbl: CrashTolerantAsyncMap::Label)
        requires
            ctam_lbl == Self::i_lbl(pre, post, lbl)
        ensures
            lbl.label_correspondence(ctam_lbl)
    ;

    proof fn init_refines(pre: SystemModel::State<Self::Model>)
    requires
        SystemModel::State::initialize(pre, pre.program, pre.disk)
    ensures
        CrashTolerantAsyncMap::State::initialize(Self::i(pre)),
        Self::inv(pre)
    ;
        
    proof fn next_refines(pre: SystemModel::State<Self::Model>, post: SystemModel::State<Self::Model>, lbl: SystemModel::Label)
    requires
        SystemModel::State::next(pre, post, lbl), Self::inv(pre),
    ensures
        CrashTolerantAsyncMap::State::next(Self::i(pre), Self::i(post), Self::i_lbl(pre, post, lbl)),
        Self::inv(post)
    ;
}
}
