// Copyright 2018-2024 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, University of Washington
// SPDX-License-Identifier: BSD-2-Clause

#![allow(unused_imports)]
use builtin::*;

use builtin_macros::*;
use state_machines_macros::state_machine;
use vstd::prelude::*;
use vstd::{map::*, seq::*, bytes::*, set::*, multiset::*};

use crate::trusted::ProgramModelTrait_t::*;
use crate::spec::AsyncDisk_t::*;
use crate::spec::MapSpec_t::{ID, SyncReqId, Request, Reply};
use crate::spec::MapSpec_t::{AsyncMap, CrashTolerantAsyncMap};
// TODO: move this somewhere else? or we can use disk lbl instead
use crate::implementation::MultisetMapRelation_v::*; 

verus!{

// Crash Tolerant System Model defined by the auditor,
// consists of an auditor defined disk model and a implementer provided program model
state_machine!{ SystemModel<ProgramModel: ProgramModelTrait> {
    fields {
        // program is simply an application I/O and disk I/O driver wih proof obligations
        pub program: ProgramModel, 

        // trusted disk model
        pub disk: DiskModel,

        pub requests: Multiset<Request>,
        pub replies: Multiset<Reply>,
        pub sync_requests: Multiset<SyncReqId>,
    }

    // Crash Tolerance is driven by the program, system model merely serves to orchestrate
    // and restricts interactions between program, application clients, and the disk
    pub enum Label
    {
        AcceptRequest{ req: Request },
        DeliverReply{ reply: Reply },

        // AcceptRequest{ sync_rec_id: SyncReqId },
        // DeliverSyncReply{ sync_rec_id: SyncReqId },

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

    init!{ initialize(program: ProgramModel, disk: DiskModel) {
        require ProgramModel::is_mkfs(disk);
        require ProgramModel::init(program);

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
        &&& !self.sync_requests.contains(id)
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

    transition!{ program_execute(lbl: Label, new_program: ProgramModel) {
        require lbl is ProgramUIOp;
        require lbl->op is Execute;

        require pre.requests.contains(lbl->op->req);
        require ProgramModel::next(pre.program, new_program, ProgramLabel::UserIO{op: lbl->op});

        update program = new_program;
        update requests = pre.requests.remove(lbl->op->req);
        update replies = pre.replies.insert(lbl->op->reply);
    }}

    // NOTE: we don't need to model this in the system model
    // these auditor only steps are needed in KVStoreTokenized
    // to enable the token flows, but make no difference at the system model layer
    // as these are noops

    // implemented by auditor
    // transition!{ accept_sync_request(lbl: Label) {
    //     require lbl is AcceptSyncRequest;
    //     require pre.fresh_id(lbl->sync_req_id);
    //     update sync_requests = pre.sync_requests.insert(sync_req_id);
    // }}

    transition!{ program_accept_sync_request(lbl: Label, new_program: ProgramModel) {
        require lbl is ProgramUIOp;
        require let ProgramUserOp::AcceptSyncRequest{sync_req_id} = lbl->op;
        require pre.fresh_id(sync_req_id);
        require ProgramModel::next(pre.program, new_program, ProgramLabel::UserIO{op: lbl->op});
        update program = new_program;
        update sync_requests = pre.sync_requests.insert(sync_req_id);
    }}

    transition!{ program_deliver_sync_reply(lbl: Label, new_program: ProgramModel) {
        require lbl is ProgramUIOp;
        require let ProgramUserOp::DeliverSyncReply{sync_req_id} = lbl->op;
        require pre.sync_requests.contains(sync_req_id);
        require ProgramModel::next(pre.program, new_program, ProgramLabel::UserIO{op: lbl->op});
        update program = new_program;
        update sync_requests = pre.sync_requests.remove(sync_req_id);
        // update sync_replies = pre.sync_replies.insert(sync_req_id);
    }}

    // implemented by auditor
    // transition!{ deliver_sync_reply(lbl: Label) {
    //     require lbl is DeliverSyncReply;
    //     require pre.sync_replies.contains(sync_req_id);
    //     update sync_replies = pre.sync_replies.remove(sync_req_id);
    // }}

    transition!{ program_disk(lbl: Label, new_program: ProgramModel, new_disk: DiskModel) {
        require lbl is ProgramDiskOp;

        let disk_lbl = DiskLabel::DiskOps{
            requests: multiset_to_map(lbl->info.reqs),
            responses: multiset_to_map(lbl->info.resps),
        };

        require ProgramModel::next(pre.program, new_program, ProgramLabel::DiskIO{info: lbl->info});
        require DiskModel::next(pre.disk, new_disk, disk_lbl);

        update program = new_program;
        update disk = new_disk;
    }}

    transition!{ program_internal(lbl: Label, new_program: ProgramModel) {
        require lbl is ProgramInternal;
        require ProgramModel::next(pre.program, new_program, ProgramLabel::Internal{});        
        update program = new_program;
    }}

    transition!{ disk_internal(lbl: Label, new_disk: DiskModel) {
        require lbl is DiskInternal;
        require DiskModel::next(pre.disk, new_disk, DiskLabel::Internal{});
        update disk = new_disk;
    }}

    transition!{ crash(lbl: Label, new_program: ProgramModel, new_disk: DiskModel) {
        require lbl is Crash;
        require ProgramModel::init(new_program); 
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
}
