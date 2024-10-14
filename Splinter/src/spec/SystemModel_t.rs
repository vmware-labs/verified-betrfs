// Copyright 2018-2023 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, University of Washington
// SPDX-License-Identifier: BSD-2-Clause

#![allow(unused_imports)]
use builtin::*;

use builtin_macros::*;
use state_machines_macros::state_machine;
use vstd::prelude::*;
use vstd::{map::*, seq::*, bytes::*, set::*};

use crate::spec::AsyncDisk_t::*;
use crate::spec::MapSpec_t::{ID, SyncReqId, Request, Reply};
use crate::spec::MapSpec_t::{AsyncMap, CrashTolerantAsyncMap};

verus!{

type DiskModel = AsyncDisk::State;
type DiskLabel = AsyncDisk::Label;

// Auditor defines externally visible actions that can be taken by a program model
pub enum ProgramLabel{
    // async operations with application clients
    AcceptRequest{req: Request},
    DeliverReply{reply: Reply},

    // declares the linearization point of each operation
    Execute{req: Request, reply: Reply}, 

    // captures program's interaction with the disk model,
    // e.g. loading/flushing/evicting cache pages
    // DiskIO{disk_reqs: Set<DiskRequest>, disk_resps: Set<DiskResponse>},
    DiskIO{disk_lbl: DiskLabel},

    // program internal operation, no externally visible actions
    Internal{},

    // program handling application client requested sync request
    ReqSync{ sync_req_id: SyncReqId },
    ReplySync{ sync_req_id: SyncReqId },

    // models system crashes
    Crash,
}

impl ProgramLabel {
    pub open spec fn is_app_label(self) -> bool {
        self is AcceptRequest || self is DeliverReply || self is Execute
    }

    pub open spec fn to_async_map_label(self) -> AsyncMap::Label 
        recommends self.is_app_label()
    {
        if let Self::AcceptRequest{req} = self {
            AsyncMap::Label::RequestOp{req}
        } else if let Self::DeliverReply{reply} = self {
            AsyncMap::Label::ReplyOp{reply}
        } else if let Self::Execute{req, reply} = self {
            AsyncMap::Label::ExecuteOp{req, reply}
        } else {
            arbitrary()
        }
    }
}

pub trait ProgramModel {

    spec fn init(&self, disk: DiskModel) -> bool;

    spec fn next(&self, post: &Self, lbl: ProgramLabel) -> bool;
}

// Crash Tolerant System Model defined by the auditor,
// consists of an auditor defined disk model and a implementer provided program model
state_machine!{ SystemModel<T: ProgramModel> {
    fields {
        // program is simply an application I/O and disk I/O driver wih proof obligations
        pub program: T,
        // trusted disk model
        pub disk: DiskModel,
        // history of application requests that have been accepted,
        // auditor uses this to promise that every request has a unique ID 
        pub id_history: Set<ID>, 
    }

    // Crash Tolerance is driven by the program, system model merely serves to orchestrate
    // and restricts interactions between program, application clients, and the disk
    pub enum Label
    {
        // program model async operate op
        ProgramAsyncOp{ program_lbl: ProgramLabel },
        // program driven disk ops
        ProgramDiskOp{ disk_lbl: DiskLabel },
        // program internal op
        ProgramInternal,
        // disk internal op
        DiskInternal,
        // models moment of persistence on disk, physical disk refines to it, no corresponding transition
        SyncOp,
        // // application requesting a sync
        // ReqSyncOp{ sync_req_id: SyncReqId },
        // // application receiving sync done
        // ReplySyncOp{ sync_req_id: SyncReqId },
        // full system crashes
        Crash,
        Noop,
    }

    transition!{ program_async(lbl: Label, new_program: T) {
        require lbl is ProgramAsyncOp;
        require lbl->program_lbl.is_app_label();

        let new_id = if lbl->program_lbl is AcceptRequest {
            Set::empty().insert(lbl->program_lbl.arrow_AcceptRequest_req().id)
        } else { Set::empty() };

        // auditor's promise: new request contains unique ID
        require pre.id_history.disjoint(new_id);
        // new program must be a valid step
        require pre.program.next(&new_program, lbl->program_lbl);

        update program = new_program;
        update id_history = pre.id_history.union(new_id);
    }}

    transition!{ program_disk(lbl: Label, new_program: T, new_disk: DiskModel) {
        require lbl is ProgramDiskOp;
        require lbl->disk_lbl is DiskOps;

        require pre.program.next(
            &new_program,
            ProgramLabel::DiskIO{disk_lbl: lbl->disk_lbl},
        );

        require DiskModel::next(pre.disk, new_disk, lbl->disk_lbl);
        
        update program = new_program;
        update disk = new_disk;
    }}

    transition!{ program_internal(lbl: Label, new_program: T) {
        require lbl is ProgramInternal;
        require pre.program.next(&new_program, ProgramLabel::Internal{});        
        update program = new_program;
    }}

    transition!{ disk_internal(lbl: Label, new_disk: DiskModel) {
        require lbl is DiskInternal;
        require DiskModel::next(pre.disk, new_disk, DiskLabel::Internal{});
        update disk = new_disk;
    }}

    transition!{ req_sync(lbl: Label, new_program: T) {
        require let Label::ProgramAsyncOp{
            program_lbl: ProgramLabel::ReqSync{sync_req_id} } = lbl;

        // promise unique sync id from all previous ids
        require !pre.id_history.contains(sync_req_id as u64);

        require pre.program.next(&new_program, lbl->program_lbl);

        update program = new_program;
        update id_history = pre.id_history.insert(sync_req_id as u64);
    }}

    transition!{ reply_sync(lbl: Label, new_program: T) {
        require lbl is ProgramAsyncOp;
        require lbl->program_lbl is ReplySync;
        // TODO: do we want the equivalent reply id constraint?
        require pre.program.next(&new_program, lbl->program_lbl);
        update program = new_program;
    }}

    transition!{ crash(lbl: Label, new_program: T, new_disk: DiskModel) {
        require lbl is Crash;

        // TODO: do we want the equivalent reply id constraint?
        require pre.program.next(&new_program, ProgramLabel::Crash{});
        require DiskModel::next(pre.disk, new_disk, DiskLabel::Crash{});

        update program = new_program;
        update disk = new_disk;
    }}

    transition!{ noop(lbl: Label) {
        require lbl is Noop;
    }}
}}

pub trait RefinementObligation {
    /// state machine refinement traits

    spec fn init(&self) -> bool;

    spec fn next(&self, post: &Self, lbl: SystemModel::Label) -> bool;

    spec fn i(&self) -> (ctam: CrashTolerantAsyncMap::State);

    spec fn i_lbl(lbl: SystemModel::Label) -> (ctam_lbl: CrashTolerantAsyncMap::Label);

    // restrict i_lbl result for application facing labels
    proof fn i_lbl_valid(lbl: SystemModel::Label, ctam_lbl: CrashTolerantAsyncMap::Label)
        requires 
            ctam_lbl == Self::i_lbl(lbl)            
        ensures 
            (lbl is ProgramAsyncOp && lbl->program_lbl.is_app_label()) <==> ctam_lbl is OperateOp,
            (lbl is ProgramAsyncOp && lbl->program_lbl.is_app_label())
                ==> lbl->program_lbl.to_async_map_label() == ctam_lbl->base_op
    ;

    proof fn init_refines(&self)
        requires self.init()
        ensures CrashTolerantAsyncMap::State::initialize(self.i())
    ;

    proof fn next_refines(&self, post: &Self, lbl: SystemModel::Label)
        requires self.next(post, lbl)
        ensures CrashTolerantAsyncMap::State::next(self.i(), post.i(), Self::i_lbl(lbl))
    ;
}

// Auditor defiend obligation for p
// impl<T: ProgramModel> RefinementObligation for SystemModel::State<T> {
//     open spec fn init(&self) -> bool
//     {
//         true
//     }
// }

// disk token label => 

// 
// 



}
