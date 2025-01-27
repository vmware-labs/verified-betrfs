// Copyright 2018-2024 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, University of Washington
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

pub type DiskModel = AsyncDisk::State;
pub type DiskLabel = AsyncDisk::Label;

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

pub trait ProgramModel : Sized {
    spec fn init(pre: Self, disk: DiskModel) -> bool;
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
        // full system crashes
        Crash,
        Noop,

        // NOTE: 
        // Sync isn't included as a system model label because 
        // the actual sync point is driven by the program model
    }

    init!{ initialize(program: T, disk: DiskModel) {
        require T::init(program, disk);
        init program = program;
        init disk = disk;
        init id_history = Set::empty();
    }}

    transition!{ program_async(lbl: Label, new_program: T) {
        require lbl is ProgramAsyncOp;
        require lbl->program_lbl.is_app_label();

        let new_id = if lbl->program_lbl is AcceptRequest {
            Set::empty().insert(lbl->program_lbl.arrow_AcceptRequest_req().id)
        } else { Set::empty() };

        // auditor's promise: new request contains unique ID
        require pre.id_history.disjoint(new_id);
        // new program must be a valid step
        require T::next(pre.program, new_program, lbl->program_lbl);

        update program = new_program;
        update id_history = pre.id_history.union(new_id);
    }}

    transition!{ program_disk(lbl: Label, new_program: T, new_disk: DiskModel) {
        require lbl is ProgramDiskOp;
        require lbl->disk_lbl is DiskOps;

        require T::next(pre.program, new_program,
            ProgramLabel::DiskIO{disk_lbl: lbl->disk_lbl},
        );

        require DiskModel::next(pre.disk, new_disk, lbl->disk_lbl);
        
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

    transition!{ req_sync(lbl: Label, new_program: T) {
        require let Label::ProgramAsyncOp{
            program_lbl: ProgramLabel::ReqSync{sync_req_id} } = lbl;

        // promise unique sync id from all previous ids
        require !pre.id_history.contains(sync_req_id as u64);

        require T::next(pre.program, new_program, lbl->program_lbl);

        update program = new_program;
        update id_history = pre.id_history.insert(sync_req_id as u64);
    }}

    transition!{ reply_sync(lbl: Label, new_program: T) {
        require lbl is ProgramAsyncOp;
        require lbl->program_lbl is ReplySync;
        require T::next(pre.program, new_program, lbl->program_lbl);
        update program = new_program;
    }}

    transition!{ crash(lbl: Label, new_program: T, new_disk: DiskModel) {
        require lbl is Crash;
        require T::next(pre.program, new_program, ProgramLabel::Crash{});
        require DiskModel::next(pre.disk, new_disk, DiskLabel::Crash{});

        update program = new_program;
        update disk = new_disk;
        update id_history = Set::empty();
    }}

    transition!{ noop(lbl: Label) {
        require lbl is Noop;
    }}
}}

impl SystemModel::Label {
    pub open spec fn label_correspondance(self, ctam_lbl: CrashTolerantAsyncMap::Label) -> bool
    {
        &&& ctam_lbl is OperateOp <==> (self is ProgramAsyncOp && self->program_lbl.is_app_label())
        &&& ctam_lbl is OperateOp ==> 
            ctam_lbl->base_op == self->program_lbl.to_async_map_label()

        &&& ctam_lbl is ReqSyncOp <==> (self is ProgramAsyncOp && self->program_lbl is ReqSync)
        &&& ctam_lbl is ReqSyncOp ==> 
            ctam_lbl.arrow_ReqSyncOp_sync_req_id() == self->program_lbl.arrow_ReqSync_sync_req_id()

        &&& ctam_lbl is ReplySyncOp <==> (self is ProgramAsyncOp && self->program_lbl is ReplySync)
        &&& ctam_lbl is ReplySyncOp ==> 
            ctam_lbl.arrow_ReplySyncOp_sync_req_id() == self->program_lbl.arrow_ReplySync_sync_req_id()
    }
}

pub trait RefinementObligation {
    type Model: ProgramModel;

    spec fn inv(model: SystemModel::State<Self::Model>) -> bool;
    
    spec fn i(model: SystemModel::State<Self::Model>) -> (ctam: CrashTolerantAsyncMap::State);

    spec fn i_lbl(lbl: SystemModel::Label) -> (ctam_lbl: CrashTolerantAsyncMap::Label);

    // restrict i_lbl result to ensure app label correspondence 
    proof fn i_lbl_valid(lbl: SystemModel::Label, ctam_lbl: CrashTolerantAsyncMap::Label)
        requires
            ctam_lbl == Self::i_lbl(lbl)            
        ensures
            lbl.label_correspondance(ctam_lbl)
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
        CrashTolerantAsyncMap::State::next(Self::i(pre), Self::i(post), Self::i_lbl(lbl)),
        Self::inv(post)
    ;
}
}
