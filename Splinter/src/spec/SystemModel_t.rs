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

pub enum ProgramUserOp{
    // add sync to request 
    // async operations with application clients
    AcceptRequest{req: Request},
    DeliverReply{reply: Reply},

    // declares the linearization point of each operation
    Execute{req: Request, reply: Reply},

    // program handling application client requested sync request
    AcceptSyncRequest{ sync_req_id: SyncReqId },
    DeliverSyncReply{ sync_req_id: SyncReqId },
}

impl ProgramUserOp {
    pub open spec fn to_ctam_label(self) -> CrashTolerantAsyncMap::Label 
    {
        if let Self::AcceptRequest{req} = self {
            CrashTolerantAsyncMap::Label::OperateOp{
                base_op: AsyncMap::Label::RequestOp{req} }
        } else if let Self::DeliverReply{reply} = self {
            CrashTolerantAsyncMap::Label::OperateOp{
                base_op: AsyncMap::Label::ReplyOp{reply} }
        } else if let Self::Execute{req, reply} = self {
            CrashTolerantAsyncMap::Label::OperateOp{
                base_op: AsyncMap::Label::ExecuteOp{req, reply} }
        } else {
            arbitrary()
        }
    }
}

// Auditor defines externally visible actions that can be taken by a program model
pub enum ProgramLabel{
    UserIO{op: ProgramUserOp},

    // captures program's interaction with the disk model,
    // e.g. loading/flushing/evicting cache pages
    // DiskIO{disk_reqs: Set<DiskRequest>, disk_resps: Set<DiskResponse>},
    DiskIO{disk_lbl: DiskLabel},

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

        // TODO(jonh): we can delete id_history assumption at this layer, now that we
        // found we have to encode it at the KVStoreTokenized layer.
        //
        // history of application requests that have been accepted,
        // auditor uses this to promise that every request has a unique ID 
        pub id_history: Set<ID>, 
    }

    // Crash Tolerance is driven by the program, system model merely serves to orchestrate
    // and restricts interactions between program, application clients, and the disk
    pub enum Label
    {
        // program model async operate op 
        // current transitions only support req, repy, execute ops 
        // expose this to enforce correspondance 
        ProgramUIOp{ op: ProgramUserOp },
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
        require T::is_mkfs(disk);
        require T::init(program);

        init program = program;
        init disk = disk;
        init id_history = Set::empty();
    }}

    transition!{ program_ui(lbl: Label, new_program: T) {
        require lbl is ProgramUIOp;

        let new_id = if lbl->op is AcceptRequest {
            Set::empty().insert(lbl->op.arrow_AcceptRequest_req().id)
        } else if lbl->op is AcceptSyncRequest {
            Set::empty().insert(lbl->op.arrow_AcceptSyncRequest_sync_req_id())
        } else { Set::empty() };

        // auditor's promise: new request contains unique ID
        require pre.id_history.disjoint(new_id);
        // new program must be a valid step
        require T::next(pre.program, new_program, ProgramLabel::UserIO{op: lbl->op});

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

    transition!{ crash(lbl: Label, new_program: T, new_disk: DiskModel) {
        require lbl is Crash;
        require T::init(new_program); 
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
    // I think this needed to be looser than what I just wrote.
    pub open spec fn label_correspondence(self, ctam_lbl: CrashTolerantAsyncMap::Label) -> bool
    {
        match self {
            Self::ProgramUIOp{op} => {
                match op {
                    ProgramUserOp::AcceptRequest{req} => {
                        ctam_lbl == CrashTolerantAsyncMap::Label::OperateOp{
                            base_op: AsyncMap::Label::RequestOp{req} }
                    },
                    ProgramUserOp::DeliverReply{reply} => {
                        ctam_lbl == CrashTolerantAsyncMap::Label::OperateOp{
                            base_op: AsyncMap::Label::ReplyOp{reply} }
                    },
                    ProgramUserOp::Execute{req, reply} => {
                        ctam_lbl == CrashTolerantAsyncMap::Label::OperateOp{
                            base_op: AsyncMap::Label::ExecuteOp{req, reply} }
                    },
                    ProgramUserOp::AcceptSyncRequest{sync_req_id} => {
                        ctam_lbl == CrashTolerantAsyncMap::Label::ReqSyncOp{sync_req_id}
                    },
                    ProgramUserOp::DeliverSyncReply{sync_req_id} => {
                        ctam_lbl == CrashTolerantAsyncMap::Label::ReplySyncOp{sync_req_id}
                    },
                }
            },
            Self::ProgramDiskOp{disk_lbl} => {
                ctam_lbl == CrashTolerantAsyncMap::Label::Noop{}
            },
            Self::ProgramInternal => {
                ctam_lbl == CrashTolerantAsyncMap::Label::Noop{}
            },
            Self::DiskInternal => {
                ctam_lbl == CrashTolerantAsyncMap::Label::Noop{}
            },
            Self::Crash => {
                ctam_lbl == CrashTolerantAsyncMap::Label::CrashOp{}
            },
            Self::Noop => {
                ctam_lbl == CrashTolerantAsyncMap::Label::Noop{}
            },
        }
    }
}



pub trait RefinementObligation {
    type Model: ProgramModel;

    spec fn inv(model: SystemModel::State<Self::Model>) -> bool;
    
    spec fn i(model: SystemModel::State<Self::Model>) -> (ctam: CrashTolerantAsyncMap::State);

    // TODO: need model to determine i_lbl's result, pre and post 
    // 
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
