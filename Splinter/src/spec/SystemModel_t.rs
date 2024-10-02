// Copyright 2018-2023 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, University of Washington
// SPDX-License-Identifier: BSD-2-Clause

#![allow(unused_imports)]
use builtin::*;

use builtin_macros::*;
use state_machines_macros::state_machine;
use vstd::{map::*, seq::*, bytes::*};

use crate::spec::AsyncDisk_t::*;
use crate::spec::MapSpec_t::{ID, SyncReqId, Request, Reply};
use crate::spec::MapSpec_t::{AsyncMap, CrashTolerantAsyncMap};

verus!{

type DiskModel = AsyncDisk::State;
type DiskLabel = AsyncDisk::Label;

// player 1 defines label used by program model

pub enum ProgramLabel{
    AcceptRequest{req: Request},
    DeliverReply{reply: Reply},

    // declare application linearization point
    Execute{req: Request, reply: Reply}, 

    // disk operation: loading/flushing/evicting cache pages
    DiskIO{disk_lbl: DiskLabel},

    // program internal operation, no disk or application i/o
    Internal{},

    Crash,
    None,
}

// player 1 defines program model obligation

pub trait ProgramModel {

    spec fn init(&self, disk: DiskModel) -> bool;

    spec fn next(&self, post: &Self, lbl: ProgramLabel) -> bool;
}

state_machine!{ SystemModel<T: ProgramModel> {
    fields {
        // program is simply an application I/O and disk I/O driver wih proof obligations
        pub program: T,
        // trusted disk model advances with the program model
        pub disk: DiskModel,
    }

    // system model are identical
    pub enum Label
    {
        // Operate{ base_op: AsyncMap::Label },
        ProgramInternal,
        DiskInternal,

        Sync, // models moment of persistence on disk
        ReqSync{ sync_req_id: SyncReqId },
        ReplySync{ sync_req_id: SyncReqId },

        Crash,
        Noop,
    }
    
    // transition!{
    //     operate(label: Label, new_program: T, new_disk: DiskModel, disk_lbl: DiskLabel) {
    //         require let Label::Operate{ base_op } = label;
    //         require let DiskLabel::DiskOps{ disk_reqs, disk_resps } = disk_lbl;

    //         // UI operation should not generate any disk traffic
    //         require base_op is RequestOp ==> disk_reqs.is_empty() && disk_resps.is_empty();
    //         require base_op is ReplyOp ==> disk_reqs.is_empty() && disk_resps.is_empty();

    //         // require pre.program.next(&new_program,)
    //         // TODO: restriction on the program label
    //         // require pre.program.next(&new_program, program_lbl);
    //         // require DiskModel::next(pre.disk, new_disk, disk_lbl);

    //         update program = new_program;
    //         update disk = new_disk;
    //     }
    // }

    // transition!{
    //     program_internal(label: Label, new_p: ProgramModel::State) {
    //         require let Label::Noop = label;
    //         require ProgramModel::State::next(pre.p, new_p, ProgramModel::Label::Internal{});
    //         update p = new_p;
    //     }
    // }
        
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
        // ensures 
        //     lbl is Operate ==> {
        //         &&& ctam_lbl is OperateOp 
        //         &&& !(lbl->base_op is ExecuteOp) ==> lbl->base_op == ctam_lbl->base_op 
        //     }
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

// Implemented by Player 2

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