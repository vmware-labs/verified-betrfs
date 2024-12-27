// Copyright 2018-2024 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, University of Washington
// SPDX-License-Identifier: BSD-2-Clause

#![allow(unused_imports)]
use builtin::*;

use builtin_macros::*;
use state_machines_macros::state_machine;
use crate::spec::MapSpec_t::*;

verus!{
    
    // SystemModel<ProgramModel> is a state machine defining the bottom layer
    // interaction  of player 2's program model and the disk model
    // has the same set of label as the top layer spec CrashTolerantAsyncMap

    // program model can take 
    
    state_machine!{ SystemModel<ProgramModel> {

        // ProgramModel: a player 2 state machine that interacts with application request and IO controller
        type ProgramModel: APPIODriver; 
        type DiskModel = AsyncDisk;

        fields{
            p: ProgramModel,
            d: DiskModel,
        }

        pub enum Label
        {
            // restriction on the application visible labels
            // player 2 can perform any arbitrary label translation

            OperateOp{ base_op: ProgramModel::Label },
            CrashOp,

            // maybe we don't want exactly the same label 
            SyncOp, // should this be present here?
            ReqSyncOp{ request_info },
            ReplySyncOp{ reply_info },
            // -----------------------------------------

            Noop,
        }

        transition!{
            // captures program model req, execute, reply
            // captures program internal and disk internal ops
            operate(label: Label, new_p: ProgramModel::State, new_d: DiskModel) {
                require let Label::OperateOp{ base_op } = label;
                // may want to restrict disk label to not be a sync?
                require ProgramModel::State::next(pre.p, new_p, base_op.program_label);
                require DiskModel::State::next(pre.d, new_d, base_op.disk_label);
                update p = new_p;
                update d = new_d;
            }
        }

        transition!{
            crash(label: Label, new_p: ProgramModel::State, new_d: DiskModel) {
                require let Label::CrashOp = label;
                require ProgramModel::State::next(pre.p, new_p, ProgramModel::Label::Crash);
                require DiskModel::State::next(pre.d, new_d, DiskModel::Label::Crash);
                update p = new_p;
                update d = new_d;
            }
        }

        transition!{
            // models a super block write landing
            sync(label: Label, new_d: DiskModel) {
                require let Label::SyncOp = label;
                require DiskModel::State::next(pre.d, new_d, DiskModel::Label::Sync{...}); // ? 
                update d = new_d;
            }
        }

        transition!{
            req_sync(label: Label, new_p: ProgramModel::State, new_d: DiskModel) {
                require let Label::ReqSyncOp{ sync_req_id } = label;
                require ProgramModel::State::next(pre.p, new_p, ProgramModel::Label::ReqSync{...});
                require DiskModel::State::next(pre.d, new_d, DiskModel::Label::DiskIO{...});
                update p = new_p;
                update d = new_d;
            }
        }

        transition!{
            reply_sync(label: Label, new_p: ProgramModel::State, new_d: DiskModel) {
                require let Label::ReplySyncOp{ sync_req_id } = label;
                require ProgramModel::State::next(pre.p, new_p, ProgramModel::Label::ReplySync{...});
                require DiskModel::State::next(pre.d, new_d, DiskModel::Label::DiskIO{...});
                update p = new_p;
                update d = new_d;
            }
        }

        transition!{
            disk_internal(label: Label, new_d: DiskModel) {
                require let Label::Noop = label;
                require DiskModel::State::next(pre.d, new_d, DiskModel::Label::Internal{});
                update d = new_d;
            }
        }

    
    }}

    // responsibility of player 2 to implement
    trait Obligation {

        type ProgramModel: APPIODriver; 

        /*
            Model Refinement Trait: requires a demonstration that the system model state machine
            can refine to the AsyncMap.State state machine
        */

        spec fn i(s: SystemModel<ProgramModel>) -> AsyncMap::State

        spec fn i_lbl(lbl: SystemModel::Label) -> AsyncMap::Label
            requires lbl is XXX
        {
            match lbl {
                ...
            }
        }

        // freedom for p2
        spec fn i_p2_lbl(lbl: SystemModel::Label) -> (result: AsyncMap::Label)
            requires lbl !is XXX
            ensures result !is XXX
        ;

        spec fn inv(s: SystemModel<ProgramModel>) -> bool

        proof fn init_refines(s: SystemModel<ProgramModel>)
            requires init(s)
            ensures inv(s)

        proof fn inv_next(s: SystemModel<ProgramModel>, s2:  SystemModel<ProgramModel>)
            requires inv(s), next(s, s2)
            ensures inv(s2) 

        
        proof fn next_refines(s: SystemModel<ProgramModel>, s2:  SystemModel<ProgramModel>)
            requires inv(s), next(s, s2), inv(s2)
            ensures AsyncMap.next(s.i(), s2.i())

        
        // implementation entry point
        // TODO: we don't have a good way to use the rust build system to prevent 
        // unwanted calls to std lib or other system calls         
        fn entry_point(a: APPIOPerm, Transition<ProgramModel>);

        // application & io correspondence captured within APPIOPerm object
        // io linearization rules

        // TODO: either a trait or a struct that encapsulate IO permissions
        // IOPerm_t struct that can be included by player 2 to perform IO
        // how to enforce application correspondance 
        
    }

   
}