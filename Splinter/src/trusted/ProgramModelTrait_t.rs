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
    AcceptSyncRequest{ sync_req_id: SyncReqId },
    DeliverSyncReply{ sync_req_id: SyncReqId },
}

pub struct ProgramDiskInfo{
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

pub trait ProgramModelTrait : Sized {
    spec fn is_mkfs(disk: DiskModel) -> bool;
    spec fn init(pre: Self) -> bool;
    spec fn next(pre: Self, post: Self, lbl: ProgramLabel) -> bool;
}

}
