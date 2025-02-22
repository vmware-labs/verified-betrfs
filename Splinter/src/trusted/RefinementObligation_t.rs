// Copyright 2018-2024 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, University of Washington
// SPDX-License-Identifier: BSD-2-Clause

#![allow(unused_imports)]
use builtin::*;

use builtin_macros::*;
use state_machines_macros::state_machine;
use vstd::prelude::*;
use vstd::{map::*, seq::*, bytes::*, set::*, multiset::*};

use crate::trusted::ProgramModelTrait_t::*;
use crate::trusted::SystemModel_t::*;

use crate::spec::AsyncDisk_t::*;
use crate::spec::MapSpec_t::{ID, SyncReqId, Request, Reply};
use crate::spec::MapSpec_t::{AsyncMap, CrashTolerantAsyncMap};
// TODO: move this somewhere else? or we can use disk lbl instead
use crate::implementation::MultisetMapRelation_v::*; 

verus!{

pub open spec fn externally_visible(ctam_lbl: CrashTolerantAsyncMap::Label) -> bool
{
    ||| ctam_lbl is OperateOp && (ctam_lbl->base_op is RequestOp || ctam_lbl->base_op is ReplyOp)
    ||| ctam_lbl is ReqSyncOp
    ||| ctam_lbl is ReplySyncOp
    ||| ctam_lbl is CrashOp
}
// visible ctam op

impl SystemModel::Label {
    pub open spec fn label_correspondence(self, ctam_lbl: CrashTolerantAsyncMap::Label) -> bool
    {
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
                    ProgramUserOp::AcceptSyncRequest{sync_req_id} => {
                        ctam_lbl == CrashTolerantAsyncMap::Label::ReqSyncOp{sync_req_id}
                    },
                    ProgramUserOp::DeliverSyncReply{sync_req_id} => {
                        ctam_lbl == CrashTolerantAsyncMap::Label::ReplySyncOp{sync_req_id}
                    },
                    _ => { !externally_visible(ctam_lbl) }
                }
            },
            Self::Crash => {
                ctam_lbl == CrashTolerantAsyncMap::Label::CrashOp{}
            },
            _ => { !externally_visible(ctam_lbl) },
        }
    }
}

pub trait RefinementObligation<Model: ProgramModelTrait> : Sized {

    spec fn inv(model: SystemModel::State<Model>) -> bool;
    
    spec fn i(model: SystemModel::State<Model>) -> (ctam: CrashTolerantAsyncMap::State);

    spec fn i_lbl(pre: SystemModel::State<Model>, post: SystemModel::State<Model>, lbl: SystemModel::Label) -> (ctam_lbl: CrashTolerantAsyncMap::Label);

    // restrict i_lbl result to ensure app label correspondence 
    proof fn i_lbl_valid(pre: SystemModel::State<Model>, post: SystemModel::State<Model>, lbl: SystemModel::Label, ctam_lbl: CrashTolerantAsyncMap::Label)
        requires
            ctam_lbl == Self::i_lbl(pre, post, lbl)
        ensures
            lbl.label_correspondence(ctam_lbl)
    ;

    proof fn init_refines(pre: SystemModel::State<Model>)
    requires
        SystemModel::State::initialize(pre, pre.program, pre.disk)
    ensures
        CrashTolerantAsyncMap::State::initialize(Self::i(pre)),
        Self::inv(pre)
    ;
        
    proof fn next_refines(pre: SystemModel::State<Model>, post: SystemModel::State<Model>, lbl: SystemModel::Label)
    requires
        SystemModel::State::next(pre, post, lbl), Self::inv(pre),
    ensures
        CrashTolerantAsyncMap::State::next(Self::i(pre), Self::i(post), Self::i_lbl(pre, post, lbl)),
        Self::inv(post)
    ;
}
}
