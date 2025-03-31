// Copyright 2018-2023 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, University of Washington
// SPDX-License-Identifier: BSD-2-Clause
use std::sync::atomic::{AtomicU64, Ordering};
use vstd::{prelude::*};
use vstd::tokens::InstanceId;

use crate::spec::MapSpec_t::{ID};
use crate::spec::KeyType_t::Key;
use crate::spec::Messages_t::Value;
use crate::spec::ImplDisk_t::*;

use crate::implementation::MultisetMapRelation_v::*;    // TODO move to _t, I guess

use crate::trusted::ReqReply_t::*;
use crate::trusted::KVStoreTokenized_t::*;
use crate::trusted::ProgramModelTrait_t::*;

verus! {

// defines the set of allowable externally visible calls by the implementer program
// right now this is tightly integrated with the implementer's tokenized state machine 
// definition but ideally we want to provide a composed SM consisted of a trusted
// request & reply tokenized SM & a tokenized program SM

// external body to prevent unprotected construction
#[verifier::external_body]
#[verifier::reject_recursive_types(ProgramModel)]
pub struct ClientAPI<ProgramModel: ProgramModelTrait>{
    pub id: AtomicU64,
    pub inputs: Vec<Input>,
    pub _p: std::marker::PhantomData<(ProgramModel,)>,
}

pub struct PollResult {
    pub user_input_ready: bool,
    pub disk_response_ready: bool,
}

impl<ProgramModel: ProgramModelTrait> ClientAPI<ProgramModel>{
    #[verifier::external_body]
    pub fn new(instance: Ghost<InstanceId>) -> (out: Self)
        ensures out.instance_id() == instance
    {
        let inputs = vec![
            Input::NoopInput{},
            Input::PutInput{key: Key(1), value: Value(11)},
            Input::QueryInput{key: Key(1)},
            Input::QueryInput{key: Key(0)},
            Input::QueryInput{key: Key(3)},
            Input::PutInput{key: Key(3), value: Value(33)},
            Input::QueryInput{key: Key(3)},
        ];

        Self{id: AtomicU64::new(0), inputs, _p: arbitrary()}
    }
    
    #[verifier::external_body]
    pub uninterp spec fn instance_id(&self) -> InstanceId;

    // right now this is a tightly coupled API, we cannot ensure that the result is 
    // comes from the tokenized state machine instance transition due to it being in proof mode
    // we want (out.1, out.2) == self.instance_id().request(KVStoreTokenized::Label::RequestOp{req})
    // but this ensure is rolling out the result of the ensure
    #[verifier::external_body]
    pub fn receive_request(&mut self, print: bool) -> (out: (Request, Tracked<KVStoreTokenized::requests<ProgramModel>>))
    ensures
        self.instance_id() == old(self).instance_id(),
        out.1@.instance_id() == self.instance_id(),
        out.1@.element() == out.0,
    {
        let id = self.id.fetch_add(1, Ordering::SeqCst);
        let input = if 0 < self.inputs.len() { self.inputs.remove(0) }
            else { Input::NoopInput{} };    // TODO: block instead

        let request = Request {input, id};
        if print {
            println!("request input {:?}", request);
        }

        (request, Tracked::assume_new())
    }

    #[verifier::external_body]
    pub fn receive_noop_request(&mut self) -> (out: (Request, Tracked<KVStoreTokenized::requests<ProgramModel>>))
    ensures
        self.instance_id() == old(self).instance_id(),
        out.1@.instance_id() == self.instance_id(),
        out.1@.element() == out.0,
        (out.0.input == Input::NoopInput{}),
    {
        let id = self.id.fetch_add(1, Ordering::SeqCst);
        let input = Input::NoopInput{};
        let request = Request {input, id};
        (request, Tracked::assume_new())
    }


    // NOTE: corresponds to a tokenized state machine reply step, consumes the reply shard
    #[verifier::external_body]
    pub fn send_reply(&self, reply: Reply,  reply_shard: Tracked<KVStoreTokenized::replies<ProgramModel>>, print: bool)
        requires 
            reply_shard@.instance_id() == self.instance_id(),
            reply_shard@.element() == reply
    {
        if print {
            println!("   reply {:?}", reply);
            println!("");
        }
    }

    #[verifier::external_body]
    pub proof fn send_disk_request_predict_id(&self) -> (tracked out: ID)
    {
        //Tracked::assume_new()
        let Tracked(out) = Tracked::assume_new(); out
    }

    #[verifier::external_body]
    pub fn send_disk_request(&mut self, disk_req: IDiskRequest, id_perm: Tracked<ID>, 
        disk_request_tokens: Tracked<KVStoreTokenized::disk_requests_multiset<ProgramModel>>) -> (out: ID)
    requires
        disk_request_tokens@.multiset() == multiset_map_singleton(id_perm@, disk_req@),
    ensures
        self.instance_id() == old(self).instance_id(),
        out == id_perm@,
    {
        let id = self.id.fetch_add(1, Ordering::SeqCst);
        id
    }

    // TODO make this async or polling Option or maybe a cheap proof-free way to poll whether a
    // response is waiting?
    #[verifier::external_body]
    pub fn receive_disk_response(&mut self)
        -> (out: (ID, IDiskResponse, Tracked<KVStoreTokenized::disk_responses_multiset<ProgramModel>>))
    ensures
        self.instance_id() == old(self).instance_id(),
        out.2@.instance_id() == self.instance_id(),
        out.2@.multiset() == multiset_map_singleton(out.0, out.1@),
    {
        (0, arbitrary(), Tracked::assume_new())
    }

    // TODO(jonh): none of this stuff is gonna work until we, you know, implement it.
    // Returns a hint as to which receive_* method may be called without blocking. If neither
    // is ready, this method blocks until one is.
    #[verifier::external_body]
    pub fn poll(&self) -> (out: PollResult)
    {
        PollResult{
            user_input_ready: true,
            disk_response_ready: true,
        }
    }
        
    // Seems like it should always be okay to brew up a token containing an empty multiset (an empty shard).
    // Yeah, MultisetToken::empty() does that.
//     #[verifier::external_body]
//     pub proof fn receive_disk_nothing(&self) -> (out: KVStoreTokenized::disk_requests_multiset)
//     ensures
//         out@.instance_id() == self.instance_id(),
//     {
//         Tracked::assume_new()
//     }

}
} 

