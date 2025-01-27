// Copyright 2018-2023 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, University of Washington
// SPDX-License-Identifier: BSD-2-Clause
use std::sync::atomic::{AtomicU64, Ordering};
use vstd::{prelude::*};

use crate::spec::MapSpec_t::{Request, Reply, Input};

// ------- breaks trust boundary -------
use crate::trusted::KVStoreTokenized_v::*;
// -------------------------------------

verus! {

// defines the set of allowable externally visible calls by the implementer program
// right now this is tightly integrated with the implementer's tokenized state machine 
// definition but ideally we want to provide a composed SM consisted of a trusted
// request & reply tokenized SM & a tokenized program SM

// external body to prevent unprotected construction
#[verifier::external_body]
pub struct ClientAPI{
    pub id: AtomicU64,
}

impl ClientAPI{
    #[verifier::external_body]
    pub fn new(instance: Ghost<KVStoreTokenized::Instance>) -> (out: Self)
        ensures out.instance() == instance
    {
        Self{id: AtomicU64::new(0)}
    }
    
    #[verifier::external_body]
    pub closed spec fn instance(&self) -> KVStoreTokenized::Instance;

    // right now this is a tightly coupled API, we cannot ensure that the result is 
    // comes from the tokenized state machine instance transition due to it being in proof mode
    // we want (out.1, out.2) == self.instance().request(KVStoreTokenized::Label::RequestOp{req})
    // but this ensure is rolling out the result of the ensure
    #[verifier::external_body]
    pub fn receive_request(&self, print: bool) -> (out: (Request, Tracked<KVStoreTokenized::requests>))
    ensures
        out.1@@.instance == self.instance(),
        out.1@@.key == out.0,
        out.1@@.count == 1,
    {
        let id = self.id.fetch_add(1, Ordering::SeqCst);
        let amt = (id % 20) as u32;

        let input = if id % 3 == 0 {
            Input::NoopInput
        } else {
            Input::NoopInput
        };

        if print {
            println!("request {}: noooooop!", id);
        }

        (Request {input, id}, Tracked::assume_new())
    }

    // NOTE: corresponds to a tokenized state machine reply step, consumes the reply shard
    #[verifier::external_body]
    pub fn send_reply(&self, reply: Reply,  reply_shard: Tracked<KVStoreTokenized::replies>, print: bool)
        requires 
            reply_shard@@.instance == self.instance(),
            reply_shard@@.key == reply
    {
        if print {
            //let result = if reply.output.succeeded { "succeeded" } else { "failed" };
            println!("reply {}", reply.id);
        }
    }
}
} 

