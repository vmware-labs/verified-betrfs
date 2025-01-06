// Copyright 2018-2023 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, University of Washington
// SPDX-License-Identifier: BSD-2-Clause
use std::sync::atomic::{AtomicU64, Ordering};
use std::sync::Arc;
use vstd::{prelude::*, map::*, multiset::*};
use vstd::pervasive::print_u64;

use crate::BankSpec_t::{Request, Reply, Input, Output, ReqID};
// use crate::BankContract_t::BankTrait;

// ------- breaks trust boundary -------
use crate::Bank_v::*;
// -------------------------------------

verus! {

// defines the set of allowable externally visible calls by the implementer program
// right now this is tightly integrated with the implementer's tokenized state machine 
// definition but ideally we want to provide a composed SM consisted of a trusted
// request & reply tokenized SM & a tokenized program SM

// external body to prevent unprotected construction
#[verifier::external_body]
pub struct TrustedAPI{
    pub id: AtomicU64,
}

impl TrustedAPI{
    #[verifier::external_body]
    pub closed spec fn instance(&self) -> Bank::Instance;

    // right now this is a tightly coupled API, we cannot ensure that the result is 
    // comes from the tokenized state machine instance transition due to it being in proof mode
    // we want (out.1, out.2) == self.instance().request(Bank::Label::RequestOp{req})
    // but this ensure is rolling out the result of the ensure
    #[verifier::external_body]
    pub fn receive_request(&self, print: bool) -> (out: (Request, Tracked<Bank::requests>))
    ensures
        out.1@@.instance == self.instance(),
        out.1@@.key == out.0,
        out.1@@.count == 1,
    {
        let id = self.id.fetch_add(1, Ordering::SeqCst);
        let amt = (id % 20) as u32;

        let input = if id % 3 == 0 {
            Input { from: id as usize, to: (id + 1) as usize, amt}
        } else {
            Input { from: (id + 1) as usize, to: id as usize, amt}
        };

        if print {
            println!("request {}: transfer ${} from {} to {}", 
            id, input.amt, input.from, input.to,);
        }

        (Request {input, id}, Tracked::assume_new())
    }

    // NOTE: corresponds to a tokenized state machine reply step, consumes the reply shard
    #[verifier::external_body]
    pub fn send_reply(&self, reply: Reply,  reply_shard: Tracked<Bank::replies>, print: bool)
        requires 
            reply_shard@@.instance == self.instance(),
            reply_shard@@.key == reply
    {
        if print {
            let result = if reply.output.succeeded { "succeeded" } else { "failed" };
            println!("reply {}: {}", reply.id, result);
        }
    }
}
} 