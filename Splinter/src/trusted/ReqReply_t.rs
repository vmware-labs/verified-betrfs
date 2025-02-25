// Copyright 2018-2024 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, University of Washington
// SPDX-License-Identifier: BSD-2-Clause
use vstd::{prelude::*};
use builtin::*;
use builtin_macros::*;

use crate::spec::KeyType_t::*;
use crate::spec::Messages_t::*;

use crate::spec::MapSpec_t;
use crate::spec::MapSpec_t::{ID};

verus!{

#[derive(Debug)]
pub enum Input {
    QueryInput { key: Key },
    PutInput { key: Key, value: Value },
    SyncInput,
    NoopInput,
}

/// An Output represents the result from taking an Input action (and contains
/// any relevant return arguments from performing the corresponding action).
#[derive(Debug)]
pub enum Output {
    QueryOutput { value: Value },
    PutOutput,
    SyncOutput,
    NoopOutput,
    // TODO: Error Output (e.g. disk full)
}

#[derive(Debug)]
pub struct Request {
    pub input: Input,
    pub id: ID,
}

impl Request {
    pub open spec fn mapspec_req(self) -> MapSpec_t::Request
    {
        let input = match self.input {
            Input::QueryInput{key} => MapSpec_t::Input::QueryInput{key},
            Input::PutInput{key, value} => MapSpec_t::Input::PutInput{key, value},
            _ => MapSpec_t::Input::NoopInput,
        };
        MapSpec_t::Request{id: self.id, input}
    }
}

#[derive(Debug)]
pub struct Reply {
    pub output: Output,
    pub id: ID,
}

impl Reply {
    pub open spec fn mapspec_reply(self) -> MapSpec_t::Reply
    {
        let output = match self.output {
            Output::QueryOutput{value} => MapSpec_t::Output::QueryOutput{value},
            Output::PutOutput{} => MapSpec_t::Output::PutOutput{},
            _ => MapSpec_t::Output::NoopOutput,
        };
        MapSpec_t::Reply{id: self.id, output}
    }
}
}