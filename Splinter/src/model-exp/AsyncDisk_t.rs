// Copyright 2018-2023 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, University of Washington
// SPDX-License-Identifier: BSD-2-Clause

#![allow(unused_imports)]
use builtin::*;

use builtin_macros::*;
use state_machines_macros::state_machine;
use vstd::{map::*, seq::*, bytes::*};

use crate::spec::MapSpec_t::{ID};

verus!{

/// The `AU` type is the type for a unique allocation unit identifier (thus we use `nat`s).
/// 
/// An Allocation Unit (AU) is the minimum disk unit the "external" (i.e.: top-level) allocator
/// allocates to data structures like the Betree and Journal. Allocation Units
/// are made up of contiguous disk sectors. AUs are specified as part of the
/// Splinter implementation. The goal of having large allocation blocks is to
/// amortize allocation costs efficiently for large amounts of data.
pub type AU = nat;

/// A page index within an AU (disk pages, so for SSDs these are on the order of 4KB).
pub type Page = nat;

/// An Address specifies a specific disk address (i.e.: an address that identifies a disk sector (or whatever
/// atomic addressing unit the disk in question uses)).
/// It does this by combining an AU index with a page index within the AU.
pub struct Address {
    /// The Allocation Unit index this address resides within.
    pub au: AU,
    /// Page index within AU for this address. In the range [0,page_count).
    pub page: Page,
}

// can be anything
pub type UnmarshalledPage = Seq<u8>;

pub struct DiskView{
    pub entries: Map<Address, UnmarshalledPage>,
}

// disk model takes any number of disk ops
pub struct ReadRequest{
    pub addr: Address,
}

pub struct ReadResponse{
    pub addr: Address,
    pub content: UnmarshalledPage,
}

pub struct WriteRequest{
    pub addr: Address,
    pub content: UnmarshalledPage,
}

pub struct WriteResponse{
    pub addr: Address,
}

// when all requests during an op show up instantaenously 
state_machine!{ AsyncDisk {
    fields {
        pub read_requests: Map<ID, ReadRequest>,
        pub write_requests: Map<ID, WriteRequest>,
        pub read_responses: Map<ID, ReadResponse>,
        pub write_responses: Map<ID, WriteResponse>,

        // the disk
        pub contents: DiskView,
    }

    pub enum Label
    {
        // NOTE: Using ID as the key eliminates a read and write 

        // ReceiveReads{read_requests: Map<ID, ReadRequest>},  // disk receives read requests from program
        // ReceiveWrites{write_requests: Map<ID, WriteRequest>}, // disk receives write requests from program
        // AckReads{read_responses: Map<ID, ReadResponse>},
        // AckWrites{write_responses: Map<ID, WriteResponse>},
        // Label { read & write }
        // Map 
        DiskIO{read_requests: Map<ID, GeneralRequest>},  // disk receives read requests from program

        Internal{},
        Crash{},
    }

    init!{ initialize() {
        init read_requests = Map::empty();
        init write_requests = Map::empty();
        init read_responses = Map::empty();
        init write_responses = Map::empty();
        init contents = DiskView{ entries: Map::empty() }; // TODO: or this can be a fixed key range of actual disk?
    }}

    transition!{ receive_reads(lbl: Label){
        require lbl is ReceiveReads;
        require lbl->read_requests.dom().disjoint(pre.read_requests.dom()); // can't overlap with queued reads
        require lbl->read_requests.dom().disjoint(pre.read_responses.dom()); // can't overlap with responded reads
        update read_requests = pre.read_requests.union_prefer_right(lbl->read_requests);
    }}

    transition!{ receive_writes(lbl: Label){
        require lbl is ReceiveWrites;
        require lbl->write_requests.dom().disjoint(pre.write_requests.dom()); // can't overlap with queued reads
        require lbl->write_requests.dom().disjoint(pre.write_responses.dom()); // can't overlap with responded reads
        update write_requests = pre.write_requests.union_prefer_right(lbl->write_requests);
    }}

    transition!{ ack_reads(lbl: Label){
        require lbl is AckReads;
        require lbl->read_responses <= pre.read_responses;
        update read_responses = pre.read_responses.remove_keys(lbl->read_responses.dom());
    }}

    transition!{ ack_writes(lbl: Label){
        require lbl is AckWrites;
        require lbl->write_responses <= pre.write_responses;
        update write_responses = pre.write_responses.remove_keys(lbl->write_responses.dom());
    }}

    // transitions model internal disk op that generates write or read responses
    

    transition!{ noop(lbl: Label){
        require lbl is Internal;
    }}

    transition!{ crash(lbl: Label){
        require lbl is Crash;
        update read_requests = Map::empty();
        update write_requests = Map::empty();
        update read_responses = Map::empty();
        update write_responses = Map::empty();
    }}
} }// end of state machine AsyncDisk

} // end of !verus