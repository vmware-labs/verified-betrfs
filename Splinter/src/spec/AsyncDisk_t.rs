// Copyright 2018-2023 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, University of Washington
// SPDX-License-Identifier: BSD-2-Clause

#![allow(unused_imports)]
use builtin::*;

use builtin_macros::*;
use state_machines_macros::state_machine;
use vstd::{map::*, seq::*, bytes::*};

use crate::spec::MapSpec_t::{ID};

verus!{

/// Address defined for spec code

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

/// Returns the number of a disk pages in an Allocation Unit. 
/// Left as an uninterpreted function since it's implementation defined.
pub closed spec(checked) fn page_count() -> nat;

/// Returns the number of Allocation Unit of the disk. 
/// Left as an uninterpreted function since it's implementation defined.
pub closed spec(checked) fn au_count() -> nat;

impl Address {
    /// Returns true iff this Address is well formed.
    pub open spec(checked) fn wf(self) -> bool {
        &&& self.au < au_count()
        &&& self.page < page_count()
    }
}

/// IAddress defined for executable code

pub type IAU = u32;

pub type IPage = u32;

pub struct IAddress {
    pub au: IAU,
    pub page: IPage,
}

/// further restricted by actual disk size
pub closed spec(checked) fn ipage_count() -> IPage;

/// further restricted by actual disk size
pub closed spec(checked) fn iau_count() -> IAU;

/// axioms relating spec and impl page and au count
#[verifier(external_body)]
pub broadcast proof fn page_count_equals_ipage_count()
    ensures page_count() == ipage_count()
;

#[verifier(external_body)]
pub broadcast proof fn au_count_equals_iau_count()
    ensures au_count() == iau_count()
;

/// models raw disk content
pub type UnmarshalledPage = Seq<u8>;

/// models the actual disk
pub struct Disk{
    pub content: Map<Address, UnmarshalledPage>,
}

pub enum DiskRequest {
    ReadReq{from: Address},
    WriteReq{to: Address, data: UnmarshalledPage},
}

pub enum DiskResponse {
    ReadResp{from: Address, data: UnmarshalledPage},
    WriteResp{to: Address},
}

state_machine!{ AsyncDisk {
    fields {
        // ephemeral states
        pub requests: Map<ID, DiskRequest>,
        pub responses: Map<ID, DiskResponse>,

        // persistent disk content
        pub disk: Disk,
    }

    pub enum Label {
        // models disk controller receiving & responding to disk ops
        DiskOps{requests: Map<ID, DiskRequest>, responses: Map<ID, DiskResponse>},  
        // models disk internal operation that actually read/write data
        Internal,
        // models the crash event
        Crash,
    }

    init!{ initialize() {
        init requests = Map::empty();
        init responses = Map::empty();
        init disk = Disk{ content: Map::empty() };
    }}

    // no changes to the disk content
    transition!{ disk_ops(lbl: Label){
        require lbl is DiskOps;

        // disallow req & resp of the same request in an atomic step
        require lbl->requests.dom().disjoint(lbl->responses.dom());

        // new requests can't overlap with pending requests
        require lbl->requests.dom().disjoint(pre.requests.dom());
        // new requests can't overlap with pending responses
        require lbl->requests.dom().disjoint(pre.responses.dom());

        // responses heard must come from the pending response set
        require lbl->responses.dom() <= pre.responses.dom();

        update requests = pre.requests.union_prefer_right(lbl->requests);
        update responses = pre.responses.remove_keys(lbl->responses.dom());
    }}

    // process reads
    transition!{ process_read(lbl: Label, id: ID){
        require lbl is Internal;

        // read processed must have been requested
        require pre.requests.dom().contains(id);
        require pre.requests[id] is ReadReq;
        require pre.requests[id]->from.wf();

        let read_resp = DiskResponse::ReadResp{
            from: pre.requests[id]->from, 
            data: pre.disk.content[pre.requests[id]->from],
        };

        update requests = pre.requests.remove(id);
        update responses = pre.responses.insert(id, read_resp);
    }}

    transition!{ process_read_failure(lbl: Label, id: ID, fake_content: UnmarshalledPage){
        require lbl is Internal;

        // read processed must have been requested
        require pre.requests.dom().contains(id);
        require pre.requests[id] is ReadReq;
        require pre.requests[id]->from.wf();
        
        // restriction possible fake content
        require fake_content != pre.disk.content[pre.requests[id]->from];
        // TODO: assume disk cannot fail from a checksum-correct state
        // to a different checksum-correct state (corrupted bits leads to mismatching checksums)

        let read_resp = DiskResponse::ReadResp{
            from: pre.requests[id]->from, 
            data: fake_content,
        };

        update requests = pre.requests.remove(id);
        update responses = pre.responses.insert(id, read_resp);
    }}

    // process writes
    transition!{ process_write(lbl: Label, id: ID){
        require lbl is Internal;
    
        // write processed must have been requested
        require pre.requests.dom().contains(id);
        require pre.requests[id] is WriteReq;
        require pre.requests[id]->to.wf();

        // TODO: require write data matches its checksum

        let write_req = pre.requests[id];
        let write_resp = DiskResponse::WriteResp{to: write_req->to};

        update requests = pre.requests.remove(id);
        update responses = pre.responses.insert(id, write_resp);
        update disk = Disk{content: pre.disk.content.insert(write_req->to, write_req->data) };
    }}

    // forgets pending requests and replies, no change to disk content
    transition!{ crash(lbl: Label){
        require lbl is Crash;

        update requests = Map::empty();
        update responses = Map::empty();
    }}

    #[invariant]
    pub open spec(checked) fn inv(self) -> bool {
        &&& self.requests.dom().disjoint(self.responses.dom())
    }

    #[inductive(initialize)]
    fn initialize_inductive(post: Self) { }
   
    #[inductive(disk_ops)]
    fn disk_ops_inductive(pre: Self, post: Self, lbl: Label) { }
   
    #[inductive(process_read)]
    fn process_read_inductive(pre: Self, post: Self, lbl: Label, id: ID) { }
   
    #[inductive(process_read_failure)]
    fn process_read_failure_inductive(pre: Self, post: Self, lbl: Label, id: ID, fake_content: UnmarshalledPage) { }
   
    #[inductive(process_write)]
    fn process_write_inductive(pre: Self, post: Self, lbl: Label, id: ID) { }
   
    #[inductive(crash)]
    fn crash_inductive(pre: Self, post: Self, lbl: Label) { }
}}

} // end of !verus
