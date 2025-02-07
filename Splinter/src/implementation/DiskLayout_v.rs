// Copyright 2018-2024 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, University of Washington
// SPDX-License-Identifier: BSD-2-Clause
use vstd::{prelude::*};
//use vstd::pervasive::print_u64;
use crate::spec::MapSpec_t::*;
use crate::spec::AsyncDisk_t::*;
use crate::spec::ImplDisk_t::*;

verus! {

pub struct Superblock {
    pub state: PersistentState,
    // need version so recovery knows the shape of the (mostly-empty) history to reconstruct (the LSN)
    pub version_index: nat,
}

pub closed spec fn spec_marshall(superblock: Superblock) -> (out: RawPage)
{
    arbitrary()
}

pub closed spec fn spec_unmarshall(raw_page: RawPage) -> (out: Superblock)
{
    arbitrary()
}

// This is gonna be hard because Superblock isn't physical yet :vP
pub fn unmarshall(raw_page: RawPage) -> (out: Superblock)
ensures
    out == spec_unmarshall(raw_page)
{
    assume( false ); // TODO
    unreached()
}

pub open spec fn spec_superblock_addr() -> Address {
    Address{au: 0, page: 0}
}

pub fn superblock_addr() -> (out: IAddress)
ensures out@ == spec_superblock_addr()
{
    IAddress{au: 0, page: 0}
}

pub open spec fn mkfs(disk: Disk) -> bool
{
    &&& disk.content.contains_key(spec_superblock_addr())
    &&& disk.content[spec_superblock_addr()] ==
        spec_marshall(Superblock{
            state: PersistentState{ appv: my_init() },
            version_index: 0,
        })
}

}//verus!
