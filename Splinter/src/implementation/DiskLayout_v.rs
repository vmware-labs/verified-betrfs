// Copyright 2018-2024 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, University of Washington
// SPDX-License-Identifier: BSD-2-Clause
use vstd::{prelude::*};
use vstd::hash_map::*;
//use vstd::pervasive::print_u64;
use crate::spec::MapSpec_t::*;
use crate::spec::AsyncDisk_t::*;
use crate::spec::ImplDisk_t::*;
use crate::spec::KeyType_t::*;
use crate::spec::Messages_t::*;
use crate::spec::TotalKMMap_t::*;
use crate::spec::FloatingSeq_t::*;

verus! {

pub closed spec(checked) fn singleton_floating_seq(at_index: nat, kmmap: TotalKMMap) -> FloatingSeq<Version>
{
    FloatingSeq::new(at_index, at_index+1,
          |i| Version{ appv: MapSpec::State{ kmmap } } )
}

pub closed spec(checked) fn view_store_as_kmmap(store: HashMapWithView<Key, Value>) -> TotalKMMap
{
    TotalKMMap(Map::new(
            |k: Key| true,
            |k: Key| if store@.contains_key(k@) { Message::Define{value: store@[k@]} }
                     else { Message::empty() }))
}

pub closed spec(checked) fn view_store_as_singleton_floating_seq(at_index: nat, store: HashMapWithView<Key, Value>) -> FloatingSeq<Version>
{
    singleton_floating_seq(at_index, view_store_as_kmmap(store))
}

pub struct Superblock {
    pub store: PersistentState,
    // need version so recovery knows the shape of the (mostly-empty) history to reconstruct (the LSN)
    pub version_index: nat,
}

pub struct ISuperblock {
    pub store: HashMapWithView<Key, Value>,
    // need version so recovery knows the shape of the (mostly-empty) history to reconstruct (the LSN)
    pub version_index: nat,
}

impl View for ISuperblock {
    type V = Superblock;
    open spec fn view(&self) -> Self::V
    {
        Superblock{
            store: PersistentState{ appv: MapSpec::State{ kmmap: view_store_as_kmmap(self.store)}},
            version_index: self.version_index
        }
    }
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
pub fn unmarshall(raw_page: RawPage) -> (out: ISuperblock)
ensures
    out@ == spec_unmarshall(raw_page)
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
            store: PersistentState{ appv: my_init() },
            version_index: 0,
        })
}

}//verus!
