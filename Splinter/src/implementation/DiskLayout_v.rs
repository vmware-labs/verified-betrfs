// Copyright 2018-2024 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, University of Washington
// SPDX-License-Identifier: BSD-2-Clause
use vstd::{prelude::*};
use vstd::hash_map::*;
use crate::spec::MapSpec_t::*;
use crate::spec::AsyncDisk_t::*;
use crate::spec::ImplDisk_t::*;
use crate::spec::KeyType_t::*;
use crate::spec::Messages_t::*;
use crate::spec::TotalKMMap_t::*;
use crate::spec::FloatingSeq_t::*;
use crate::abstract_system::MsgHistory_v::{MsgHistory, KeyedMessage};
use crate::abstract_system::StampedMap_v::*;

verus! {

pub type iLSN = u64;

pub open spec(checked) fn singleton_floating_seq(at_index: nat, kmmap: TotalKMMap) -> FloatingSeq<Version>
{
    FloatingSeq::new(at_index, at_index+1,
          |i| Version{ appv: MapSpec::State{ kmmap } } )
}

pub open spec(checked) fn view_store_as_kmmap(store: HashMapWithView<Key, Value>) -> TotalKMMap
{
    TotalKMMap(Map::new(
            |k: Key| true,
            |k: Key| if store@.contains_key(k@) { Message::Define{value: store@[k@]} }
                     else { Message::empty() }))
}

pub open spec(checked) fn view_store_as_singleton_floating_seq(at_index: nat, store: HashMapWithView<Key, Value>) -> FloatingSeq<Version>
{
    singleton_floating_seq(at_index, view_store_as_kmmap(store))
}

pub struct Superblock {
    pub store: PersistentState, // mapspec
    // need version so recovery knows the shape of the (mostly-empty) history to reconstruct (the LSN)
    pub version_index: nat,
}

// NOTE: all subfields must be pub 
pub struct Journal {
    pub msg_history: Vec<KeyedMessage>,
    pub seq_start: iLSN,
}

impl View for Journal {
    type V = MsgHistory;

    open spec fn view(&self) -> Self::V
    {
        let seq_start = self.seq_start as nat;
        let seq_end = (self.msg_history.len() + seq_start) as nat;
        let msgs = Map::new(
            |k: LSN| seq_start <= k < seq_end,
            |k: LSN| self.msg_history@[k - seq_start]
        );
        MsgHistory{msgs, seq_start, seq_end}
    }
}

pub struct ISuperblock {
    pub journal: Journal
}

impl View for ISuperblock {
    type V = Superblock;

    open spec fn view(&self) -> Self::V
    {
        let map = self.journal.to_stamped_map();
        Superblock{
            store: PersistentState{ appv: MapSpec::State{ kmmap: map.value}},
            version_index: map.seq_end
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

pub fn marshall(sb: &ISuperblock) -> (out: RawPage)
ensures
    out == spec_marshall(sb@)
{
    assume( false ); // TODO
    unreached()
}

pub fn unmarshall(raw_page: &RawPage) -> (out: ISuperblock)
ensures
    out@ == spec_unmarshall(*raw_page)
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
    &&& disk.contains_key(spec_superblock_addr())
    &&& disk[spec_superblock_addr()] ==
        spec_marshall(Superblock{
            store: PersistentState{ appv: my_init() },
            version_index: 0,
        })
}

}//verus!
