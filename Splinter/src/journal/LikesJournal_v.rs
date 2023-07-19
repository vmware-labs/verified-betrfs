// Copyright 2018-2021 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, and University of Washington
// SPDX-License-Identifier: BSD-2-Clause
//
#![allow(unused_imports)]
use builtin::*;
use vstd::prelude::*;
use vstd::{map::*,multiset::*};

use builtin_macros::*;
use state_machines_macros::state_machine;

use crate::abstract_system::StampedMap_v::LSN;
use crate::abstract_system::MsgHistory_v::*;
use crate::journal::LinkedJournal_v::TruncatedJournal;
use crate::journal::LinkedJournal_v::DiskView;
use crate::disk::GenericDisk_v::*;
use crate::allocation_layer::Likes_v::*;

verus!{
    pub open spec(checked) fn singleton_index(start: LSN, end: LSN, value: Address) -> Map<LSN, Address>
    {
        Map::new(|x: LSN| start <= x < end, |x:LSN| value)
    }

    impl DiskView {
        pub open spec(checked) fn build_lsn_addr_index(self, root: Pointer) -> Map<LSN, Address>
        recommends
            self.decodable(root), self.acyclic(),
            root.is_Some() ==> self.boundary_lsn < self.entries[root.unwrap()].message_seq.seq_end,
        decreases self.the_rank_of(root) when self.decodable(root) && self.acyclic()
        {
            if root.is_None() {
                map!{}
            } else {
                let curr_msgs = self.entries[root.unwrap()].message_seq;
                let start_lsn = if self.boundary_lsn > curr_msgs.seq_start { self.boundary_lsn } else { curr_msgs.seq_start };
                let update = singleton_index(start_lsn, curr_msgs.seq_end, root.unwrap());

                update.union_prefer_right(self.build_lsn_addr_index(self.entries[root.unwrap()].cropped_prior(self.boundary_lsn)))
            }
        }
    } // end of impl DiskView

    pub open spec(checked) fn map_to_likes(lsn_addr_map: Map<LSN, Address>) -> Likes
        decreases lsn_addr_map.dom().len() when lsn_addr_map.dom().finite()
    {
        if lsn_addr_map.dom().len() == 0 {
            no_likes()
        } else {
            let k = lsn_addr_map.dom().choose();
            let sub_likes = map_to_likes(lsn_addr_map.remove(k));
            Multiset::empty().insert(lsn_addr_map[k]).add(sub_likes)
        }
    }

    impl TruncatedJournal {
        pub open spec(checked) fn build_lsn_addr_index(self) ->  Map<LSN, Address>
            recommends self.decodable()
        {
            self.disk_view.build_lsn_addr_index(self.freshest_rec)
        }
    
        pub open spec /*XXX(checked)*/ fn transitive_likes(self) -> Likes 
        {
            if !self.decodable() {
                no_likes()
            } else {
                //XXX need an ensures that build_lsn_addr_index gives a finite map
                let lsn_addr_map = self.build_lsn_addr_index();
                // TODO(verus): map.Values && multiset constructor
                // we just want to have multiset{lsn_addr_map.values}
                map_to_likes(lsn_addr_map)
            }
        }
    }
}
