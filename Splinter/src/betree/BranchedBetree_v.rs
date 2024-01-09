// #![allow(unused_imports)]
// use builtin::*;

// use builtin_macros::*;
// use state_machines_macros::state_machine;

// use vstd::prelude::*;

// use crate::spec::KeyType_t::*;
// use crate::spec::Messages_t::*;
// use crate::disk::GenericDisk_v::*;
// use crate::betree::Buffer_v::*;
// use crate::betree::LinkedBranch_v;
// use crate::betree::LinkedBufferSeq_v;
// use crate::betree::LinkedBufferSeq_v::BufferSeq;
// use crate::betree::BufferOffsets_v::*;
// use crate::betree::OffsetMap_v::*;
// use crate::betree::Memtable_v::*;
// use crate::betree::Domain_v::*;
// use crate::betree::PivotTable_v::*;
// use crate::betree::SplitRequest_v::*;
// use crate::abstract_system::StampedMap_v::*;
// use crate::abstract_system::MsgHistory_v::*;

// verus! {

// // Should be imported by use crate::disk::GenericDisk_v::*;
// // pub type Pointer = GenericDisk::Pointer;
// // pub type Address = GenericDisk::Address;

// pub type StampedBetree = Stamped<BranchedBetree::State>;
// pub type BranchDiskView = LinkedBranch_v::DiskView;

// pub struct BetreeNode {
//   pub branches: BranchSeq,
//   pub pivot_table: PivotTable,
//   pub children: seq<Pointer>,
//   pub flushedOffsets: BufferOffsets
// }

// // What is a BranchedBetree?
// // A BranchedBetree uses a B+tree as the write buffer for the tree
// // (??)
// pub mod BranchedBetree {

// pub struct State {
//   pub root: Pointer,
//   pub disk_view: diskView,
//   pub branch_disk_view: BranchDiskView
// }

// } // pub mod BranchedBetree

// } // verus!
