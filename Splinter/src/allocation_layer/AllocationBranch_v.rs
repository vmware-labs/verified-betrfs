// Copyright 2018-2024 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, University of Washington
// SPDX-License-Identifier: BSD-2-Clause
use builtin::*;

use builtin_macros::*;

use vstd::prelude::*;
use crate::spec::KeyType_t::*;
use crate::spec::Messages_t::*;
use crate::disk::GenericDisk_v::*;
use crate::betree::Utils_v::*;
use crate::betree::Buffer_v::*;
use crate::betree::BufferDisk_v::*;
use crate::betree::LinkedBranch_v::*;
use crate::betree::LinkedBranch_v::Refinement_v;
use crate::allocation_layer::MiniAllocator_v::*;

verus!{

// Allocation Branch 
// first need a summary type 
pub type Summary = Set<AU>; // describe the set of AUs occupied by the rest of the b+tree
pub type BranchNode = Node<Summary>;

impl Buffer for BranchNode {
    open spec fn linked_contains(self, dv: BufferDisk<Self>, addr: Address, key: Key) -> bool 
    {
        self.linked_query(dv, addr, key) == Message::Update{ delta: nop_delta() }
    }

    open spec fn linked_query(self, dv: BufferDisk<Self>, addr: Address, key: Key) -> Message 
    {
        LinkedBranch{root: addr, disk_view: DiskView{entries: dv.entries}}.query(key)
    }

    open spec fn i(self, dv: BufferDisk<Self>, addr: Address) -> SimpleBuffer 
    {
        LinkedBranch{root: addr, disk_view: DiskView{entries: dv.entries}}.i().i()
    }
}

pub enum BuildEvent {
    Initialize{addr: Address},
    Insert{key: Key, msg: Message, path: Path<Summary>},
    Append{keys: Seq<Key>, msgs: Seq<Message>, path: Path<Summary>},
    Split{addr: Address, path: Path<Summary>, split_arg: SplitArg},
    AllocFill{},
    Seal{aux_ptr: Pointer},
}

pub struct AllocationBranch {
    pub branch: Option<LinkedBranch<Summary>>,
    pub mini_allocator: MiniAllocator,
}

impl AllocationBranch {
    pub open spec fn new(free_aus: Set<AU>) -> Self {
        AllocationBranch{
            branch: None,
            mini_allocator: MiniAllocator::empty().add_aus(free_aus),
        }
    }

    pub open spec fn can_initialize(self, addr: Address) -> bool
    {
        self.mini_allocator.can_allocate(addr)
    }

    pub open spec(checked) fn branch_initialize(self, addr: Address) -> Self 
        recommends self.can_initialize(addr)
    {
        AllocationBranch{
            branch: Some(empty_linked_branch(addr)),
            mini_allocator: self.mini_allocator.allocate(addr),
        }
    }

    pub open spec fn branch_query(self, key: Key) -> Message
        recommends self.branch is Some
    {
        self.branch.unwrap().query(key)
    }

    pub open spec fn can_insert(self, key: Key, msg: Message, path: Path<Summary>) -> bool
    {
        &&& self.branch is Some
        &&& self.branch.unwrap().can_insert(key, msg, path)
    }

    pub open spec fn branch_insert(self, key: Key, msg: Message, path: Path<Summary>) -> Self
        recommends self.can_insert(key, msg, path)
    {
        AllocationBranch{
            branch: Some(self.branch.unwrap().insert(key, msg, path)),
            ..self
        }
    }

    pub open spec fn can_append(self, keys: Seq<Key>, msgs: Seq<Message>, path: Path<Summary>) -> bool
    {
        &&& self.branch is Some
        &&& self.branch.unwrap().can_append(keys, msgs, path)
    }

    pub open spec fn branch_append(self, keys: Seq<Key>, msgs: Seq<Message>, path: Path<Summary>) -> Self
        recommends self.can_append(keys, msgs, path)
    {
        AllocationBranch{
            branch: Some(self.branch.unwrap().append(keys, msgs, path)),
            ..self
        }
    }

    pub open spec fn can_split(self, addr: Address, path: Path<Summary>, split_arg: SplitArg) -> bool
    {
        &&& self.branch is Some
        &&& self.mini_allocator.can_allocate(addr)
        &&& self.branch.unwrap().can_split(addr, path, split_arg)
    }

    pub open spec fn branch_split(self, addr: Address, path: Path<Summary>, split_arg: SplitArg) -> Self
        recommends self.can_split(addr, path, split_arg)
    {
        AllocationBranch{
            branch: Some(self.branch.unwrap().split(addr, path, split_arg)),
            mini_allocator: self.mini_allocator.allocate(addr),
        }
    }

    pub open spec fn can_fill(self, aus: Set<AU>) -> bool
    {
        self.mini_allocator.allocs.dom().disjoint(aus)
    }

    pub open spec fn mini_allocator_fill(self, aus: Set<AU>) -> Self 
        recommends self.can_fill(aus)
    {
        AllocationBranch{
            mini_allocator: self.mini_allocator.add_aus(aus),
            ..self
        }
    }

    pub open spec fn can_seal(self, ptr: Pointer, dealloc_aus: Set<AU>) -> bool
    {
        &&& self.branch is Some
        &&& ptr is Some <==> self.branch.unwrap().root() is Index
        &&& ptr is Some ==> self.mini_allocator.can_allocate(ptr.unwrap()) 
                            && !dealloc_aus.contains(ptr.unwrap().au)
        // NOTE: excludes summary node from being allocated from a new AU which is a fair restriction
        &&& self.mini_allocator.removable_aus() == dealloc_aus 
    }

    // seal creates a summary node if the current root is not a leaf,
    // returns any unused AUs and resets the mini allocator to empty
    pub open spec fn branch_seal(self, ptr: Pointer, dealloc_aus: Set<AU>) -> Self
        recommends self.can_seal(ptr, dealloc_aus)
    {
        if ptr is Some {
            let mini_allocator = self.mini_allocator.allocate(ptr.unwrap());
            let reserved_aus = mini_allocator.reserved_aus();
            Self{
                branch: Some(self.branch.unwrap().seal(ptr.unwrap(), reserved_aus)),
                mini_allocator: MiniAllocator::empty(),
            }
        } else {
            Self{
                mini_allocator: MiniAllocator::empty(),
                ..self
            }
        }
    }

    pub open spec fn build_next(pre: Self, post: Self, event: BuildEvent, allocs: Set<AU>, deallocs: Set<AU>) -> bool
    {
        let alloc_checks = 
            if event is AllocFill {
                deallocs.is_empty()
            } else if event is Seal {
                allocs.is_empty()
            } else {
                allocs.is_empty() && deallocs.is_empty()
            };

        alloc_checks && match event {
            BuildEvent::Initialize{addr} => {
                &&& pre.can_initialize(addr)
                &&& pre.branch_initialize(addr) == post
            },
            BuildEvent::Insert{key, msg, path} => {
                &&& pre.can_insert(key, msg, path)
                &&& pre.branch_insert(key, msg, path) == post
                
            },
            BuildEvent::Append{keys, msgs, path} => {
                &&& pre.can_append(keys, msgs, path)
                &&& pre.branch_append(keys, msgs, path) == post
            },
            BuildEvent::Split{addr, path, split_arg} => {
                &&& pre.can_split(addr, path, split_arg)
                &&& pre.branch_split(addr, path, split_arg) == post
            },
            BuildEvent::AllocFill{} => {
                &&& pre.can_fill(allocs)
                &&& pre.mini_allocator_fill(allocs) == post
            },
            BuildEvent::Seal{aux_ptr} => {
                &&& pre.can_seal(aux_ptr, deallocs)
                &&& pre.branch_seal(aux_ptr, deallocs) == post
            },
        }
    }

    pub open spec(checked) fn branch_sealed(self) -> bool 
    {
        &&& self.branch is Some
        &&& self.branch.unwrap().sealed_root()
        &&& self.mini_allocator == MiniAllocator::empty()
    }

    // utility functions 

    pub open spec(checked) fn alloc_aus(branches: Seq<Self>) -> Set<AU>
    {
        let aus = Seq::new(branches.len(), |i:int| branches[i].mini_allocator.all_aus());
        union_seq_of_sets(aus)
    }
} // end of impl AllocationBranch

impl LinkedBranch<Summary> {
    pub open spec fn get_summary(self) -> Summary
        recommends self.has_root() 
    {
        if self.root() is Index {
            self.disk_view.get(self.root()->aux_ptr.unwrap())->0
        } else {
            set![self.root.au]
        }
    }

    pub open spec(checked) fn seal(self, addr: Address, summary: Summary) -> Self
        recommends self.has_root() && self.root() is Index
    {
        let new_aux_node = Node::Auxiliary(summary);
        let new_root_node = Node::Index{
            pivots: self.root()->pivots,
            children: self.root()->children,
            aux_ptr: Some(addr),
        };
        LinkedBranch{
            disk_view: self.disk_view.modify_disk(addr, new_aux_node).modify_disk(self.root, new_root_node),
            ..self
        }
    }

    pub open spec(checked) fn addrs_closed_under_summary(self, summary: Summary) -> bool
        recommends self.acyclic()
    {
        let reachable_addrs = self.reachable_addrs_using_ranking(self.the_ranking());
        &&& forall |addr| #[trigger] reachable_addrs.contains(addr) 
            ==> summary.contains(addr.au)
        &&& self.root() is Index && self.root()->aux_ptr is Some
            ==> summary.contains(self.root()->aux_ptr.unwrap().au)
    }

    pub open spec fn sealed_root(self) -> bool
    {
        &&& self.has_root()
        &&& self.root() is Index ==> {
            &&& self.root()->aux_ptr is Some
            &&& self.disk_view.valid_address(self.root()->aux_ptr.unwrap())
        }
    }

    pub open spec fn valid_sealed_branch(self) -> bool
    {
        &&& self.inv()
        &&& self.sealed_root()
        &&& self.addrs_closed_under_summary(self.get_summary())
    }
} // end of impl LinkedBranch<Summary>

impl AllocationBranch {
    pub open spec fn inv(self) -> bool
    {
        &&& self.mini_allocator.wf()
        &&& self.branch is Some ==> {
            let branch = self.branch.unwrap();
            &&& branch.inv()
            &&& {
                let summary_aus = if self.branch_sealed() { branch.get_summary() } else { self.mini_allocator.reserved_aus() };
                &&& branch.addrs_closed_under_summary(summary_aus)
            }
        }
    }
} // end of impl AllocationBranch 
} // end of verus