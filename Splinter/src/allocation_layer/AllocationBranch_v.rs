// Copyright 2018-2024 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, University of Washington
// SPDX-License-Identifier: BSD-2-Clause
use builtin::*;

use builtin_macros::*;

use vstd::prelude::*;
use vstd::map::*;

use crate::spec::KeyType_t::*;
use crate::spec::Messages_t::*;
use crate::disk::GenericDisk_v::*;
use crate::betree::Utils_v::*;
use crate::betree::Buffer_v::*;
use crate::betree::BufferDisk_v::*;
use crate::betree::LinkedBranch_v::*;
use crate::betree::LinkedBranch_v::Refinement_v;
use crate::allocation_layer::MiniAllocator_v::*;
use crate::allocation_layer::Likes_v::*;

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
    Initialize{addr: Address, keys: Seq<Key>, msgs: Seq<Message>},
    // Insert{key: Key, msg: Message, path: Path<Summary>},
    Append{keys: Seq<Key>, msgs: Seq<Message>, path: Path<Summary>},
    Split{addr: Address, path: Path<Summary>, split_arg: SplitArg},
    AllocFill{},
    Seal{aux_ptr: Pointer},
}

pub struct AllocationBranch {
    pub sealed: bool,
    pub branch: Option<LinkedBranch<Summary>>,
    pub mini_allocator: MiniAllocator,
}

impl AllocationBranch {
    pub open spec fn new(free_aus: Set<AU>) -> Self {
        AllocationBranch{
            sealed: false,
            branch: None,
            mini_allocator: MiniAllocator::empty().add_aus(free_aus),
        }
    }

    pub open spec fn can_initialize(self, addr: Address, keys: Seq<Key>, msgs: Seq<Message>) -> bool
    {
        &&& !self.sealed
        // can initialize also means that no pages are allocated
        &&& self.mini_allocator.reserved_aus() == Set::<AU>::empty()
        &&& self.mini_allocator.can_allocate(addr)
        &&& keys.len() > 0
        &&& keys.len() == msgs.len()
        &&& Key::is_strictly_sorted(keys)
    }

    pub open spec(checked) fn branch_initialize(self, addr: Address, keys: Seq<Key>, msgs: Seq<Message>) -> Self 
        recommends self.can_initialize(addr, keys, msgs), self.mini_allocator.wf()
    {
        let branch = LinkedBranch{
            root: addr, 
            disk_view: DiskView{entries: map!{addr => Node::Leaf{keys, msgs}}}
        };

        AllocationBranch{
            branch: Some(branch),
            mini_allocator: self.mini_allocator.allocate(addr),
            ..self
        }
    }

    pub open spec fn branch_query(self, key: Key) -> Message
        recommends self.branch is Some
    {
        self.branch.unwrap().query(key)
    }

    pub open spec fn can_append(self, keys: Seq<Key>, msgs: Seq<Message>, path: Path<Summary>) -> bool
    {
        &&& !self.sealed
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
        &&& !self.sealed
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
            ..self
        }
    }

    pub open spec fn can_fill(self, aus: Set<AU>) -> bool
    {
        &&& !self.sealed
        &&& self.mini_allocator.allocs.dom().disjoint(aus)
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
        &&& !self.sealed
        &&& self.branch is Some
        &&& ptr is Some <==> self.branch.unwrap().root() is Index
        &&& ptr is Some ==> {
            &&& self.mini_allocator.can_allocate(ptr.unwrap())
            &&& !dealloc_aus.contains(ptr.unwrap().au)
        }
        // NOTE: excludes summary node from being allocated from a new AU which is a fair restriction
        &&& self.mini_allocator.removable_aus() == dealloc_aus 
    }

    // seal creates a summary node if the current root is not a leaf
    // returns any unused AUs and resets the mini allocator to empty
    pub open spec fn branch_seal(self, ptr: Pointer, dealloc_aus: Set<AU>) -> Self
        recommends self.can_seal(ptr, dealloc_aus)
    {
        if ptr is Some {
            let mini_allocator = self.mini_allocator.allocate(ptr.unwrap());
            let reserved_aus = self.mini_allocator.reserved_aus();
            Self{                
                sealed: true,
                branch: Some(self.branch.unwrap().seal(ptr.unwrap(), reserved_aus)),
                mini_allocator: mini_allocator.prune(dealloc_aus),
            }
        } else {
            Self{
                sealed: true,
                mini_allocator: self.mini_allocator.prune(dealloc_aus),
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
            BuildEvent::Initialize{addr, keys, msgs} => {
                &&& pre.can_initialize(addr, keys, msgs)
                &&& pre.branch_initialize(addr, keys, msgs) == post
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
        self.sealed
    }

    // utility functions 

    pub open spec(checked) fn alloc_aus(branches: Seq<Self>) -> Set<AU>
    {
        let aus = Seq::new(branches.len(), |i:int| branches[i].mini_allocator.all_aus());
        union_seq_of_sets(aus)
    }

    pub open spec(checked) fn addrs_closed_under_mini_allocator(self) -> bool
        recommends self.branch is Some
    {
        forall |addr| #[trigger] self.branch.unwrap().disk_view.entries.contains_key(addr)
            <==> self.mini_allocator.page_is_reserved(addr)
    }

    pub proof fn alloc_aus_singleton(self) 
        ensures Self::alloc_aus(seq![self]) == self.mini_allocator.all_aus()
    {
        let aus = Seq::new(seq![self].len(), |i:int| seq![self][i].mini_allocator.all_aus());
        assert(union_seq_of_sets(aus.drop_last()) == Set::<AU>::empty());
        assert(union_seq_of_sets(aus) == union_seq_of_sets(aus.drop_last()).union(aus.last()));
        assert(union_seq_of_sets(aus) == aus.last());
        assert(aus.last() == self.mini_allocator.all_aus());
    }

    pub proof fn alloc_aus_append(branches: Seq<Self>, append: Self) 
        ensures Self::alloc_aus(branches.push(append)) == 
            Self::alloc_aus(branches) + Self::alloc_aus(seq![append])
    {
        let total_branches = branches.push(append);
        let total_aus = Seq::new(total_branches.len(), |i:int| total_branches[i].mini_allocator.all_aus());
        let branches_aus = Seq::new(branches.len(), |i:int| branches[i].mini_allocator.all_aus());

        assert(union_seq_of_sets(total_aus) == union_seq_of_sets(total_aus.drop_last()).union(total_aus.last()));
        assert(total_aus.drop_last() == branches_aus);
        append.alloc_aus_singleton();
    }

    pub proof fn alloc_aus_remove(branches: Seq<Self>, idx: int) 
        requires 
            0 <= idx < branches.len(),
        ensures 
            Self::alloc_aus(branches.remove(idx)) + branches[idx].mini_allocator.all_aus() == Self::alloc_aus(branches) 
        decreases branches.len()
    {
        if idx == branches.len() - 1 {
            Self::alloc_aus_append(branches.drop_last(), branches.last());
            assert(branches.drop_last().push(branches.last()) == branches); // trigger
            Self::alloc_aus_singleton(branches[idx]);
        } else {
            Self::alloc_aus_remove(branches.drop_last(), idx);
            assert(Self::alloc_aus(branches.drop_last().remove(idx)) + branches[idx].mini_allocator.all_aus() 
                == Self::alloc_aus(branches.drop_last()));
            assert(branches.drop_last().remove(idx) == branches.remove(idx).drop_last());

            Self::alloc_aus_append(branches.remove(idx).drop_last(), branches.last());
            Self::alloc_aus_append(branches.drop_last(), branches.last());

            assert(branches.drop_last().push(branches.last()) == branches); // trigger
            assert(branches.remove(idx).drop_last().push(branches.last()) == branches.remove(idx)); // trigger
            assert(Self::alloc_aus(branches.remove(idx)) + branches[idx].mini_allocator.all_aus() == Self::alloc_aus(branches));
        }
    }

    pub proof fn alloc_aus_update(branches: Seq<Self>, idx: int, update: Self)
        requires 
            0 <= idx < branches.len(),
            branches[idx].mini_allocator.all_aus() <= update.mini_allocator.all_aus(),
        ensures 
            Self::alloc_aus(branches.update(idx, update))
            == Self::alloc_aus(branches) + (update.mini_allocator.all_aus() - branches[idx].mini_allocator.all_aus()),
        decreases branches.len()
    {
        if idx == branches.len() - 1 {
            let updated = branches.update(idx, update);

            Self::alloc_aus_append(branches.drop_last(), branches.last());
            Self::alloc_aus_append(updated.drop_last(), updated.last());

            assert(branches.drop_last().push(branches.last()) == branches); // trigger
            assert(updated.drop_last().push(updated.last()) == updated); // trigger

            branches.last().alloc_aus_singleton();
            updated.last().alloc_aus_singleton();

            assert(updated.drop_last() == branches.drop_last());
            assert(update == updated.last());

            assert(Self::alloc_aus(updated) == Self::alloc_aus(branches.drop_last()) + update.mini_allocator.all_aus());
            assert(Self::alloc_aus(updated) == Self::alloc_aus(branches)
                + (update.mini_allocator.all_aus() - branches[idx].mini_allocator.all_aus()));
        } else {
            Self::alloc_aus_update(branches.drop_last(), idx, update);
            assert(branches.drop_last().update(idx, update) == branches.update(idx, update).drop_last());
                
            Self::alloc_aus_append(branches.update(idx, update).drop_last(), branches.last());
            Self::alloc_aus_append(branches.drop_last(), branches.last());

            assert(branches.drop_last().push(branches.last()) == branches); // trigger
            assert(branches.update(idx, update).drop_last().push(branches.last()) == branches.update(idx, update)); // trigger

            assert(Self::alloc_aus(branches.update(idx, update)) == Self::alloc_aus(branches.drop_last()) + 
                (update.mini_allocator.all_aus() - branches[idx].mini_allocator.all_aus()) + Self::alloc_aus(seq![branches.last()]));
            assert(Self::alloc_aus(branches.update(idx, update)) == Self::alloc_aus(branches) +
                (update.mini_allocator.all_aus() - branches[idx].mini_allocator.all_aus()));
        }
    }

    pub broadcast proof fn alloc_aus_ensures(branches: Seq<Self>, i: int) 
        requires 0 <= i < branches.len()
        ensures #[trigger] branches[i].mini_allocator.all_aus() <= Self::alloc_aus(branches)
    {
        let aus = Seq::new(branches.len(), |i:int| branches[i].mini_allocator.all_aus());

        assert forall |au| #[trigger] branches[i].mini_allocator.all_aus().contains(au)
        implies Self::alloc_aus(branches).contains(au)
        by {
            assert(0 <= i < aus.len());
            assert(aus[i].contains(au));  // trigger
            lemma_set_subset_of_union_seq_of_sets(aus, au);
        }
    }

    pub proof fn alloc_aus_contains(branches: Seq<Self>, au: AU) -> (i: int)
        requires Self::alloc_aus(branches).contains(au) 
        ensures 0 <= i < branches.len() && branches[i].mini_allocator.all_aus().contains(au)
    {
        let aus = Seq::new(branches.len(), |i:int| branches[i].mini_allocator.all_aus());
        lemma_union_seq_of_sets_contains(aus, au);
        let i = choose |i| 0 <= i < aus.len() && #[trigger] aus[i].contains(au);
        i
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

    pub open spec fn sealed_root(self) -> bool
    {
        &&& self.has_root()
        &&& self.root() is Index ==> {
            &&& self.root()->aux_ptr is Some
            &&& self.disk_view.valid_address(self.root()->aux_ptr.unwrap())
            &&& self.disk_view.entries[self.root()->aux_ptr.unwrap()] is Auxiliary
        }
    }

    pub open spec fn full_repr(self) -> Set<Address>
    {
        if self.root() is Index {
            self.representation() + set!{self.root()->aux_ptr.unwrap()}
        } else {
            self.representation()
        }
    }

    pub open spec fn tight_disk_view_with_summary(self) -> bool
    {
        self.disk_view.representation() == self.full_repr()
    }

    pub open spec fn valid_sealed_branch(self) -> bool
    {
        &&& self.inv()
        &&& self.sealed_root()

        &&& addrs_closed(self.full_repr(), self.get_summary())
        &&& restrict_domain_au(self.disk_view.entries, self.get_summary()) =~= self.full_repr()
    }
} // end of impl LinkedBranch<Summary>

impl AllocationBranch {
    pub open spec fn inv(self) -> bool
    {
        &&& self.mini_allocator.wf()
        &&& self.sealed ==> self.branch is Some
        &&& self.branch is Some ==> {
            let branch = self.branch.unwrap();
            &&& self.sealed ==> {
                &&& branch.valid_sealed_branch()
                &&& branch.tight_disk_view_with_summary()
                &&& branch.get_summary() == self.mini_allocator.all_aus()
            }
            &&& !self.sealed ==> {
                &&& branch.inv()
                &&& self.addrs_closed_under_mini_allocator()
                &&& branch.tight_disk_view()
            }
        }
    }

    pub proof fn build_next_preserves_inv(pre: Self, post: Self, event: BuildEvent, allocs: Set<AU>, deallocs: Set<AU>)
        requires 
            pre.inv(), 
            Self::build_next(pre, post, event, allocs, deallocs), 
        ensures 
            post.inv(), 
    {
        match event {
            BuildEvent::Initialize{addr, keys, msgs} => {
                let branch = post.branch.unwrap();
                assert(branch.valid_ranking(map!{addr => 1nat}));
                assert(branch.disk_view.entries.dom() =~= set!{addr});
                assert(post.mini_allocator.page_is_reserved(addr)); // trigger

                assert forall |address| #[trigger] post.mini_allocator.page_is_reserved(address)
                implies branch.disk_view.entries.contains_key(address)
                by {
                    if address != addr {
                        assert(pre.mini_allocator.reserved_aus().contains(address.au));
                        assert(false);
                    }
                }
                assert(post.inv());
            },
            BuildEvent::Append{keys, msgs, path} => {
                let pre_branch = pre.branch.unwrap();
                let post_branch = post.branch.unwrap();

                Refinement_v::append_refines(pre_branch, keys, msgs, path);
                assert(post.inv());
            },
            BuildEvent::Split{addr, path, split_arg} => {
                let pre_branch = pre.branch.unwrap();
                let post_branch = post.branch.unwrap();

                Refinement_v::split_refines(pre_branch, addr, path, split_arg);
                assert(post.mini_allocator.allocs[addr.au].reserved.contains(addr)); // trigger
                assert(post.mini_allocator.reserved_aus().contains(addr.au));
                assert(pre.mini_allocator.reserved_aus() <= post.mini_allocator.reserved_aus());   
                assert(post.inv());
            },
            BuildEvent::AllocFill{} => {
                assert(post.inv());
            },
            BuildEvent::Seal{aux_ptr} => {
                let pre_branch = pre.branch.unwrap();
                let post_branch = post.branch.unwrap();
                pre.branch_seal_preserves_inv(aux_ptr, deallocs);
                assert(post.inv());
            },
        }
    }

    pub proof fn branch_seal_preserves_inv(self, aux_ptr: Pointer, deallocs: Set<AU>)
        requires self.inv(), self.can_seal(aux_ptr, deallocs), 
        ensures self.branch_seal(aux_ptr, deallocs).inv()
    {
        let branch = self.branch.unwrap();
        let post = self.branch_seal(aux_ptr, deallocs);
        let post_branch = post.branch.unwrap();

        if aux_ptr is None {
            assert forall |au| self.mini_allocator.reserved_aus().contains(au) 
            implies au == branch.root.au
            by {
                if au != branch.root.au {
                    let addr = self.mini_allocator.allocs[au].reserved.choose();
                    if (self.mini_allocator.allocs[au].reserved.finite()) {
                        if self.mini_allocator.allocs[au].reserved.len() == 0 {
                            self.mini_allocator.allocs[au].reserved.lemma_len0_is_empty();
                            assert(false);
                        }
                    }
                    assert(self.mini_allocator.allocs[au].reserved.contains(addr)); // trigger
                    assert(branch.disk_view.entries.contains_key(addr));
                    assert(false);
                }
            }
            assert(branch.get_summary() == set!{branch.root.au});
            assert(post.mini_allocator.all_aus() == self.mini_allocator.reserved_aus());
            assert(branch.get_summary() =~= post.mini_allocator.all_aus());
            assert(post.inv());
            return;
        }

        let reserved_aus = self.mini_allocator.reserved_aus();
        let except = set!{branch.root} + set!{aux_ptr.unwrap()};

        assert(post_branch == branch.seal(aux_ptr.unwrap(), reserved_aus));
        assert(branch.disk_view.entries.remove_keys(except) =~= post_branch.disk_view.entries.remove_keys(except));
        assert(post_branch.disk_view.same_except(branch.disk_view, except));

        assert(forall |i| #[trigger] post_branch.root().valid_child_index(i) 
            ==> branch.root().valid_child_index(i)); // trigger

        let ranking = branch.the_ranking();
        assert(post_branch.acyclic()) by {
            assert(post_branch.disk_view.node_children_respects_rank(ranking, branch.root));
            assert(post_branch.valid_ranking(ranking));
        }

        let post_ranking = post_branch.the_ranking();
        let post_i = post_branch.i_internal(post_ranking);
        let pre_i = branch.i_internal(ranking);

        Refinement_v::i_internal_wf(branch, ranking);
        assert(pre_i.wf());

        assert forall |i| 0 <= i < post_i->children.len()
        implies ({
            &&& #[trigger] branch.root().valid_child_index(i)
            &&& post_i->children[i] == pre_i->children[i]
            &&& branch.child_at_idx(i).reachable_addrs_using_ranking(ranking)
                == post_branch.child_at_idx(i).reachable_addrs_using_ranking(post_ranking)
        }) by {
            assert(branch.root().valid_child_index(i));
            assert(post_branch.root().valid_child_index(i));

            let pre_child = branch.child_at_idx(i);
            let post_child = post_branch.child_at_idx(i);

            assert(pre_child.reachable_addrs_using_ranking(ranking).disjoint(except)) by {
                if pre_child.reachable_addrs_using_ranking(ranking).contains(branch.root) {
                    Refinement_v::lemma_reachable_child_has_smaller_rank(pre_child, ranking, branch.root);
                }
                if pre_child.reachable_addrs_using_ranking(ranking).contains(aux_ptr.unwrap()) {
                    Refinement_v::lemma_reachable_implies_valid_address(pre_child, ranking, aux_ptr.unwrap());
                }
            }
            Refinement_v::lemma_reachable_unchanged_implies_same_i_internal(
                pre_child, ranking, post_child, post_ranking, except);
        }
        assert(post_i->children =~= pre_i->children);
        assert(post_i.wf());
        Refinement_v::lemma_i_wf_implies_inv(post_branch, post_ranking);
        assert(post_branch.inv_internal(post_ranking));

        assert(post_branch.representation() =~= branch.representation()) 
        by {
            let subtree_addrs = branch.children_reachable_addrs_using_ranking(ranking);
            let post_subtree_addrs = post_branch.children_reachable_addrs_using_ranking(post_ranking);
            assert(subtree_addrs =~= post_subtree_addrs);
        }

        assert(post_branch.get_summary() =~= post.mini_allocator.all_aus());
        assert(post_branch.disk_view.entries.dom() =~= branch.disk_view.entries.dom() + set!{aux_ptr.unwrap()}); // trigger
        assert(post.inv());
    }
} // end of impl AllocationBranch 
} // end of verus