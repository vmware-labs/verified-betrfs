// Copyright 2018-2024 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, University of Washington
// SPDX-License-Identifier: BSD-2-Clause
#![allow(unused_imports)]
use builtin::*;

use builtin_macros::*;
use state_machines_macros::state_machine;

use vstd::{prelude::*, seq_lib::*, set_lib::*, map_lib::*, multiset::*};
use crate::spec::KeyType_t::*;
use crate::spec::Messages_t::*;
use crate::disk::GenericDisk_v::*;
use crate::betree::Buffer_v::*;
use crate::betree::LinkedSeq_v::*;
use crate::betree::BufferDisk_v;
use crate::betree::BufferDisk_v::*;
use crate::betree::BufferOffsets_v::*;
use crate::betree::OffsetMap_v::*;
use crate::betree::Memtable_v::*;
use crate::betree::Domain_v::*;
use crate::betree::Utils_v::*;
use crate::betree::PivotTable_v::*;
use crate::betree::SplitRequest_v::*;
use crate::betree::LinkedBetree_v::*;
use crate::betree::LinkedBranch_v;
use crate::betree::LinkedBranch_v::LinkedBranch;
use crate::allocation_layer::Likes_v::*;
use crate::allocation_layer::AllocationBranch_v::*;
use crate::allocation_layer::AllocationBetree_v::*;
use crate::abstract_system::StampedMap_v::*;
use crate::abstract_system::MsgHistory_v::*;

verus! {

impl BufferDisk<BranchNode> {
    pub open spec fn to_branch_disk(self) -> LinkedBranch_v::DiskView::<Summary>
    {
       LinkedBranch_v::DiskView{entries: self.entries}
    }
}

impl LinkedBetree<BranchNode> {
    pub open spec fn get_branch(self, root: Address) -> LinkedBranch<Summary>
    {
        LinkedBranch{root, disk_view: self.buffer_dv.to_branch_disk()}
    }

    pub open spec fn sealed_branch_roots(self, branch_roots: Set<Address>) -> bool
    {
        &&& forall |root| branch_roots.contains(root) 
            ==> #[trigger] self.get_branch(root).valid_sealed_branch()
    }

    pub open spec fn build_branch_summary(self, branch_roots: Set<Address>) -> Map<AU, Set<AU>>
        // decreases branch_roots.len() when branch_roots.finite()
    {
        let root_to_au = Map::new(|addr| branch_roots.contains(addr), |addr: Address| addr.au);
        let au_to_root = root_to_au.invert();
        au_to_root.map_values(|root| self.get_branch(root).get_summary())
        // if branch_roots.len() == 0 {
        //     map!{}
        // } else {
        //     let root = branch_roots.choose();
        //     let sub_branch_summary = self.build_branch_summary(branch_roots.remove(root));
        //     sub_branch_summary.insert(root.au, )
        // }
    }
}   

impl SplitAddrs {
    pub open spec fn to_aus(self) -> Set<AU>
    {
        set!{self.left.au, self.right.au, self.parent.au}
    }

    pub open spec fn addrs_in_disjoint_aus(self) -> bool
    {
        &&& self.left.au != self.right.au
        &&& self.left.au != self.parent.au
        &&& self.right.au != self.parent.au
    }
}

impl TwoAddrs {
    pub open spec fn to_aus(self) -> Set<AU>
    {
        set!{self.addr1.au, self.addr2.au}
    }

    pub open spec fn addrs_in_disjoint_aus(self) -> bool
    {
        self.addr1.au != self.addr2.au
    }
}

pub open spec fn seq_addrs_disjoint_aus(addrs: Seq<Address>) -> bool
{
    forall |i,j| 0<=i<addrs.len() && 0<=j<addrs.len() && i != j
    ==> #[trigger] addrs[i].au != #[trigger] addrs[j].au
}

pub open spec fn set_addrs_disjoint_aus(addrs: Set<Address>) -> bool
{
    forall |addr1, addr2| #[trigger] addrs.contains(addr1) 
        && #[trigger] addrs.contains(addr2) && addr1 != addr2
    ==> addr1.au != addr2.au
}

pub open spec fn map_with_disjoint_values<K,V>(m: Map<K, Set<V>>) -> bool
{
    forall |k1, k2| #[trigger] m.contains_key(k1) 
        && #[trigger] m.contains_key(k2) && k1 != k2
    ==> m[k1].disjoint(m[k2])
}

// injective guarantees that values themselves

impl CompactorInput{
    pub open spec(checked) fn input_roots(inputs: Seq<CompactorInput>) -> Set<Address>
    {
        let roots_seq = Seq::new(inputs.len(), |i| inputs[i].input_buffers.addrs.to_set());
        union_seq_of_sets(roots_seq)
    }
}

// NOTE: inv needs to maintain disjointness between all wip branches

state_machine!{ AllocationBranchBetree {
    fields {
        pub betree: LinkedBetreeVars::State<BranchNode>, 

        pub betree_aus: AULikes,        // tree node reference
        pub branch_aus: AULikes,        // root au of each branch
        pub branch_summary: Map<AU, Summary>,  // map a branch root au to its summary au set

        pub compactors: Seq<CompactorInput>, // track ongoing compaction inputs
        pub wip_branches: Seq<AllocationBranch>, // track ongoing branches that are being built
    }

    pub enum Label
    {
        Label{linked_lbl: LinkedBetreeVars::Label},
        Internal{allocs: Set<AU>, deallocs: Set<AU>}, // internal label
    }    

    pub open spec fn is_fresh(self, aus: Set<AU>) -> bool
    {
        &&& self.betree_aus.dom().disjoint(aus)
        &&& self.summary_aus().disjoint(aus)
        &&& self.branch_allocator_aus().disjoint(aus)
        &&& self.read_ref_aus().disjoint(aus)
    }

    pub open spec fn summary_aus(self) -> Set<AU>
    {
        union_set_of_sets(self.branch_summary.values())
    }

    pub open spec fn branch_allocator_aus(self) -> Set<AU>
    {
        AllocationBranch::alloc_aus(self.wip_branches)
    }

    pub open spec fn read_ref_aus(self) -> Set<AU>
    {
        CompactorInput::input_aus(self.compactors)
    }

    init!{ initialize(betree: LinkedBetreeVars::State<BranchNode>) {
        require LinkedBetreeVars::State::initialize(betree, betree); // buffer_dv restriction: valid_buffer_dv
        let (betree_likes, branch_likes) = betree.linked.transitive_likes();

        require betree.linked.sealed_branch_roots(branch_likes.dom());
        require betree.linked.dv.entries.dom().disjoint(betree.linked.buffer_dv.repr());
        require set_addrs_disjoint_aus(betree_likes.dom() + branch_likes.dom());

        let branch_summary = betree.linked.build_branch_summary(branch_likes.dom());
        require map_with_disjoint_values(branch_summary);

        init betree = betree;
        init betree_aus = to_au_likes(betree_likes);
        init branch_aus = to_au_likes(branch_likes);
        init branch_summary = branch_summary;
        init compactors = Seq::empty();
        init wip_branches = Seq::empty();
    }}

    transition!{ au_likes_noop(lbl: Label, new_betree: LinkedBetreeVars::State<BranchNode>) {
        require lbl is Label;
        require !(lbl->linked_lbl is Internal);
        require LinkedBetreeVars::State::next(pre.betree, new_betree, lbl->linked_lbl);
        update betree = new_betree;
    }}

    transition!{ branch_begin(lbl: Label) {
        require lbl is Internal;
        require pre.is_fresh(lbl->allocs);
        require lbl->deallocs.is_empty();

        let branch = AllocationBranch::new(lbl->allocs);
        update wip_branches = pre.wip_branches.push(branch);
    }}

    // may involve allocation and deallocation
    transition!{ branch_build(lbl: Label, idx: int, post_branch: AllocationBranch, event: BuildEvent) {
        require lbl is Internal;
        require pre.is_fresh(lbl->allocs);
        require 0 <= idx < pre.wip_branches.len();

        require AllocationBranch::build_next(pre.wip_branches[idx], post_branch, event, lbl->allocs, lbl->deallocs);
        update wip_branches = pre.wip_branches.update(idx, post_branch);
    }}

    // abort must return all aus from mini allocator
    transition!{ branch_abort(lbl: Label, idx: int) {
        require lbl is Internal;
        require 0 <= idx < pre.wip_branches.len();
        require lbl->allocs.is_empty();
        require lbl->deallocs == pre.wip_branches[idx].mini_allocator.all_aus();
        update wip_branches = pre.wip_branches.remove(idx);
    }}

    transition!{ internal_flush_memtable(lbl: Label, new_betree: LinkedBetreeVars::State<BranchNode>, branch_idx: int, new_root_addr: Address) {
        require lbl is Internal;
        require pre.is_fresh(lbl->allocs);
        require 0 <= branch_idx < pre.wip_branches.len();
        require pre.wip_branches[branch_idx].branch_sealed();
        
        let new_branch = pre.wip_branches[branch_idx].branch.unwrap();
        let linked_new_addrs = TwoAddrs{addr1: new_root_addr, addr2: new_branch.root};

        require LinkedBetreeVars::State::internal_flush_memtable(pre.betree, new_betree, 
            LinkedBetreeVars::Label::Internal{}, new_branch.root(), new_betree.linked, linked_new_addrs);
    
        let pushed = pre.betree.linked.push_memtable(new_branch.root(), linked_new_addrs);
        let (new_betree_aus, new_branch_aus) = AllocationBetree::State::flush_memtable_au_likes(
                pre.betree, new_betree, linked_new_addrs, pre.betree_aus, pre.branch_aus);
        let new_branch_summary = pre.branch_summary.insert(new_branch.root.au, new_branch.get_summary());

        require lbl->allocs == Set::empty().insert(new_root_addr.au);
        require lbl->deallocs == pre.betree_aus.dom() - new_betree_aus.dom();

        // define the domain
        require restrict_domain_au(pushed.dv.entries, new_betree_aus.dom()) == new_betree.linked.dv.entries.dom();
    
        let full_buffer_dv = pushed.buffer_dv.entries.union_prefer_right(new_branch.disk_view.entries);
        let new_summary_aus = union_set_of_sets(new_branch_summary.values());

        require new_branch.disk_view.entries <= new_betree.linked.buffer_dv.entries;
        require restrict_domain_au(full_buffer_dv, new_summary_aus + pre.read_ref_aus()) == new_betree.linked.buffer_dv.repr();

        update betree = new_betree;
        update betree_aus = new_betree_aus;
        update branch_aus = new_branch_aus;
        update branch_summary = new_branch_summary;
        update wip_branches = pre.wip_branches.remove(branch_idx);
    }}

    transition!{ internal_grow(lbl: Label, new_betree: LinkedBetreeVars::State<BranchNode>, new_root_addr: Address) {
        require lbl is Internal;
        require pre.is_fresh(lbl->allocs);
        require lbl->allocs == Set::empty().insert(new_root_addr.au);
        require lbl->deallocs.is_empty();

        require LinkedBetreeVars::State::internal_grow(pre.betree, new_betree, 
            LinkedBetreeVars::Label::Internal{}, new_root_addr);

        update betree = new_betree;
        update betree_aus = pre.betree_aus.insert(new_root_addr.au);
    }}

    transition!{ internal_split(lbl: Label, new_betree: LinkedBetreeVars::State<BranchNode>, path: Path<BranchNode>, 
        request: SplitRequest, new_addrs: SplitAddrs, path_addrs: PathAddrs) {
        require lbl is Internal;
        require pre.is_fresh(lbl->allocs);
        require new_addrs.addrs_in_disjoint_aus();
        require new_addrs.to_aus().disjoint(seq_addrs_to_aus(path_addrs));
        require seq_addrs_disjoint_aus(path_addrs);

        require LinkedBetreeVars::State::internal_split(pre.betree, new_betree, LinkedBetreeVars::Label::Internal{}, 
            new_betree.linked, path, request, new_addrs, path_addrs);

        let splitted = LinkedBetreeVars::State::post_split(path, request, new_addrs, path_addrs);
        let (new_betree_aus, new_branch_aus) = AllocationBetree::State::internal_split_au_likes(
            path, request, new_addrs, path_addrs, pre.betree_aus, pre.branch_aus);

        require lbl->allocs == new_addrs.to_aus() + seq_addrs_to_aus(path_addrs);
        require lbl->deallocs == pre.betree_aus.dom() - new_betree_aus.dom();

        require restrict_domain_au(splitted.dv.entries, new_betree_aus.dom()) == new_betree.linked.dv.entries.dom();
        require pre.betree.linked.buffer_dv == new_betree.linked.buffer_dv;

        update betree = new_betree;
        update betree_aus = new_betree_aus;
        update branch_aus = new_branch_aus;
    }}
    
    transition!{ internal_flush(lbl: Label, new_betree: LinkedBetreeVars::State<BranchNode>, path: Path<BranchNode>, 
        child_idx: nat, buffer_gc: nat, new_addrs: TwoAddrs, path_addrs: PathAddrs) {
        require lbl is Internal;
        require pre.is_fresh(lbl->allocs);
        require new_addrs.addrs_in_disjoint_aus();
        require new_addrs.to_aus().disjoint(seq_addrs_to_aus(path_addrs));
        require seq_addrs_disjoint_aus(path_addrs);

        require LinkedBetreeVars::State::internal_flush(pre.betree, new_betree, LinkedBetreeVars::Label::Internal{}, 
            new_betree.linked, path, child_idx, buffer_gc, new_addrs, path_addrs);

        let flushed = LinkedBetreeVars::State::post_flush(path, child_idx, buffer_gc, new_addrs, path_addrs);
        let (new_betree_aus, new_branch_aus) = AllocationBetree::State::internal_flush_au_likes(
            path, child_idx, buffer_gc, new_addrs, path_addrs, pre.betree_aus, pre.branch_aus);

        let tree_deallocs_aus = pre.betree_aus.dom() - new_betree_aus.dom();
        let branch_deallocs_aus = pre.branch_aus.dom() - new_branch_aus.dom() - pre.read_ref_aus();
        let new_branch_summary = pre.branch_summary.remove_keys(branch_deallocs_aus);
        let new_summary_aus = union_set_of_sets(new_branch_summary.values());

        let dealloc_branch_summary = pre.branch_summary.restrict(branch_deallocs_aus);
        let summary_deallocs_aus = union_set_of_sets(dealloc_branch_summary.values());

        require lbl->allocs == new_addrs.to_aus() + seq_addrs_to_aus(path_addrs);
        require lbl->deallocs == tree_deallocs_aus + summary_deallocs_aus;

        require restrict_domain_au(flushed.dv.entries, new_betree_aus.dom()) == new_betree.linked.dv.entries.dom();
        require restrict_domain_au(pre.betree.linked.buffer_dv.entries, new_summary_aus + pre.read_ref_aus()) == new_betree.linked.buffer_dv.repr();

        update betree = new_betree;
        update betree_aus = new_betree_aus;
        update branch_aus = new_branch_aus;
        update branch_summary = new_branch_summary;
    }}

    transition!{ internal_compact_begin(lbl: Label, path: Path<BranchNode>, start: nat, end: nat, input: CompactorInput) {
        require lbl is Internal;
        require lbl->allocs.is_empty();
        require lbl->deallocs.is_empty();

        require path.linked == pre.betree.linked;
        require AllocationBetree::State::valid_compactor_input(path, start, end, input);
        update compactors = pre.compactors.push(input);
    }}

    transition!{ internal_compact_abort(lbl: Label, input_idx: int, new_betree: LinkedBetreeVars::State<BranchNode>) {
        require lbl is Internal;
        require 0 <= input_idx < pre.compactors.len();

        let new_compactors = pre.compactors.remove(input_idx);

        let released_read_refs = seq_addrs_to_aus(pre.compactors[input_idx].input_buffers.addrs);
        let dealloc_read_refs = released_read_refs - pre.branch_aus.dom();

        let new_branch_summary = pre.branch_summary.remove_keys(dealloc_read_refs);
        let dealloc_branch_summary = pre.branch_summary.restrict(dealloc_read_refs);
        let new_summary_aus = union_set_of_sets(new_branch_summary.values());

        require lbl->allocs.is_empty();
        require lbl->deallocs == union_set_of_sets(dealloc_branch_summary.values());

        let new_domain = restrict_domain_au(pre.betree.linked.buffer_dv.entries, new_summary_aus + CompactorInput::input_aus(new_compactors));
        let new_buffer_dv = BufferDisk{entries: pre.betree.linked.buffer_dv.entries.restrict(new_domain)};

        require new_betree.memtable == pre.betree.memtable;
        require new_betree == LinkedBetreeVars::State::<BranchNode>{
            linked: LinkedBetree::<BranchNode>{
                buffer_dv: new_buffer_dv,
                ..pre.betree.linked
            },
            ..pre.betree
        };

        update betree = new_betree;
        update branch_summary = new_branch_summary;
        update compactors = new_compactors;
    }}

    // input compact complete 
    transition!{ internal_compact_complete(lbl: Label, input_idx: int, new_betree: LinkedBetreeVars::State<BranchNode>, 
        path: Path<BranchNode>, start: nat, end: nat, branch_idx: int, new_node_addr: Address, path_addrs: PathAddrs) {
        require lbl is Internal;
        require pre.is_fresh(lbl->allocs);
        require !seq_addrs_to_aus(path_addrs).contains(new_node_addr.au);
        require seq_addrs_disjoint_aus(path_addrs);

        require 0 <= input_idx < pre.compactors.len();
        require AllocationBetree::State::valid_compactor_input(path, start, end, pre.compactors[input_idx]);
        require 0 <= branch_idx < pre.wip_branches.len();
        require pre.wip_branches[branch_idx].branch_sealed();

        let new_branch = pre.wip_branches[branch_idx].branch.unwrap();
        let linked_new_addrs = TwoAddrs{addr1: new_node_addr, addr2: new_branch.root};

        require LinkedBetreeVars::State::internal_compact(pre.betree, new_betree, LinkedBetreeVars::Label::Internal{}, 
            new_betree.linked, path, start, end, new_branch.root(), linked_new_addrs, path_addrs);

        let new_compactors = pre.compactors.remove(input_idx);
        let compacted = LinkedBetreeVars::State::post_compact(path, start, end, new_branch.root(), linked_new_addrs, path_addrs);
        let (new_betree_aus, new_branch_aus) = AllocationBetree::State::internal_compact_complete_au_likes(
            path, start, end, linked_new_addrs, path_addrs, pre.betree_aus, pre.branch_aus);

        let tree_deallocs_aus = pre.betree_aus.dom() - new_betree_aus.dom();
        let branch_deallocs_aus = pre.branch_aus.dom() - new_branch_aus.dom() - CompactorInput::input_aus(new_compactors);

        let new_branch_summary = pre.branch_summary.remove_keys(branch_deallocs_aus);
        let new_summary_aus = union_set_of_sets(new_branch_summary.values());

        let dealloc_branch_summary = pre.branch_summary.restrict(branch_deallocs_aus);
        let summary_deallocs_aus = union_set_of_sets(dealloc_branch_summary.values());

        require lbl->allocs == seq_addrs_to_aus(path_addrs).insert(new_node_addr.au);
        require lbl->deallocs == tree_deallocs_aus + summary_deallocs_aus;

        let full_buffer_dv = compacted.buffer_dv.entries.union_prefer_right(new_branch.disk_view.entries);

        require restrict_domain_au(compacted.dv.entries, new_betree_aus.dom()) == new_betree.linked.dv.entries.dom();
        require restrict_domain_au(full_buffer_dv, new_summary_aus + CompactorInput::input_aus(new_compactors)) == new_betree.linked.buffer_dv.repr();

        update betree = new_betree;
        update betree_aus = new_betree_aus;
        update branch_aus = new_branch_aus;
        update branch_summary = new_branch_summary;
        update compactors = new_compactors;
    }}

    pub open spec fn wip_branches_inv(self) -> bool
    {
        forall |i| 0 <= i < self.wip_branches.len()
        ==> #[trigger] self.wip_branches[i].inv()
    }

    #[invariant]
    pub open spec(checked) fn inv(self) -> bool {
        let linked = self.betree.linked;
        let (betree_likes, branch_likes) = linked.transitive_likes();
        let compactor_roots = CompactorInput::input_roots(self.compactors);

        &&& self.betree.inv()
        &&& self.betree_aus == to_au_likes(betree_likes)
        &&& self.branch_aus == to_au_likes(branch_likes)

        // new domain disjointness for AllocationBranchBetree 
        // couldn't prove this at layers above because we pass through
        // the "richer" disk and relaxed disk domain requirement to allow for 
        // garbage collection invisible to upper layers
        &&& linked.dv.entries.dom().disjoint(linked.buffer_dv.repr())

        // branch related invs
        // reachable & compactors are valid sealed branches that do not overlap in AUs
        &&& linked.sealed_branch_roots(branch_likes.dom())
        &&& linked.sealed_branch_roots(compactor_roots)
        &&& set_addrs_disjoint_aus(betree_likes.dom() + branch_likes.dom() + compactor_roots)

        // summary should be disjoint
        &&& self.branch_aus.dom() + self.read_ref_aus() == self.branch_summary.dom()
        &&& map_with_disjoint_values(self.branch_summary) // ensures that summary doesn't overlap
        &&& self.branch_summary == linked.build_branch_summary(branch_likes.dom() + compactor_roots)

        // wip branches must be valid as well
        &&& self.wip_branches_inv()
    }

    #[inductive(initialize)]
    fn initialize_inductive(post: Self, betree: LinkedBetreeVars::State<BranchNode>) {
        let linked = post.betree.linked;
        let (betree_likes, branch_likes) = linked.transitive_likes();
        let compactor_roots = CompactorInput::input_roots(post.compactors);

        assert(betree_likes.dom() + branch_likes.dom() + compactor_roots == betree_likes.dom() + branch_likes.dom());
        assert(set_addrs_disjoint_aus(betree_likes.dom() + branch_likes.dom()));

        assert(post.branch_aus.dom() + post.read_ref_aus() == post.branch_aus.dom());
        assert(post.branch_aus.dom() == to_au_likes(branch_likes).dom());

        let root_to_au = Map::new(|addr| branch_likes.dom().contains(addr), |addr: Address| addr.au);
        assert(root_to_au.dom() == branch_likes.dom());
        let au_to_root = root_to_au.invert();

        to_au_likes_domain(branch_likes);
        assert(to_au_likes(branch_likes).dom() == to_aus(branch_likes.dom()));

        assert(au_to_root.dom() == to_aus(root_to_au.dom()));
        assert(au_to_root.dom() == post.branch_aus.dom());
        assert(post.branch_aus.dom() == post.branch_summary.dom());

        assert(branch_likes.dom() + compactor_roots == branch_likes.dom());
        assert(post.branch_summary == linked.build_branch_summary(branch_likes.dom() + compactor_roots));
    }
   
    #[inductive(au_likes_noop)]
    fn au_likes_noop_inductive(pre: Self, post: Self, lbl: Label, new_betree: LinkedBetreeVars::State<BranchNode>) {
        reveal(LinkedBetreeVars::State::next);
        reveal(LinkedBetreeVars::State::next_by);
        assert(post.inv());
    }
   
    #[inductive(branch_begin)]
    fn branch_begin_inductive(pre: Self, post: Self, lbl: Label) {
        assert(post.inv());
    }
   
    #[inductive(branch_build)]
    fn branch_build_inductive(pre: Self, post: Self, lbl: Label, idx: int, post_branch: AllocationBranch, event: BuildEvent) {
        // build must fail for this 
        assert(post.inv());
    }
   
    #[inductive(branch_abort)]
    fn branch_abort_inductive(pre: Self, post: Self, lbl: Label, idx: int) {
        assert(post.inv());
    }
   
    #[inductive(internal_flush_memtable)]
    fn internal_flush_memtable_inductive(pre: Self, post: Self, lbl: Label, 
        new_betree: LinkedBetreeVars::State<BranchNode>, branch_idx: int, new_root_addr: Address) 
    { 
        
        // only requiring branch sealed
    }
   
    #[inductive(internal_grow)]
    fn internal_grow_inductive(pre: Self, post: Self, lbl: Label, new_betree: LinkedBetreeVars::State<BranchNode>, new_root_addr: Address) { }
   
    #[inductive(internal_split)]
    fn internal_split_inductive(pre: Self, post: Self, lbl: Label, new_betree: LinkedBetreeVars::State<BranchNode>, path: Path<BranchNode>, request: SplitRequest, new_addrs: SplitAddrs, path_addrs: PathAddrs) { }
   
    #[inductive(internal_flush)]
    fn internal_flush_inductive(pre: Self, post: Self, lbl: Label, new_betree: LinkedBetreeVars::State<BranchNode>, path: Path<BranchNode>, child_idx: nat, buffer_gc: nat, new_addrs: TwoAddrs, path_addrs: PathAddrs) { }
   
    #[inductive(internal_compact_begin)]
    fn internal_compact_begin_inductive(pre: Self, post: Self, lbl: Label, path: Path<BranchNode>, start: nat, end: nat, input: CompactorInput) { }
   
    #[inductive(internal_compact_abort)]
    fn internal_compact_abort_inductive(pre: Self, post: Self, lbl: Label, input_idx: int, new_betree: LinkedBetreeVars::State<BranchNode>) { }
   
    #[inductive(internal_compact_complete)]
    fn internal_compact_complete_inductive(pre: Self, post: Self, lbl: Label, input_idx: int, new_betree: LinkedBetreeVars::State<BranchNode>, path: Path<BranchNode>, start: nat, end: nat, branch_idx: int, new_node_addr: Address, path_addrs: PathAddrs) { }
}} // end of AllocationBetree state machine

} // end of verus!