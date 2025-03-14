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
use crate::betree::LinkedBranch_v::Refinement_v;
use crate::allocation_layer::Likes_v::*;
use crate::allocation_layer::LikesBetree_v::*;
use crate::allocation_layer::AllocationBranch_v::*;
use crate::allocation_layer::AllocationBetree_v::*;
use crate::abstract_system::StampedMap_v::*;
use crate::abstract_system::MsgHistory_v::*;

verus! {

// broadcast use to_aus_contains;

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
            ==> (#[trigger] self.get_branch(root)).valid_sealed_branch()
    }

    pub open spec fn build_branch_summary(self, branch_roots: Set<Address>) -> Map<AU, Set<AU>>
    {
        let root_to_au = Map::new(|addr| branch_roots.contains(addr), |addr: Address| addr.au);
        let au_to_root = root_to_au.invert();
        au_to_root.map_values(|root| self.get_branch(root).get_summary())
    }

    pub proof fn build_branch_summary_finite(self, branch_roots: Set<Address>) 
        requires branch_roots.finite()
        ensures self.build_branch_summary(branch_roots).dom().finite(),
    {
        let root_to_au = Map::new(|addr| branch_roots.contains(addr), |addr: Address| addr.au);
        assert(root_to_au.dom() =~= branch_roots);
        assert(root_to_au.dom().finite());
        lemma_values_finite(root_to_au);
        assert(root_to_au.values().finite());

        let au_to_root = root_to_au.invert();
        assert(au_to_root.dom().finite());
        let result = self.build_branch_summary(branch_roots);
        assert(result.dom() =~= au_to_root.dom());
    }

    pub proof fn build_branch_summary_contains(self, branch_roots: Set<Address>, root: Address) 
        requires 
            branch_roots.contains(root),
            set_addrs_disjoint_aus(branch_roots),
        ensures 
            self.build_branch_summary(branch_roots).contains_key(root.au),
            self.build_branch_summary(branch_roots)[root.au]
            == self.get_branch(root).get_summary()
    {
        let root_to_au = Map::new(|addr| branch_roots.contains(addr), |addr: Address| addr.au);
        assert(root_to_au.dom() =~= branch_roots);
        assert(root_to_au.contains_pair(root, root.au)); // witness
    }

    pub proof fn build_branch_summary_get_addr(self, branch_roots: Set<Address>, au: AU) -> (addr: Address)
        requires 
            set_addrs_disjoint_aus(branch_roots),
            self.build_branch_summary(branch_roots).contains_key(au),
        ensures 
            addr.au == au,
            branch_roots.contains(addr),
            self.build_branch_summary(branch_roots)[au] == self.get_branch(addr).get_summary()
    {
        let addr = choose |addr| #[trigger] branch_roots.contains(addr) && addr.au == au;
        let root_to_au = Map::new(|addr| branch_roots.contains(addr), |addr: Address| addr.au);
        assert(root_to_au.contains_pair(addr, addr.au)); // witness
        addr
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

pub open spec fn set_addrs_disjoint_aus(addrs: Set<Address>) -> bool
{
    forall |a,b| addrs.contains(a) && addrs.contains(b) && a != b
    ==> #[trigger] a.au != #[trigger] b.au
}

pub open spec fn seq_addrs_disjoint_aus(addrs: Seq<Address>) -> bool
{
    forall |i,j| 0<=i<addrs.len() && 0<=j<addrs.len() && i != j
    ==> #[trigger] addrs[i].au != #[trigger] addrs[j].au
}

pub open spec fn map_with_disjoint_values<K,V>(m: Map<K, Set<V>>) -> bool
{
    forall |k1, k2| #[trigger] m.contains_key(k1) 
        && #[trigger] m.contains_key(k2) && k1 != k2
    ==> m[k1].disjoint(m[k2])
}

pub open spec fn map_with_finite_values<K,V>(m: Map<K, Set<V>>) -> bool
{
    forall |k| #[trigger] m.contains_key(k) ==> m[k].finite()
}

// injective guarantees that values themselves

impl CompactorInput{
    pub open spec(checked) fn input_roots(inputs: Seq<CompactorInput>) -> Set<Address>
    {
        let roots_seq = Seq::new(inputs.len(), |i| inputs[i].input_buffers.addrs.to_set());
        union_seq_of_sets(roots_seq)
    }

    pub proof fn input_roots_finite(inputs: Seq<CompactorInput>)
        ensures Self::input_roots(inputs).finite()
    {
        let roots_seq = Seq::new(inputs.len(), |i| inputs[i].input_buffers.addrs.to_set());
        lemma_union_seq_of_sets_finite(roots_seq);
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
        require LinkedBetreeVars::State::initialize(betree, betree);
        let (betree_likes, branch_likes) = betree.linked.transitive_likes();

        require betree.linked.sealed_branch_roots(branch_likes.dom());

        let branch_summary = betree.linked.build_branch_summary(branch_likes.dom());
        require set_addrs_disjoint_aus(branch_likes.dom());
        require map_with_disjoint_values(branch_summary);

        let betree_aus = to_au_likes(betree_likes);
        let summary_aus = union_set_of_sets(branch_summary.values());

        require addrs_closed(betree.linked.dv.entries.dom(), betree_aus.dom());
        require addrs_closed(betree.linked.buffer_dv.entries.dom(), summary_aus);
        require betree_aus.dom().disjoint(summary_aus);

        init betree = betree;
        init betree_aus = betree_aus;
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

        // define the domain removing old betree root
        require new_betree.linked.dv.entries.dom() == restrict_domain_au(pushed.dv.entries, new_betree_aus.dom());
        require new_betree.linked.buffer_dv.entries == pre.betree.linked.buffer_dv.entries.union_prefer_right(new_branch.disk_view.entries);

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
        ==> (#[trigger] self.wip_branches[i]).inv()
    }

    pub open spec fn wip_branches_disjoint(self) -> bool
    {
        forall |i, j| 0 <= i < self.wip_branches.len() && 
            0 <= j < self.wip_branches.len() && i != j
        ==> (#[trigger] self.wip_branches[i]).mini_allocator.all_aus().disjoint(
            (#[trigger]self.wip_branches[j]).mini_allocator.all_aus())
    }

    #[invariant]
    pub open spec(checked) fn inv(self) -> bool {
        let linked = self.betree.linked;
        let (betree_likes, branch_likes) = linked.transitive_likes();
        let compactor_roots = CompactorInput::input_roots(self.compactors);

        &&& self.betree.inv()
        &&& self.betree_aus == to_au_likes(betree_likes)
        &&& self.branch_aus == to_au_likes(branch_likes)

        // added branch inv
        &&& linked.sealed_branch_roots(branch_likes.dom() + compactor_roots)

        // summary should be disjoint
        &&& set_addrs_disjoint_aus(branch_likes.dom() + compactor_roots)
        &&& map_with_disjoint_values(self.branch_summary)
        // &&& map_with_finite_values(self.branch_summary)
        &&& self.branch_summary == linked.build_branch_summary(branch_likes.dom() + compactor_roots)

        // new domain disjointness for AllocationBranchBetree 
        // couldn't prove this at layers above because we pass through
        // the "richer" disk and relaxed disk domain requirement to allow for 
        // garbage collection invisible to upper layers
        &&& addrs_closed(linked.dv.entries.dom(), self.betree_aus.dom())
        &&& addrs_closed(linked.buffer_dv.entries.dom(), self.summary_aus())

        &&& self.betree_aus.dom().disjoint(self.summary_aus())
        &&& self.betree_aus.dom().disjoint(self.branch_allocator_aus())
        &&& self.summary_aus().disjoint(self.branch_allocator_aus())
        // &&& self.branch_aus.dom() + self.read_ref_aus() == self.branch_summary.dom() // derive from^

        &&& self.wip_branches_inv()
        &&& self.wip_branches_disjoint()
    }

    #[inductive(initialize)]
    fn initialize_inductive(post: Self, betree: LinkedBetreeVars::State<BranchNode>) {
        let linked = post.betree.linked;
        let (betree_likes, branch_likes) = linked.transitive_likes();
        let compactor_roots = CompactorInput::input_roots(post.compactors);

        assert(betree_likes.dom() + branch_likes.dom() + compactor_roots == betree_likes.dom() + branch_likes.dom());
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
        assert(post.betree_aus.dom() == pre.betree_aus.dom());

        AllocationBranch::alloc_aus_append(pre.wip_branches, post.wip_branches.last());
        post.wip_branches.last().alloc_aus_singleton();
        assert(post.branch_allocator_aus() == pre.branch_allocator_aus() + lbl->allocs);

        broadcast use AllocationBranch::alloc_aus_ensures;
        assert(post.inv());
    }
   
    #[inductive(branch_build)]
    fn branch_build_inductive(pre: Self, post: Self, lbl: Label, idx: int, post_branch: AllocationBranch, event: BuildEvent) {
        AllocationBranch::build_next_preserves_inv(pre.wip_branches[idx], post_branch, event, lbl->allocs, lbl->deallocs);
        broadcast use AllocationBranch::alloc_aus_ensures;

        match event {
            BuildEvent::AllocFill{} => {
                assert(post_branch.mini_allocator.all_aus() - lbl->allocs == pre.wip_branches[idx].mini_allocator.all_aus());
                AllocationBranch::alloc_aus_update(pre.wip_branches, idx, post_branch);
                assert(pre.branch_allocator_aus() + lbl->allocs =~= post.branch_allocator_aus());
                assert(post.wip_branches_disjoint());
            }
            BuildEvent::Seal{aux_ptr} => {
                assert(pre.wip_branches[idx].mini_allocator.all_aus() - lbl->deallocs == post_branch.mini_allocator.all_aus());
                AllocationBranch::alloc_aus_update(post.wip_branches, idx, pre.wip_branches[idx]);
                assert(post.wip_branches.update(idx, pre.wip_branches[idx]) == pre.wip_branches); // trigger
                assert(pre.branch_allocator_aus() =~= post.branch_allocator_aus() + lbl->deallocs);

                assert(forall |i|  0 <= i < post.wip_branches.len() ==> 
                    #[trigger] post.wip_branches[i].mini_allocator.all_aus() 
                    <= pre.wip_branches[i].mini_allocator.all_aus());
                assert(post.wip_branches_disjoint());
            }
            _ => {
                assert(pre.wip_branches[idx].mini_allocator.all_aus() == post_branch.mini_allocator.all_aus());
                AllocationBranch::alloc_aus_update(pre.wip_branches, idx, post_branch);
                assert(pre.branch_allocator_aus() =~= post.branch_allocator_aus());
                assert(post.wip_branches_disjoint());
            }
        }
        assert(post.inv());
    }
   
    #[inductive(branch_abort)]
    fn branch_abort_inductive(pre: Self, post: Self, lbl: Label, idx: int) {
        AllocationBranch::alloc_aus_remove(pre.wip_branches, idx);
        assert(post.inv());
    }
   
    #[inductive(internal_flush_memtable)]
    fn internal_flush_memtable_inductive(pre: Self, post: Self, lbl: Label, 
        new_betree: LinkedBetreeVars::State<BranchNode>, branch_idx: int, new_root_addr: Address) 
    { 
        let new_branch = pre.wip_branches[branch_idx].branch.unwrap();
        let linked_new_addrs = TwoAddrs{addr1: new_root_addr, addr2: new_branch.root};
        let pushed = pre.betree.linked.push_memtable(new_branch.root(), linked_new_addrs);

        let (pushed_betree_likes, pushed_buffer_likes) = pushed.transitive_likes();
        let (post_betree_likes, post_branch_likes) = post.betree.linked.transitive_likes();

        assert(new_branch.representation().contains(new_branch.root));
        AllocationBranch::alloc_aus_ensures(pre.wip_branches, branch_idx);

        pre.betree.internal_flush_memtable_aus_ensures(post.betree, new_branch.root(), linked_new_addrs);    
        pushed.valid_view_ensures(new_betree.linked);
        pushed.valid_view_implies_same_transitive_likes(new_betree.linked);
        assert(new_betree.inv());

        let compactor_roots = CompactorInput::input_roots(pre.compactors);
        let (pre_betree_likes, pre_branch_likes) = pre.betree.linked.transitive_likes();
        LikesBetree::State::push_memtable_likes_ensures(pre.betree, new_betree, new_branch.root(), linked_new_addrs);
        assert(post_branch_likes.dom() =~= pre_branch_likes.dom() + set!{new_branch.root});

        let new_branch_dv = post.betree.linked.buffer_dv.to_branch_disk();
        let branch_dv = pre.betree.linked.buffer_dv.to_branch_disk();

        // TODO: extract into a separate proof
        assert(branch_dv.wf()) by {
            CompactorInput::input_roots_finite(pre.compactors);
            assert(compactor_roots.finite());
            assert(pre_branch_likes.dom().finite());

            if compactor_roots.is_empty() && pre_branch_likes.dom().is_empty() {
                assert(pre.branch_summary.values() =~= Set::<Set<AU>>::empty());
                assert(pre.summary_aus() =~= Set::<AU>::empty());
                assert(branch_dv.entries.dom() =~= Set::<Address>::empty());
                assert(branch_dv.wf());
            } else {
                if compactor_roots.is_empty() {
                    compactor_roots.lemma_len0_is_empty();
                    assert(!pre_branch_likes.dom().is_empty());
                    assert(exists |root| pre_branch_likes.dom().contains(root));
                    let root = choose |root| pre_branch_likes.dom().contains(root);
                    assert(pre.betree.linked.get_branch(root).inv());
                } else {
                    assert(exists |root| compactor_roots.contains(root));
                    let root = choose |root| compactor_roots.contains(root);
                    assert(pre.betree.linked.get_branch(root).inv());
                }
            }
        }
        assert(new_branch_dv.wf());

        let pre_branch_roots =  pre_branch_likes.dom() + compactor_roots;
        let post_branch_roots = post_branch_likes.dom() + compactor_roots;

        assert forall |root| post_branch_roots.contains(root) 
        implies (#[trigger] post.betree.linked.get_branch(root)).valid_sealed_branch()
        by {
            let pre_branch = if root == new_branch.root { new_branch } else { pre.betree.linked.get_branch(root) };
            let other_branch =  if root == new_branch.root { pre.betree.linked.get_branch(root) } else { new_branch };
            let post_branch = post.betree.linked.get_branch(root);

            assert(pre_branch.valid_sealed_branch());
            assert(post_branch.acyclic()) by {
                let _ = pre_branch.valid_ranking_big_disk(post_branch);
            }
            assert(post_branch.inv()) by {
                pre_branch.subdisk_same_i_internal(pre_branch.the_ranking(), post_branch, post_branch.the_ranking());
                Refinement_v::i_internal_wf(pre_branch, pre_branch.the_ranking());
                Refinement_v::lemma_i_wf_implies_inv(post_branch,  post_branch.the_ranking());
            }
            assert(post_branch.representation() == pre_branch.representation()) by {
                Refinement_v::lemma_reachable_addrs_subset(pre_branch, pre_branch.the_ranking());
                assert(pre_branch.representation() <= pre_branch.disk_view.entries.dom());
                assert(pre_branch.disk_view.entries.remove_keys(other_branch.disk_view.entries.dom())
                =~= post_branch.disk_view.entries.remove_keys(other_branch.disk_view.entries.dom())); // trigger
                Refinement_v::lemma_reachable_unchanged_implies_same_i_internal(pre_branch, pre_branch.the_ranking(), 
                    post_branch, post_branch.the_ranking(), other_branch.disk_view.entries.dom());
            }
            assert(post_branch.valid_sealed_branch());
        }

        CompactorInput::input_roots_finite(pre.compactors);
        pre.betree.linked.build_branch_summary_finite(pre_branch_roots);
        if pre.branch_summary.contains_key(new_branch.root.au) {
            let addr = pre.betree.linked.build_branch_summary_get_addr(pre_branch_roots, new_branch.root.au);
            assert(pre.betree.linked.get_branch(addr).valid_sealed_branch()); // trigger
            assert(false);
        }
        branch_summary_insert_ensures(pre.branch_summary, new_branch);

        to_au_likes_singleton(new_root_addr);
        assert(post.betree_aus.dom() <= pre.betree_aus.dom() + set!{ new_root_addr.au });

        assert(post.betree_aus.dom().disjoint(post.summary_aus())) by {
            assert(pre.summary_aus().disjoint(set!{new_root_addr.au}));
            assert(new_branch.get_summary().disjoint(set!{new_root_addr.au}));
        }

        AllocationBranch::alloc_aus_remove(pre.wip_branches, branch_idx);
        assert(post.branch_allocator_aus() + new_branch.get_summary() == pre.branch_allocator_aus());
        assert forall |au| post.branch_allocator_aus().contains(au) 
        implies !new_branch.get_summary().contains(au)
        by {
            let i = AllocationBranch::alloc_aus_contains(post.wip_branches, au);
            let pre_idx = if i < branch_idx { i } else { i + 1 };
            assert(pre.wip_branches[pre_idx].mini_allocator.all_aus().contains(au));
        }

        assert(pre_branch_roots + set!{new_branch.root} =~= post_branch_roots); // trigger
        assert forall |addr| pre_branch_roots.contains(addr)
        implies addr.au != new_branch.root.au
        by {
            assert(pre.betree.linked.get_branch(addr).valid_sealed_branch()); // trigger
            assert(pre.betree.linked.buffer_dv.entries.contains_key(addr));
        }
        assert(set_addrs_disjoint_aus(post_branch_roots));
        pre.betree.linked.build_branch_summary_insert(post.betree.linked, pre_branch_roots, new_branch);

        assert(post.inv());
    }

    #[inductive(internal_grow)]
    fn internal_grow_inductive(pre: Self, post: Self, lbl: Label, new_betree: LinkedBetreeVars::State<BranchNode>, new_root_addr: Address) 
    {
        assume(false);
    }
   
    #[inductive(internal_split)]
    fn internal_split_inductive(pre: Self, post: Self, lbl: Label, new_betree: LinkedBetreeVars::State<BranchNode>, path: Path<BranchNode>, request: SplitRequest, new_addrs: SplitAddrs, path_addrs: PathAddrs) 
    { 
        assume(false);
    }
   
    #[inductive(internal_flush)]
    fn internal_flush_inductive(pre: Self, post: Self, lbl: Label, new_betree: LinkedBetreeVars::State<BranchNode>, path: Path<BranchNode>, child_idx: nat, buffer_gc: nat, new_addrs: TwoAddrs, path_addrs: PathAddrs) 
    { 
        assume(false);    
    }
   
    #[inductive(internal_compact_begin)]
    fn internal_compact_begin_inductive(pre: Self, post: Self, lbl: Label, path: Path<BranchNode>, start: nat, end: nat, input: CompactorInput) 
    { 
        assume(false);
    }
   
    #[inductive(internal_compact_abort)]
    fn internal_compact_abort_inductive(pre: Self, post: Self, lbl: Label, input_idx: int, new_betree: LinkedBetreeVars::State<BranchNode>) 
    { 
        assume(false);
    }
   
    #[inductive(internal_compact_complete)]
    fn internal_compact_complete_inductive(pre: Self, post: Self, lbl: Label, input_idx: int, new_betree: LinkedBetreeVars::State<BranchNode>, path: Path<BranchNode>, start: nat, end: nat, branch_idx: int, new_node_addr: Address, path_addrs: PathAddrs) 
    {
        assume(false);
    }
}} // end of AllocationBetree state machine

proof fn branch_summary_insert_ensures(branch_summary: Map<AU, Set<AU>>, branch: LinkedBranch<Summary>)
    requires
        branch_summary.dom().finite(),
        map_with_disjoint_values(branch_summary),
        branch.valid_sealed_branch(),
        !branch_summary.contains_key(branch.root.au),
        union_set_of_sets(branch_summary.values()).disjoint(branch.get_summary())
    ensures ({
        let post_summary = branch_summary.insert(branch.root.au, branch.get_summary());
        &&& map_with_disjoint_values(post_summary)
        &&& union_set_of_sets(post_summary.values()) == 
            union_set_of_sets(branch_summary.values()) + branch.get_summary()
    })
{
    broadcast use lemma_union_set_of_sets_contains;

    let summary_aus = union_set_of_sets(branch_summary.values());
    lemma_values_finite(branch_summary);
    let post_summary = branch_summary.insert(branch.root.au, branch.get_summary());

    assert forall |k1, k2| #[trigger] post_summary.contains_key(k1) 
    && #[trigger] post_summary.contains_key(k2) && k1 != k2
    implies post_summary[k1].disjoint(post_summary[k2])
    by {
        if k1 == branch.root.au || k2 == branch.root.au {
            let other = if k1 == branch.root.au { k2 } else { k1 };
            assert(branch_summary.values().contains(post_summary[other]));
            assert(post_summary[other] <= summary_aus);
        } else {
            assert(branch_summary.contains_key(k1));
            assert(branch_summary.contains_key(k2));
        }
    }

    lemma_values_finite(post_summary);
    assert(post_summary.contains_key(branch.root.au));
    assert(post_summary.contains_value(branch.get_summary()));

    lemma_union_set_of_sets_contains(post_summary.values(), branch.get_summary());

    assert(branch.representation().contains(branch.root)); // trigger
    assert(branch.get_summary().contains(branch.root.au));

    assert(post_summary.remove(branch.root.au) =~= branch_summary);
    assert(post_summary.values().remove(branch.get_summary()) =~= branch_summary.values());
}

impl LinkedBetree<BranchNode> {
    // merge with another disk
    pub proof fn build_branch_summary_insert(self, post: Self, branch_roots: Set<Address>, branch: LinkedBranch<Summary>)
        requires 
            branch.valid_sealed_branch(),
            self.sealed_branch_roots(branch_roots),
            set_addrs_disjoint_aus(branch_roots + set!{branch.root}),
            post.buffer_dv.entries == self.buffer_dv.entries.union_prefer_right(branch.disk_view.entries),
            self.buffer_dv.entries.dom().disjoint(branch.disk_view.entries.dom()),
        ensures
            post.build_branch_summary(branch_roots + set!{branch.root}) 
            == self.build_branch_summary(branch_roots).insert(branch.root.au, branch.get_summary())
    {
        let pre_summary = self.build_branch_summary(branch_roots);

        let post_branch_roots = branch_roots + set!{branch.root};
        let post_summary = post.build_branch_summary(post_branch_roots);
        let insert_summary = pre_summary.insert(branch.root.au, branch.get_summary());

        let post_root_to_au = Map::new(|addr| post_branch_roots.contains(addr), |addr: Address| addr.au);
        assert(post_root_to_au.dom() =~= post_branch_roots);
        
        let pre_root_to_au = Map::new(|addr| branch_roots.contains(addr), |addr: Address| addr.au);
        assert(pre_root_to_au.dom() =~= branch_roots);

        assert forall |au| true 
        implies ({
            &&& #[trigger] insert_summary.contains_key(au) == post_summary.contains_key(au)
            &&& insert_summary.contains_key(au) ==> insert_summary[au] == post_summary[au]
        })
        by {
            if insert_summary.contains_key(au) || post_summary.contains_key(au) {
                if au == branch.root.au {
                    post.build_branch_summary_contains(post_branch_roots, branch.root);
                    assert(post.get_branch(branch.root).get_summary() == branch.get_summary());
                } else {
                    let addr = self.build_branch_summary_get_addr(branch_roots, au);
                    post.build_branch_summary_contains(post_branch_roots, addr);
                    assert(self.get_branch(addr).valid_sealed_branch());
                    assert(post.get_branch(addr).get_summary() == self.get_branch(addr).get_summary());
                }
            }
        }
        assert(insert_summary.dom() =~= post_summary.dom());
        assert(insert_summary =~= post_summary);
    }
} // end of impl LinkedBetree<BranchNode>

} // end of verus!