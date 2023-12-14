#![allow(unused_imports)]
use builtin::*;

use builtin_macros::*;
use state_machines_macros::state_machine;

use vstd::prelude::*;

use crate::spec::KeyType_t::*;
use crate::spec::Messages_t::*;
use crate::disk::GenericDisk_v::*;
use crate::betree::Buffer_v::*;
use crate::betree::LinkedBufferSeq_v;
use crate::betree::LinkedBufferSeq_v::BufferSeq;
use crate::betree::BufferOffsets_v::*;
use crate::betree::OffsetMap_v::*;
use crate::betree::Memtable_v::*;
use crate::betree::Domain_v::*;
use crate::betree::PivotTable_v::*;
use crate::betree::SplitRequest_v::*;
use crate::abstract_system::StampedMap_v::*;
use crate::abstract_system::MsgHistory_v::*;

verus! {
// Introduces a diskview and pointers, carries forward filtered buffer stacks inside the 
// betree nodes. There are two disk views here. One for the BetreeNode type, and one for 
// the abstract Branch type. A refining state machine replaces single-node branches with
// b+trees.

#[verifier::ext_equal]
pub struct BetreeNode {
    pub buffers: BufferSeq,
    pub pivots: PivotTable,
    pub children: Seq<Pointer>,
    pub flushed: BufferOffsets // # of buffers flushed to each child
}

pub type BufferDiskView = LinkedBufferSeq_v::DiskView;

impl BetreeNode {
    pub open spec(checked) fn wf(self) -> bool
    {
        &&& self.pivots.wf()
        &&& self.children.len() == self.pivots.num_ranges()
        &&& self.children.len() == self.flushed.len()
        &&& self.flushed.all_lte(self.buffers.len()) // values in flushed are bounded by # of buffers
    }

    pub open spec(checked) fn valid_child_index(self, child_idx: nat) -> bool
    {
        &&& child_idx < self.children.len()   
    }

    pub open spec(checked) fn occupied_child_index(self, child_idx: nat) -> bool
        recommends self.wf()
    {
        &&& self.valid_child_index(child_idx)
        &&& self.children[child_idx as int].is_Some()
    }

    pub open spec(checked) fn my_domain(self) -> Domain
        recommends self.wf()
    {
        Domain::Domain{
            start: self.pivots[0],
            end: self.pivots.pivots.last()
        }
    }

    pub open spec(checked) fn child_domain(self, child_idx: nat) -> Domain
        recommends self.wf(), self.valid_child_index(child_idx)
    {
        Domain::Domain{
            start: self.pivots[child_idx as int],
            end: self.pivots[child_idx as int + 1]
        }
    }

    pub open spec(checked) fn extend_buffer_seq(self, buffers: BufferSeq) -> BetreeNode
        recommends self.wf()
    {
        BetreeNode{
            buffers: self.buffers.extend(buffers),
            pivots: self.pivots,
            children: self.children,
            flushed: self.flushed
        }
    }

    #[verifier(recommends_by)]
    pub proof fn flushed_ofs_inline_lemma(self, key: Key)
    {
        self.pivots.route_lemma(key);
        assert( 0 <= self.pivots.route(key) < self.flushed.offsets.len() );
    }

    // returns the flushed offset (index into buffers) for a given key
    // buffers flushed to a child are no longer active for that child
    // renamed from ActiveBuffersForKey
    pub open spec /*XXX (checked)*/ fn flushed_ofs(self, key: Key) -> nat
        recommends self.key_in_domain(key)
    {
        recommends_by(Self::flushed_ofs_inline_lemma);
        let r = self.pivots.route(key);
        self.flushed.offsets[r]
    }

    pub open spec(checked) fn is_leaf(self) -> bool
    {
        &&& self.children.len() == 1
        &&& self.children[0].is_None()
        &&& self.flushed.offsets == seq![0nat]
    }

    pub open spec(checked) fn is_index(self) -> bool
    {
        forall |i| #![auto] self.valid_child_index(i) ==> self.children[i as int].is_Some()
    }

    pub open spec(checked) fn can_split_leaf(self, split_key: Key) -> bool
    {
        &&& self.wf()
        &&& self.is_leaf()
        &&& self.my_domain().contains(split_key)
        &&& self.my_domain().get_Domain_start() != to_element(split_key)
    }

    pub open spec(checked) fn split_leaf(self, split_key: Key) -> (BetreeNode, BetreeNode)
        recommends self.can_split_leaf(split_key)
    {
        let new_left = BetreeNode{
            buffers: self.buffers,
            pivots: self.pivots.update(1, to_element(split_key)),
            children: self.children,
            flushed: self.flushed
        };

        let new_right = BetreeNode{
            buffers: self.buffers,
            pivots: self.pivots.update(0, to_element(split_key)),
            children: self.children,
            flushed: self.flushed
        };

        (new_left, new_right)
    }

    pub open spec(checked) fn can_split_index(self, pivot_idx: nat) -> bool
    {
        &&& self.wf()
        &&& self.is_index()
        &&& 0 < pivot_idx < self.pivots.num_ranges()
    }

    pub open spec(checked) fn  split_index(self, pivot_idx: nat) -> (BetreeNode, BetreeNode)
        recommends self.can_split_index(pivot_idx)
    {
        let idx = pivot_idx as int;
        let new_left = BetreeNode{
            buffers: self.buffers,
            pivots: self.pivots.subrange(0, idx+1),
            children: self.children.subrange(0, idx),
            flushed: self.flushed.slice(0, idx)
        };

        let new_right = BetreeNode{
            buffers: self.buffers,
            pivots: self.pivots.subrange(idx, self.pivots.len() as int),
            children: self.children.subrange(idx, self.children.len() as int),
            flushed: self.flushed.slice(idx, self.flushed.len() as int)
        };

        (new_left, new_right)
    }

    pub open spec(checked) fn empty_root(domain: Domain) -> BetreeNode
        recommends domain.wf(), domain.is_Domain()
    {
        BetreeNode{
            buffers: BufferSeq::empty(),
            pivots: domain_to_pivots(domain),
            children: seq![None],
            flushed: BufferOffsets{offsets: seq![0]}
        }
    }

    pub open spec(checked) fn compact_key_range(self, start: nat, end: nat, k: Key, buffer_dv: BufferDiskView) -> bool
        recommends self.wf(), start < end <= self.buffers.len()
    {
        &&& self.key_in_domain(k)
        &&& self.flushed_ofs(k) <= end
        &&& exists |buffer_idx| self.buffers.slice(start as int, end as int).key_in_buffer_filtered(
                buffer_dv, self.make_offset_map().decrement(start), 0, k, buffer_idx)
    }

    pub open spec(checked) fn compact_key_value(self, start: nat, end: nat, k: Key, buffer_dv: BufferDiskView) -> Message
        recommends self.wf(), start < end <= self.buffers.len(), 
            self.compact_key_range(start, end, k, buffer_dv)
    {
        let from = if self.flushed_ofs(k) <= start { 0 } else { self.flushed_ofs(k)-start };
        self.buffers.slice(start as int, end as int).query_from(buffer_dv, k, from)
    }

    pub open spec(checked) fn key_in_domain(self, key: Key) -> bool
    {
        &&& self.wf()
        &&& self.pivots.bounded_key(key)
    }

    pub open spec /*XXX(checked)*/ fn child_ptr(self, key: Key) -> Pointer
        recommends self.key_in_domain(key)
    {
        self.children[self.pivots.route(key)]
    }

    pub open spec(checked) fn make_offset_map(self) -> OffsetMap
        recommends self.wf()
    {
        OffsetMap{ offsets: Map::new(|k| true,
            |k| if self.key_in_domain(k) {
                self.flushed_ofs(k)
            } else {
                self.buffers.len()
            })
        }
    }
} // end impl BetreeNode


pub struct DiskView {
    pub entries: Map<Address, BetreeNode>,
}

impl DiskView {
    pub open spec(checked) fn entries_wf(self) -> bool 
    {
        forall |addr| #[trigger] self.entries.contains_key(addr) ==> self.entries[addr].wf()
    }

    pub open spec(checked) fn is_nondangling_ptr(self, ptr: Pointer) -> bool
    {
        ptr.is_Some() ==> self.entries.contains_key(ptr.unwrap())
    }

    pub open spec(checked) fn node_has_nondangling_child_ptrs(self, node: BetreeNode) -> bool
        recommends self.entries_wf(), node.wf()
    {
        forall |i| #[trigger] node.valid_child_index(i) ==> self.is_nondangling_ptr(node.children[i as int])
    }

    pub open spec(checked) fn child_linked(self, node: BetreeNode, idx: nat) -> bool
        recommends self.entries_wf(), node.wf(), 
            node.valid_child_index(idx),
            self.node_has_nondangling_child_ptrs(node),
    {
        let child_ptr = node.children[idx as int];
        &&& child_ptr.is_Some() ==> self.entries[child_ptr.unwrap()].my_domain() == node.child_domain(idx)
    }

    pub open spec(checked) fn node_has_linked_children(self, node: BetreeNode) -> bool
        recommends self.entries_wf(), node.wf(), self.node_has_nondangling_child_ptrs(node)
    {
        forall |i| #[trigger] node.valid_child_index(i) ==> self.child_linked(node, i)
    }

    pub open spec(checked) fn healthy_child_ptrs(self) -> bool
        recommends self.entries_wf()
    {
        &&& forall |addr| #[trigger] self.entries.contains_key(addr) ==> ({
            &&& self.node_has_nondangling_child_ptrs(self.entries[addr])
            &&& self.node_has_linked_children(self.entries[addr])
        })
    }

    pub open spec(checked) fn wf(self) -> bool
    {
        &&& self.entries_wf()
        &&& self.healthy_child_ptrs()
        &&& self.entries.dom().finite()
    }

    pub open spec(checked) fn get(self, ptr: Pointer) -> BetreeNode
        recommends self.is_nondangling_ptr(ptr), ptr.is_Some()
    {
        self.entries[ptr.unwrap()]
    }

    pub open spec(checked) fn agrees_with_disk(self, other: DiskView) -> bool
    {
        self.entries.agrees(other.entries)
    }

    pub open spec(checked) fn is_subdisk(self, bigger: DiskView) -> bool
    {
        self.entries <= bigger.entries  
    }

    pub open spec(checked) fn node_children_respects_rank(self, ranking: Ranking, addr: Address) -> bool
        recommends self.wf(), self.entries.contains_key(addr), ranking.contains_key(addr)
    {
        let node = self.entries[addr];
        &&& forall |idx| #[trigger] node.valid_child_index(idx) && node.children[idx as int].is_Some() 
            ==> ({
                let child_addr = node.children[idx as int].unwrap();
                &&& ranking.contains_key(child_addr)
                &&& ranking[child_addr] < ranking[addr]
            })
    }

    pub open spec(checked) fn valid_ranking(self, ranking: Ranking) -> bool
    {
        &&& self.wf()
        &&& forall |addr| self.entries.contains_key(addr) && #[trigger] ranking.contains_key(addr)
            ==> self.node_children_respects_rank(ranking, addr)
    }

    pub open spec(checked) fn is_fresh(self, addrs: Set<Address>) -> bool 
    {
        self.entries.dom().disjoint(addrs)
    }

    pub open spec(checked) fn modify_disk(self, addr: Address, node: BetreeNode) -> DiskView
    {
        DiskView{ entries: self.entries.insert(addr, node) }
    }

    pub open spec(checked) fn no_dangling_buffer_ptr(self, buffer_dv: BufferDiskView) -> bool
    {
        forall |addr| self.entries.contains_key(addr) ==> #[trigger] self.entries[addr].buffers.valid(buffer_dv)
    }
}

pub open spec(checked) fn empty_disk() -> DiskView
{
    DiskView{ entries: Map::empty() }
}


// maybe name this a none flush addrs
pub struct TwoAddrs {
    pub addr1: Address,
    pub addr2: Address,
}

impl TwoAddrs {
    pub open spec(checked) fn no_duplicates(self) -> bool
    {
        &&& self.addr1 != self.addr2
    }

    pub open spec(checked) fn repr(self) -> Set<Address>
        recommends self.no_duplicates()
    {
        set!{self.addr1, self.addr2}
    }
}

pub struct SplitAddrs {
    pub left: Address,
    pub right: Address,
    pub parent: Address
}

impl SplitAddrs {
    pub open spec(checked) fn no_duplicates(self) -> bool
    {
        &&& self.left != self.right
        &&& self.right != self.parent
        &&& self.parent != self.left
    }

    pub open spec(checked) fn repr(self) -> Set<Address>
        recommends self.no_duplicates()
    {
        set!{self.left, self.right, self.parent}
    }
}

pub struct LinkedBetree {
    pub root: Pointer,
    pub dv: DiskView,
    pub buffer_dv: BufferDiskView
}

pub type StampedBetree = Stamped<LinkedBetree>;

pub open spec(checked) fn empty_linked_betree() -> LinkedBetree
{
    LinkedBetree{root: None, dv: empty_disk(), buffer_dv: LinkedBufferSeq_v::empty_disk() }
}

pub open spec(checked) fn empty_image() -> StampedBetree {
    Stamped{ value: empty_linked_betree(), seq_end: 0 }
}

impl LinkedBetree {
    pub open spec(checked) fn wf(self) -> bool
    {
        &&& self.dv.wf()
        &&& self.buffer_dv.wf()
        &&& self.dv.is_nondangling_ptr(self.root)
        &&& self.dv.is_fresh(self.buffer_dv.repr())
        &&& self.dv.no_dangling_buffer_ptr(self.buffer_dv)
    }

    pub open spec(checked) fn has_root(self) -> bool
    {
        &&& self.root.is_Some()
        &&& self.dv.is_nondangling_ptr(self.root)
    }

    pub open spec(checked) fn root(self) -> BetreeNode
        recommends self.has_root()
    {
        self.dv.get(self.root)
    }

    pub open spec(checked) fn valid_ranking(self, ranking: Ranking) -> bool
    {
        &&& self.wf()
        &&& self.dv.valid_ranking(ranking)
        &&& self.has_root() ==> ranking.contains_key(self.root.unwrap())
    }

    pub open spec(checked) fn acyclic(self) -> bool
    {
        &&& self.wf()
        &&& exists |ranking| self.valid_ranking(ranking)
    }

    pub open spec(checked) fn the_ranking(self) -> Ranking
        recommends self.acyclic()
    {
        let ranking = choose |ranking| self.valid_ranking(ranking);
        ranking
    }

    pub open spec(checked) fn is_fresh(self, addrs: Set<Address>) -> bool
    {
        &&& self.dv.is_fresh(addrs)
        &&& self.buffer_dv.is_fresh(addrs)
    }

    pub open spec(checked) fn child_at_idx(self, idx: nat) -> LinkedBetree
        recommends self.wf(), self.has_root(), self.root().valid_child_index(idx)
    {
        LinkedBetree{ root: self.root().children[idx as int], dv: self.dv, buffer_dv: self.buffer_dv }
    }

    pub open spec(checked) fn child_for_key(self, k: Key) -> LinkedBetree
        recommends self.has_root(), self.root().key_in_domain(k)
    {
        LinkedBetree{ root: self.root().child_ptr(k), dv: self.dv, buffer_dv: self.buffer_dv }
    }

    pub open spec(checked) fn get_rank(self, ranking: Ranking) -> nat
        recommends self.wf()
    {
        if self.has_root() && ranking.contains_key(self.root.unwrap()) {
            ranking[self.root.unwrap()] + 1
        } else {
            0
        }
    }

    pub open spec(checked) fn child_count(self) -> nat
        recommends self.wf()
    {
        if self.has_root() { self.root().children.len() } else { 0 }
    }

    pub open spec(checked) fn can_recurse_for_reachable(self, ranking: Ranking, child_idx: nat) -> bool
    {
        &&& self.wf()
        &&& self.has_root()
        &&& self.valid_ranking(ranking)
        &&& child_idx <= self.child_count()
    }

    #[verifier::decreases_by]
    pub proof fn reachable_addrs_using_ranking_recur_proof(self, ranking: Ranking, child_idx: nat)
    {
        if child_idx < self.child_count() {
            assert(self.root().valid_child_index(child_idx)); // trigger
        }
    }

    // TODO(verus): workaround since verus doesn't support mutually recursive closure
    pub open spec(checked) fn reachable_addrs_using_ranking_recur(self, ranking: Ranking, child_idx: nat) -> Set<Address>
        recommends self.can_recurse_for_reachable(ranking, child_idx)
        decreases self.get_rank(ranking), self.child_count()-child_idx when self.can_recurse_for_reachable(ranking, child_idx) 
            via Self::reachable_addrs_using_ranking_recur_proof
    {
        if child_idx == self.child_count() {
            set!{}
        } else {
            let child_addrs = self.child_at_idx(child_idx).reachable_addrs_using_ranking(ranking);
            let right_subtree_addrs = self.reachable_addrs_using_ranking_recur(ranking, child_idx + 1);
            child_addrs + right_subtree_addrs
        }
    }

    pub open spec(checked) fn reachable_addrs_using_ranking(self, ranking: Ranking) -> Set<Address>
        recommends self.wf(), self.valid_ranking(ranking)
        decreases self.get_rank(ranking) when self.wf() && self.valid_ranking(ranking)
    {
        if self.has_root() {
            let sub_tree_addrs = self.reachable_addrs_using_ranking_recur(ranking, 0);
            let root_addr = set!{ self.root.unwrap() };
            root_addr + sub_tree_addrs
        } else {
            set!{}
        }
    }

    // repr of all reachable betree nodes
    pub open spec(checked) fn reachable_betree_addrs(self) -> Set<Address>
        recommends self.acyclic()
    {
        self.reachable_addrs_using_ranking(self.the_ranking())
    }

    // TODO(Jialin): can change to decreases by when we prove that all address from betree_addr is nondangling ptr
    pub open spec/*XXX (checked)*/ fn reachable_buffer(self, addr: Address, buffer_addr: Address) -> bool
        recommends self.acyclic()
    {
        &&& self.reachable_betree_addrs().contains(addr) 
        &&& self.dv.get(Some(addr)).buffers.repr().contains(buffer_addr)
    }

    // repr of all reachable buffers
    pub open spec(checked) fn reachable_buffer_addrs(self) -> Set<Address>
        recommends self.acyclic()
    {
        let betree_addrs = self.reachable_betree_addrs();
        Set::new(|buffer_addr| exists |addr| self.reachable_buffer(addr, buffer_addr))
    }

    pub open spec(checked) fn build_tight_tree(self) -> LinkedBetree
    {
        if self.acyclic() {
            let tight_dv = DiskView{ entries: self.dv.entries.restrict(self.reachable_betree_addrs()) };
            let tight_buffer_dv = BufferDiskView{ entries: self.buffer_dv.entries.restrict(self.reachable_buffer_addrs()) };
            LinkedBetree{ root: self.root, dv: tight_dv, buffer_dv: tight_buffer_dv }
        } else {
            self
        }
    }

    pub open spec(checked) fn push_memtable(self, memtable: Memtable, new_addrs: TwoAddrs) -> LinkedBetree
        recommends self.wf(), new_addrs.no_duplicates(), self.is_fresh(new_addrs.repr())
    {
        let memtable_buffer = BufferSeq{ buffers: seq![new_addrs.addr2] };
        let new_root = 
            if self.has_root() {
                self.root().extend_buffer_seq(memtable_buffer)
            } else {
                BetreeNode::empty_root(total_domain()).extend_buffer_seq(memtable_buffer)
            };
        let new_dv = self.dv.modify_disk(new_addrs.addr1, new_root);
        let new_buffer_dv = self.buffer_dv.modify_disk(new_addrs.addr2, memtable.buffer);
        LinkedBetree{ root: Some(new_addrs.addr1), dv: new_dv, buffer_dv: new_buffer_dv }
    }

    pub open spec(checked) fn grow(self, new_root_addr: Address) -> LinkedBetree
        recommends self.wf(), self.is_fresh(Set::empty().insert(new_root_addr))
    {
        let new_root = BetreeNode{
            buffers: BufferSeq::empty(), 
            pivots: domain_to_pivots(total_domain()),
            children: seq![self.root],
            flushed: BufferOffsets{offsets: seq![0]},
        };
        let new_dv = self.dv.modify_disk(new_root_addr, new_root);
        LinkedBetree{ root: Some(new_root_addr), dv: new_dv, buffer_dv: self.buffer_dv }
    }

    // operations on linked betree:
    pub open spec(checked) fn can_split_parent(self, request: SplitRequest) -> bool
    {
        &&& self.wf()
        &&& self.has_root()
        &&& self.root().valid_child_index(request.get_child_idx())
        &&& self.child_at_idx(request.get_child_idx()).has_root()
        &&& match request {
            SplitRequest::SplitLeaf{child_idx, split_key} => {
                &&& self.child_at_idx(child_idx).root().can_split_leaf(split_key)
            }
            SplitRequest::SplitIndex{child_idx, child_pivot_idx} => {
                &&& self.child_at_idx(child_idx).root().can_split_index(child_pivot_idx)                
            }
        }
    }

    // NOTE: recommmends check sucks here
    pub open spec(checked) fn split_parent(self, request: SplitRequest, new_addrs: SplitAddrs) -> LinkedBetree
        recommends self.can_split_parent(request)
    {
        match request {
            SplitRequest::SplitLeaf{child_idx, split_key} => {
                let (new_left_child, new_right_child) = self.child_at_idx(child_idx).root().split_leaf(split_key);
                let new_children = self.root().children.update(child_idx as int, Some(new_addrs.left)
                    ).insert(child_idx as int + 1, Some(new_addrs.right));

                let new_parent = BetreeNode{
                    buffers: self.root().buffers,
                    pivots: self.root().pivots.insert(child_idx as int + 1, to_element(split_key)),
                    children: new_children,
                    flushed: self.root().flushed.dup(child_idx as int)
                };

                let new_dv = self.dv.modify_disk(new_addrs.left, new_left_child
                    ).modify_disk(new_addrs.right, new_right_child
                    ).modify_disk(new_addrs.parent, new_parent);

                LinkedBetree{root: Some(new_addrs.parent), dv: new_dv, buffer_dv: self.buffer_dv }
            }
            SplitRequest::SplitIndex{child_idx, child_pivot_idx} => {
                let (new_left_child, new_right_child) = self.child_at_idx(child_idx).root().split_index(child_pivot_idx);
                let new_children = self.root().children.update(child_idx as int, Some(new_addrs.left)
                    ).insert(child_idx as int + 1, Some(new_addrs.right));

                // NOTE(Jialin): literally needs to match the syntax for the recommend check to be recognized
                let new_parent = BetreeNode{
                    buffers: self.root().buffers,
                    pivots: self.root().pivots.insert(child_idx as int + 1, 
                            self.child_at_idx(child_idx).root().pivots[child_pivot_idx as int]), 
                    children: new_children,
                    flushed: self.root().flushed.dup(child_idx as int)
                };

                let new_dv = self.dv.modify_disk(new_addrs.left, new_left_child
                    ).modify_disk(new_addrs.right, new_right_child
                    ).modify_disk(new_addrs.parent, new_parent);

                LinkedBetree{ root: Some(new_addrs.parent), dv: new_dv, buffer_dv: self.buffer_dv }
            }
        }
    }

    pub open spec(checked) fn can_flush(self, child_idx: nat, buffer_gc: nat) -> bool
    {
        &&& self.wf()
        &&& self.has_root()
        &&& self.root().occupied_child_index(child_idx)
        &&& self.root().flushed.update(child_idx as int, self.root().buffers.len()).all_gte(buffer_gc)
    }

    pub open spec/*XXX(checked)*/ fn flush(self, child_idx: nat, buffer_gc: nat, new_addrs: TwoAddrs) -> LinkedBetree
        recommends self.can_flush(child_idx, buffer_gc), self.is_fresh(new_addrs.repr())
    {
        let root = self.root();
        let flush_upto = root.buffers.len(); 
        let flushed_ofs = root.flushed.offsets[child_idx as int];

        let buffers_to_child = root.buffers.slice(flushed_ofs as int, flush_upto as int);
        let child = self.dv.get(root.children[child_idx as int]);
        let new_child = child.extend_buffer_seq(buffers_to_child);

        let new_root = BetreeNode{
            buffers: root.buffers.slice(buffer_gc as int, flush_upto as int),
            pivots: root.pivots,
            children: root.children.update(child_idx as int, Some(new_addrs.addr2)),
            flushed: root.flushed.update(child_idx as int, flush_upto).shift_left(buffer_gc),
        };

        let new_dv = self.dv.modify_disk(new_addrs.addr1, new_root).modify_disk(new_addrs.addr2, new_child);
        LinkedBetree{ root: Some(new_addrs.addr1), dv: new_dv, buffer_dv: self.buffer_dv }
    }

    pub open spec(checked) fn can_compact(self, start: nat, end: nat, compacted_buffer: Buffer) -> bool 
    {
        &&& self.wf()
        &&& self.has_root()
        &&& start < end <= self.root().buffers.len()
        &&& forall |k| #![auto] compacted_buffer.map.contains_key(k) <==> self.root().compact_key_range(start, end, k, self.buffer_dv)
        &&& forall |k| #![auto] compacted_buffer.map.contains_key(k) ==>
                compacted_buffer.query(k) == self.root().compact_key_value(start, end, k, self.buffer_dv)
    }

     pub open spec/*XXX(checked)*/ fn compact(self, start: nat, end: nat, compacted_buffer: Buffer, new_addrs: TwoAddrs) -> LinkedBetree
        recommends 
            new_addrs.no_duplicates(), 
            self.is_fresh(new_addrs.repr()),
            self.can_compact(start, end, compacted_buffer),
    {
        let new_root = BetreeNode{
            buffers: self.root().buffers.update_subrange(start as int, end as int, new_addrs.addr2),
            pivots: self.root().pivots,
            children: self.root().children,
            flushed: self.root().flushed.adjust_compact(start as int, end as int)
        };

        let new_dv = self.dv.modify_disk(new_addrs.addr1, new_root);
        let new_buffer_dv = self.buffer_dv.modify_disk(new_addrs.addr2, compacted_buffer);
        LinkedBetree{ root: Some(new_addrs.addr1), dv: new_dv, buffer_dv: new_buffer_dv }
    }

} // end of LinkedBetree impl

pub struct QueryReceiptLine{
    pub linked: LinkedBetree,
    pub result: Message
}

impl QueryReceiptLine{
    pub open spec(checked) fn wf(self) -> bool
    {
        &&& self.result.is_Define()
    }
} // end impl QueryReceiptLine

pub struct QueryReceipt{
    pub key: Key,
    pub linked: LinkedBetree,
    pub lines: Seq<QueryReceiptLine>
}

impl QueryReceipt{
    pub open spec(checked) fn structure(self) -> bool
    {
        &&& 0 < self.lines.len()
        &&& self.linked.wf()
        &&& self.lines[0].linked == self.linked
        &&& forall |i:nat| #![auto] i < self.lines.len() ==> self.lines[i as int].linked.dv == self.linked.dv
        &&& forall |i:nat| #![auto] i < self.lines.len() ==> self.lines[i as int].linked.buffer_dv == self.linked.buffer_dv
        &&& forall |i:nat| #![auto] i < self.lines.len() ==> self.lines[i as int].linked.has_root() <==> i < self.lines.len()-1
        &&& self.lines.last().result == Message::Define{value: default_value()}
    }

    pub open spec(checked) fn node(self, i:int) -> BetreeNode
        recommends self.structure(), 0 <= i < self.lines.len() - 1
    {
        self.lines[i].linked.root()
    }

    pub open spec(checked) fn all_lines_wf(self) -> bool
        recommends self.structure()
    {
        &&& forall |i:nat| #![auto] i < self.lines.len() ==> self.lines[i as int].wf()
        &&& forall |i:nat| #![auto] i < self.lines.len() ==> self.lines[i as int].linked.acyclic()
        &&& forall |i:nat| #![auto] i < self.lines.len()-1 ==> self.lines[i as int].linked.root().buffers.valid(self.linked.buffer_dv)
        &&& forall |i:nat| #![auto] i < self.lines.len()-1 ==> self.node(i as int).key_in_domain(self.key)
    }

    pub open spec(checked) fn child_linked_at(self, i: int) -> bool
        recommends self.structure(), self.all_lines_wf(), 0 <= i < self.lines.len()-1
    {
        self.lines[i+1].linked.root == self.node(i).child_ptr(self.key)
    }

    pub open spec(checked) fn result_at(self, i: int) -> Message
        recommends 0 <= i < self.lines.len()
    {
        self.lines[i].result
    }

    pub open spec/*XXX(checked)*/ fn result_linked_at(self, i: int) -> bool
        recommends self.structure(), self.all_lines_wf(), 0 <= i < self.lines.len()-1
    {
        let start = self.node(i).flushed_ofs(self.key);
        let msg = self.node(i).buffers.query_from(self.linked.buffer_dv, self.key, start as int);
        self.lines[i].result == self.result_at(i+1).merge(msg)
    }

    pub open spec(checked) fn result(self) -> Message
        recommends self.structure()
    {
        self.result_at(0)
    }

    pub open spec(checked) fn valid(self) -> bool
    {
        &&& self.structure()
        &&& self.all_lines_wf()
        &&& (forall |i| #![auto] 0 <= i < self.lines.len()-1 ==> self.child_linked_at(i))
        &&& (forall |i| #![auto] 0 <= i < self.lines.len()-1 ==> self.result_linked_at(i))
    }

    pub open spec(checked) fn valid_for(self, linked: LinkedBetree, key: Key) -> bool
    {
        &&& self.valid()
        &&& self.linked == linked
        &&& self.key == key
    }
} // end impl QueryReceipt

pub type PathAddrs = Seq<Address>;

pub struct Path{
    pub linked: LinkedBetree,
    pub key: Key,
    pub depth: nat
}

impl Path{
    pub open spec(checked) fn subpath(self) -> Path
        recommends 0 < self.depth, 
            self.linked.has_root(), 
            self.linked.root().key_in_domain(self.key)
    {
        Path{ linked: self.linked.child_for_key(self.key), key: self.key, depth: (self.depth - 1) as nat }
    }

    pub open spec(checked) fn valid(self) -> bool
        decreases self.depth
    {
        &&& self.linked.has_root()
        &&& self.linked.acyclic()
        &&& self.linked.root().key_in_domain(self.key)
        &&& (0 < self.depth ==> self.linked.root().is_index())
        &&& (0 < self.depth ==> self.subpath().valid())
    }

    pub open spec(checked) fn target(self) -> LinkedBetree
        recommends self.valid()
        decreases self.depth
    {
        if self.depth == 0 {
            self.linked
        } else {
            self.subpath().target()
        }
    }

    pub open spec(checked) fn addrs_on_path(self) -> Set<Address>
        recommends self.valid()
        decreases self.depth
    {
        if self.depth == 0 {
            set!{self.linked.root.unwrap()}
        } else {
            self.subpath().addrs_on_path() + set!{self.linked.root.unwrap()}
        }
    }

    pub open spec/*XXX(checked)*/ fn can_substitute(self, replacement: LinkedBetree, path_addrs: PathAddrs) -> bool
    {
        &&& self.valid()
        &&& self.target().has_root()
        &&& replacement.wf()
        &&& replacement.has_root()
        &&& replacement.root().my_domain() == self.target().root().my_domain()
        &&& self.depth == path_addrs.len()
        &&& self.linked.dv.is_subdisk(replacement.dv)
        &&& self.linked.buffer_dv.is_subdisk(replacement.buffer_dv)
    }

    pub open spec/*XXX (checked)*/ fn substitute(self, replacement: LinkedBetree, path_addrs: PathAddrs) -> LinkedBetree
        recommends self.can_substitute(replacement, path_addrs)
        decreases self.depth, 1nat
    {
        if self.depth == 0 {
            replacement
        } else {
            let node = self.linked.root();
            let subtree = self.subpath().substitute(replacement, path_addrs.subrange(1, path_addrs.len() as int));
            let new_children = node.children.update(node.pivots.route(self.key), subtree.root);
            let new_node = BetreeNode{ buffers: node.buffers, pivots: node.pivots, children: new_children, flushed: node.flushed };
            let new_dv = subtree.dv.modify_disk(path_addrs[0], new_node);
            LinkedBetree{ root: Some(path_addrs[0]), dv: new_dv, buffer_dv: replacement.buffer_dv }
        }
    }
} // end impl Path


state_machine!{ LinkedBetreeVars {
    fields {
        pub memtable: Memtable,
        pub linked: LinkedBetree,
    }

    pub open spec(checked) fn wf(self) -> bool {
        &&& self.linked.wf()
    }

    #[is_variant]
    pub enum Label
    {
        Query{end_lsn: LSN, key: Key, value: Value},
        Put{puts: MsgHistory},
        FreezeAs{stamped_betree: StampedBetree},
        Internal{},   // Local No-op label
    }

    transition!{ query(lbl: Label, receipt: QueryReceipt) {
        require let Label::Query{end_lsn, key, value} = lbl;
        require end_lsn == pre.memtable.seq_end;
        require receipt.valid_for(pre.linked, key);
        require Message::Define{value} == receipt.result().merge(pre.memtable.query(key));
    }}

    transition!{ put(lbl: Label) {
        require let Label::Put{puts} = lbl;
        require puts.wf();
        require puts.seq_start == pre.memtable.seq_end;
        update memtable = pre.memtable.apply_puts(puts);
    }}

    transition!{ freeze_as(lbl: Label) {
        require let Label::FreezeAs{stamped_betree} = lbl;
        // require pre.wf();
        require pre.memtable.is_empty();
        require stamped_betree == Stamped{value: pre.linked, seq_end: pre.memtable.seq_end};
    }}

    transition!{ internal_flush_memtable(lbl: Label, new_addrs: TwoAddrs) {
        require let Label::Internal{} = lbl;
        // require pre.wf();
        require new_addrs.no_duplicates();
        require pre.linked.is_fresh(new_addrs.repr());
        update memtable = pre.memtable.drain();
        update linked = pre.linked.push_memtable(pre.memtable, new_addrs).build_tight_tree();
    }}

    transition!{ internal_grow(lbl: Label, new_root_addr: Address) {
        require let Label::Internal{} = lbl;
        // require pre.wf();
        require pre.linked.is_fresh(Set::empty().insert(new_root_addr));
        update linked = pre.linked.grow(new_root_addr);
    }}

    transition!{ internal_split(lbl: Label, path: Path, request: SplitRequest, new_addrs: SplitAddrs, path_addrs: PathAddrs) {
        require let Label::Internal{} = lbl;
        require path.valid();
        require path_addrs.no_duplicates();
        require path.depth == path_addrs.len();
        require path.target().can_split_parent(request);
        require new_addrs.no_duplicates();
        require new_addrs.repr().disjoint(path_addrs.to_set());
        require path.linked == pre.linked;
        require pre.linked.is_fresh(new_addrs.repr());
        require pre.linked.is_fresh(path_addrs.to_set());
        update linked = path.substitute(path.target().split_parent(request, new_addrs), path_addrs).build_tight_tree();
    }}

    transition!{ internal_flush(lbl: Label, path: Path, child_idx: nat, buffer_gc: nat, new_addrs: TwoAddrs, path_addrs: PathAddrs) {
        require let Label::Internal{} = lbl;
        require path.valid();
        require path_addrs.no_duplicates();
        require path.depth == path_addrs.len();
        require path.target().can_flush(child_idx, buffer_gc);
        require new_addrs.no_duplicates();
        require new_addrs.repr().disjoint(path_addrs.to_set());
        require path.linked == pre.linked;
        require pre.linked.is_fresh(new_addrs.repr());
        require pre.linked.is_fresh(path_addrs.to_set());
        update linked = path.substitute(path.target().flush(child_idx, buffer_gc, new_addrs), path_addrs).build_tight_tree();
    }}

    transition!{ internal_compact(lbl: Label, path: Path, start: nat, end: nat, compacted_buffer: Buffer, new_addrs: TwoAddrs, path_addrs: PathAddrs) {
        require let Label::Internal{} = lbl;
        require path.valid();
        require path_addrs.no_duplicates();
        require path.depth == path_addrs.len();
        require path.target().can_compact(start, end, compacted_buffer);
        require new_addrs.no_duplicates();
        require new_addrs.repr().disjoint(path_addrs.to_set());
        require path.linked == pre.linked;
        require pre.linked.is_fresh(new_addrs.repr());
        require pre.linked.is_fresh(path_addrs.to_set());
        update linked = path.substitute(path.target().compact(start, end, compacted_buffer, new_addrs), path_addrs).build_tight_tree();
    }}

    transition!{ internal_noop(lbl: Label) {
        require let Label::Internal{} = lbl;
    }}

    init!{ initialize(stamped_betree: StampedBetree) {
        require stamped_betree.value.wf();
        init memtable = Memtable::empty_memtable(stamped_betree.seq_end);
        init linked = stamped_betree.value;
    }}
}} // end LinkedBetree state machine


} // end verus!
