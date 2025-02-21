// Copyright 2018-2024 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, University of Washington
// SPDX-License-Identifier: BSD-2-Clause
//
use builtin::*;
use vstd::math;
use vstd::prelude::*;

use state_machines_macros::state_machine;

use crate::abstract_system::MsgHistory_v::*;
use crate::abstract_system::StampedMap_v::LSN;
use crate::allocation_layer::MiniAllocator_v::*;
use crate::disk::GenericDisk_v::AU;
use crate::disk::GenericDisk_v::*;
use crate::allocation_layer::LikesJournal_v;
use crate::journal::LinkedJournal_v;
use crate::journal::LinkedJournal_v::{DiskView, LinkedJournal, TruncatedJournal};

verus! {

#[verifier::ext_equal]
pub struct JournalImage {
    pub tj: TruncatedJournal,
    pub first: AU,
}

impl JournalImage {
    pub open spec(checked) fn wf(self) -> bool {
        self.tj.wf()
    }

    pub open spec(checked) fn accessible_aus(self) -> Set<AU> {
        to_aus(self.tj.disk_view.entries.dom())
    }

    pub open spec(checked) fn empty() -> Self {
        Self { tj: TruncatedJournal::mkfs(), first: 0 }
    }

    pub open spec(checked) fn valid_image(self) -> bool {
        &&& self.tj.disk_view.wf_addrs()

        &&& self.tj.disk_view.pointer_is_upstream(self.tj.freshest_rec, self.first)
        &&& self.tj.disk_view.domain_tight_wrt_index(self.tj.build_lsn_au_index(self.first), self.tj.freshest_rec)
        &&& self.tj.disk_view.bounded_inactive_lsns(self.tj.build_lsn_au_index(self.first), self.tj.freshest_rec)
    }

    pub proof fn empty_is_valid_image()
        ensures
            Self::empty().valid_image(),
    {
        TruncatedJournal::mkfs_ensures();
        reveal(DiskView::pages_allocated_in_lsn_order);
    }
}

pub type LsnAUIndex = Map<LSN, AU>;

// Removed (checked) due to lambda being total
pub open spec   /*(checked)*/
fn lsn_au_index_discard_up_to(lsn_au_index: LsnAUIndex, bdy: LSN) -> (out:
    LsnAUIndex)  //     ensures  //         out.len(lsn_au_index),  //         forall |k| out.contains_key(k) :: bdy <= k,  //         forall |k| lsn_au_index.contains_key(k) && bdy <= k ==> out.contains_key(k),
{
    Map::new(|lsn| lsn_au_index.contains_key(lsn) && bdy <= lsn, |lsn| lsn_au_index[lsn])
}

pub proof fn lsn_au_index_discard_up_to_ensures(lsn_au_index: LsnAUIndex, bdy: LSN)
    ensures
        ({
            let out = lsn_au_index_discard_up_to(lsn_au_index, bdy);
            &&& out <= lsn_au_index
            &&& forall|k|
                out.contains_key(k) ==> bdy <= k
                &&& forall|k| lsn_au_index.contains_key(k) && bdy <= k ==> out.contains_key(k)
        }),
{
}

// TODO(jonh): duplicates text in LikesJournal_v. Eww.
pub open spec(checked) fn singleton_index(start_lsn: LSN, end_lsn: LSN, value: AU) -> (index:
    LsnAUIndex) {
    Map::new(|lsn| start_lsn <= lsn < end_lsn, |lsn| value)
}

// Update lsnAUIndex with additional lsn's from a new record
pub open spec(checked) fn lsn_au_index_append_record(
    lsn_au_index: LsnAUIndex,
    msgs: MsgHistory,
    au: AU,
) -> (out: LsnAUIndex)
    recommends
        msgs.wf(),
        msgs.seq_start < msgs.seq_end,  // nonempty history
// ensures LinkedJournal::lsn_disjoint(lsn_au_index.dom(), msgs)
//      ==> out.values() == lsn_au_index.values() + set![au]

{
    // msgs is complete map from seqStart to seqEnd
    let update = singleton_index(msgs.seq_start, msgs.seq_end, au);
    let out = lsn_au_index.union_prefer_right(update);
    // assertion here in dafny original
    out
}

pub open spec(checked) fn contiguous_lsns(
    lsn_au_index: LsnAUIndex,
    lsn1: LSN,
    lsn2: LSN,
    lsn3: LSN,
) -> bool {
    ({
        &&& lsn1 <= lsn2 <= lsn3
        &&& lsn_au_index.contains_key(lsn1)
        &&& lsn_au_index.contains_key(lsn3)
        &&& lsn_au_index[lsn1] == lsn_au_index[lsn3]
    }) ==> {
        &&& lsn_au_index.contains_key(lsn2)
        &&& lsn_au_index[lsn1] == lsn_au_index[lsn2]
    }
}

pub open spec(checked) fn aus_hold_contiguous_lsns(lsn_au_index: LsnAUIndex) -> bool {
    forall|lsn1, lsn2, lsn3| contiguous_lsns(lsn_au_index, lsn1, lsn2, lsn3)
}

pub open spec(checked) fn au_addrs_past_pointer(ptr: Pointer) -> Set<Address> {
    if ptr is None {
        Set::empty()
    } else {
        Set::new(|addr: Address| ptr.unwrap().after_page(addr))
    }
}

impl DiskView {
    pub open spec fn tight_domain(self, index: LsnAUIndex, root: Pointer) -> Set<Address>
    {
        Set::new( |addr: Address| {
                &&& self.entries.contains_key(addr) 
                &&& index.values().contains(addr.au) 
                &&& !au_addrs_past_pointer(root).contains(addr)
            }
        )
    }

    pub open spec fn domain_tight_wrt_index(self, index: LsnAUIndex, root: Pointer) -> bool {
        forall|addr|
            #[trigger] self.entries.dom().contains(addr) ==> {
                &&& index.values().contains(addr.au)
                &&& root is Some ==> !root.unwrap().after_page(addr)
            }
    }

    pub open spec fn bounded_inactive_lsns(self, index: LsnAUIndex, root: Pointer) -> bool {
        forall|addr, lsn|
            ({
                &&& self.entries.dom().contains(addr)
                &&& self.entries[addr].message_seq.contains(lsn)
                &&& index.values().contains(addr.au) 
                &&& !index.contains_key(lsn)
                &&& root is Some ==> !root.unwrap().after_page(addr)
            }) ==> lsn < self.boundary_lsn
    }

    #[verifier(opaque)]
    pub closed spec(checked) fn index_keys_exist_valid_entries(
        self,
        lsn_au_index: LsnAUIndex,
    ) -> bool
        recommends
            self.wf(),
    {
        forall|lsn|
            #[trigger]
            lsn_au_index.contains_key(lsn) ==> exists|addr: Address|
                addr.wf() && addr.au == lsn_au_index[lsn] && #[trigger]
                self.addr_supports_lsn(addr, lsn)
    }

    // one-off explicit instantiation lemma for use in predicates where reveal is verboten.
    pub proof fn instantiate_index_keys_exist_valid_entries(
        self,
        lsn_au_index: LsnAUIndex,
        lsn: LSN,
    ) -> (addr: Address)
        requires
            self.wf(),
            lsn_au_index.contains_key(lsn),
            self.index_keys_exist_valid_entries(lsn_au_index),
        ensures
            addr.wf(),
            lsn_au_index[lsn] == addr.au,
            self.addr_supports_lsn(addr, lsn),
    {
        reveal(DiskView::index_keys_exist_valid_entries);
        let addr = choose|addr: Address|
            addr.wf() && addr.au == lsn_au_index[lsn] && #[trigger]
            self.addr_supports_lsn(addr, lsn);
        addr
    }

    pub open spec(checked) fn build_lsn_au_index_page_walk(self, root: Pointer) -> LsnAUIndex
        recommends
            self.decodable(root),
            self.acyclic(),
        decreases
            self.the_rank_of(root),  // TODO(chris): this when clause isn't working!
        when {
            // TODO(chris): oh look, &&&s not ,s! Let's run with that!
            &&& self.decodable(root)
            &&& self.acyclic()
        }
    {
        if root is None {
            Map::empty()
        } else {
            let curr_msgs = self.entries[root.unwrap()].message_seq;
            let update = singleton_index(
                math::max(self.boundary_lsn as int, curr_msgs.seq_start as int) as nat,
                curr_msgs.seq_end,
                root.unwrap().au,
            );
            self.build_lsn_au_index_page_walk(self.next(root)).union_prefer_right(update)
        }
    }

    // I think you could prove this by connecting from page_walk to au_walk, thence to
    // lsn_addr_index, thence via index_domain_valid. But... ew.
    pub proof fn build_lsn_au_index_page_walk_domain(self, root: Pointer)
        requires
            self.decodable(root),
            self.acyclic(),
        ensures
            forall|lsn|
                self.build_lsn_au_index_page_walk(root).contains_key(lsn) <==> (self.tj_at(
                    root,
                ).seq_start() <= lsn < self.tj_at(root).seq_end()),
        decreases self.the_rank_of(root),
    {
        // TODO(chris) Another great application of spec ensures. (Also frustrating absence; spent
        // a dozen lines discovering the trigger on top of the dozen lines setting this silly thing
        // up)
        if root is Some {
            self.build_lsn_au_index_page_walk_domain(self.next(root));
            let prior_result = self.build_lsn_au_index_page_walk(self.next(root));  // trigger mctriggerface that we'd get for free in spec ensures
        }
    }

    pub proof fn build_lsn_au_index_page_walk_exist_valid_entries(self, root: Pointer)
        requires
            self.decodable(root),
            self.acyclic(),
            self.wf_addrs(),
        ensures
            self.index_keys_exist_valid_entries(self.build_lsn_au_index_page_walk(root)),
        decreases self.the_rank_of(root),
    {
        reveal(DiskView::index_keys_exist_valid_entries);
        if root is Some {
            let curr_msgs = self.entries[root.unwrap()].message_seq;
            let update = singleton_index(
                math::max(self.boundary_lsn as int, curr_msgs.seq_start as int) as nat,
                curr_msgs.seq_end,
                root.unwrap().au,
            );
            assert forall|lsn| update.contains_key(lsn) implies exists|addr: Address|
                addr.wf() && addr.au == update[lsn] && #[trigger]
                self.addr_supports_lsn(addr, lsn) by {
                assert(self.addr_supports_lsn(root.unwrap(), lsn));
            }
//            assert(self.index_keys_exist_valid_entries(update));
            self.build_lsn_au_index_page_walk_exist_valid_entries(self.next(root));
        }
    }

    #[verifier(decreases_by)]
    pub proof fn build_lsn_au_index_au_walk_helper(self, root: Pointer, first: AU) {
        match root {
            None => {},
            Some(addr) => {
                if addr.au == first {
                } else {
                    // Nine lines of boilerplate to insert this one line in the right place. :v/
                    let bottom = first_page(root);
                    self.bottom_properties(root, first);
                    self.transitive_ranking(bottom.unwrap(), root.unwrap(), first);
                }
            },
        }
    }

    pub open spec   /*(checked)*/
    fn build_lsn_au_index_au_walk(self, root: Pointer, first: AU) -> LsnAUIndex
        recommends
            self.pointer_is_upstream(root, first),
            self.acyclic(),
            self.internal_au_pages_fully_linked(),
        decreases self.the_rank_of(root),
    {
        // NOTE(Jialin): if we don't take the root is Some into account when writing the decreases when,
        // verifier can't seem to infer that root is None is the base case and returns map![]
        // unable to prove that calling this with None returns an empty map without changes to the decreases when
        decreases_when(
            {
                root is Some ==> ({
                    &&& self.pointer_is_upstream(root, first)
                    &&& self.acyclic()
                    &&& self.internal_au_pages_fully_linked()
                })
            },
        );
        decreases_by(Self::build_lsn_au_index_au_walk_helper);
        match root {
            None => map![],
            Some(addr) => {
                if addr.au == first {
                    self.build_lsn_au_index_page_walk(root)
                } else {
                    // Jump over all the intermediate pages in the AU; we know how they're laid out already.
                    let bottom = first_page(root);
                    let last_lsn = self.entries[root.unwrap()].message_seq.seq_end;
                    let first_lsn = self.entries[bottom.unwrap()].message_seq.seq_start;
                    let update = singleton_index(first_lsn, last_lsn, bottom.unwrap().au);
                    let prior_result = self.build_lsn_au_index_au_walk(self.next(bottom), first);
                    prior_result.union_prefer_right(update)
                }
            },
        }
    }

    pub proof fn build_lsn_au_index_equiv_page_walk(self, root: Pointer, first: AU)
        requires
            self.pointer_is_upstream(root, first)
        ensures
            self.build_lsn_au_index_au_walk(root, first) =~= self.build_lsn_au_index_page_walk(
                root,
            ),
        decreases self.the_rank_of(root),
    {
        match root {
            None => {},
            Some(addr) => {
                if addr.au == first {
                } else {
                    self.build_lsn_au_index_equiv_page_walk(self.next(root), first);
                    // TODO(andrea): rediscovering this is brutal. I copy-pasted the definition
                    // three times before realizing I hadn't satisfied decreases_by. This should
                    // have been dispatched in the spec fn.  Aaargh.
                    self.bottom_properties(root, first);
                    //                     let bottom = first_page(root);
                    //                     let last_lsn = dv.entries[root.unwrap()].message_seq.seq_end;
                    //                     let first_lsn = dv.entries[bottom.unwrap()].message_seq.seq_start;
                    //                     let update = singleton_index(first_lsn, last_lsn, bottom.unwrap().au);
                    //                     let prior_result = Self::build_lsn_au_index_au_walk(dv, dv.next(bottom), first);
                    //                     let output = prior_result.union_prefer_right(update);
                    //                     assert( output == Self::build_lsn_au_index_au_walk(dv, root, first) );
                    if 0 < root.unwrap().page {  // zero case is easy; au-walk and page-walk do the same thing
                        assert(self.next(root) is Some) by   /*contradiction*/ {
                            if self.next(root) is None {
                                assert(self.addr_supports_lsn(root.unwrap(), self.boundary_lsn));  // witness
//                                assert(false);
                            }
                        }
                        self.bottom_properties(self.next(root), first);
                    }
                }
            },
        }
    }

    pub proof fn build_lsn_au_index_page_walk_sub_disk(self, big: DiskView, root: Pointer)
        requires
            self.decodable(root),
            big.decodable(root),
            big.acyclic(),
            self.is_sub_disk_with_newer_lsn(big),
        ensures
            self.build_lsn_au_index_page_walk(root) <= big.build_lsn_au_index_page_walk(root),
            self.is_sub_disk(big) ==> self.build_lsn_au_index_page_walk(root) == big.build_lsn_au_index_page_walk(root)
        decreases self.the_rank_of(root),
    {
        assert forall|addr|
            self.entries.contains_key(addr) ==> big.entries.contains_key(
                addr,
            ) by {}  // trigger for ranking

        assert(self.valid_ranking(big.the_ranking()));
        if root is Some {
            self.build_lsn_au_index_page_walk_sub_disk(big, self.next(root));
            self.build_lsn_au_index_page_walk_domain(self.next(root));
        }
    }

    pub proof fn build_commutes_over_append_record(
        self,
        root: Pointer,
        msgs: MsgHistory,
        new_addr: Address,
    )
        requires
            self.tj_at(root).decodable(),
            self.tj_at(root).seq_end() == msgs.seq_start,
            msgs.wf(),
            !msgs.is_empty(),
            !self.entries.contains_key(new_addr),
        ensures
            ({
                let old_au_idx = self.build_lsn_au_index_page_walk(root);  // super-let, please
                let au_update = singleton_index(msgs.seq_start, msgs.seq_end, new_addr.au);
                let incremental_idx = old_au_idx.union_prefer_right(au_update);
                let appended_tj = self.tj_at(root).append_record(new_addr, msgs);
                let built_idx = appended_tj.disk_view.build_lsn_au_index_page_walk(
                    appended_tj.freshest_rec,
                );
                incremental_idx
                    =~= built_idx  // remember, kids, the tilde is a proof strategy!

            }),
        decreases self.the_rank_of(root),
    {
        let appended_tj = self.tj_at(root).append_record(new_addr, msgs);
        assert(appended_tj.disk_view.valid_ranking(self.tj_at(root).marshal_ranking(new_addr)));  // witness to acyclic
        self.build_lsn_au_index_page_walk_sub_disk(appended_tj.disk_view, root);
    }

    pub proof fn bottom_properties(self, root: Pointer, first: AU)
        requires
            self.pointer_is_upstream(root, first),
            root is Some,
            root.unwrap().au != first,
        ensures  // TODO wish I had a superlet for bottom=first_page(root) here

            self.next(first_page(root)) is Some,  // else root.au == first
            self.decodable(self.next(first_page(root))),  // because decodable-ity is recursive
            self.buildable(self.next(first_page(root))),
            // a couple uglies I threw in to complete lemma_aus_hold_contiguous_lsns
            self.pointer_is_upstream(first_page(root), first),
            self.tj_at(self.next(first_page(root))).seq_end() <= self.tj_at(root).seq_end(),
        decreases self.the_rank_of(root),
    {
        if self.next(root) is None {
            assert(self.addr_supports_lsn(root.unwrap(), self.boundary_lsn));
//            assert(false);
        }
        if root.unwrap().page != 0 {
            //             assert( dv.entries.contains_key(first_page(root).unwrap()) );
            //             assert( Self::au_page_links_to_prior(dv, root.unwrap()) );
            self.bottom_properties(self.next(root), first);
        }
    }

    pub open spec(checked) fn upstream(self, addr: Address) -> bool {
        &&& self.entries.contains_key(addr)
        &&& self.boundary_lsn < self.entries[addr].message_seq.seq_end
    }

    // NB talking about dv.next() is painful because we have to reason about interactions
    // with a moving dv.boundary. Maybe easier to break down the reasoning into pointers
    // (which don't change) and layer the boundary reasoning on top.
    pub open spec(checked) fn nonzero_pages_point_backward(self) -> bool
        recommends
            self.wf(),
    {
        forall|addr: Address|
            #![auto]
            ({
                &&& addr.page != 0
                &&& self.entries.contains_key(addr)
            }) ==> self.entries[addr].prior_rec == Some(addr.previous())
    }

    // Profiling suggested this quantifier is trigger happy
    // Changing from close to open bc we need it in the refinement proof
    #[verifier(opaque)]
    pub open spec(checked) fn pages_allocated_in_lsn_order(self) -> bool
        recommends
            self.wf(),
    {
        forall|alo: Address, ahi: Address|
            #![auto]
            ({
                &&& alo.au == ahi.au
                &&& alo.page < ahi.page
                &&& self.entries.contains_key(alo)
                &&& self.entries.contains_key(ahi)
            }) ==> self.entries[alo].message_seq.seq_end <= self.entries[ahi].message_seq.seq_start
    }

    pub open spec(checked) fn internal_au_pages_fully_linked(self) -> bool
        recommends
            self.wf(),
    {
        &&& self.nonzero_pages_point_backward()
        &&& self.pages_allocated_in_lsn_order()
    }

    pub proof fn nonfirst_properties(self, root: Pointer, first: AU)
        requires
            self.pointer_is_upstream(root, first),
            root is Some,
            root.unwrap().au != first,
        ensures
            forall|ptr: Pointer|
                #![auto]
                ptr is Some && ptr.unwrap().au == root.unwrap().au && ptr.unwrap().page
                    <= root.unwrap().page ==> self.pointer_is_upstream(ptr, first),
            forall|ptr: Pointer|
                #![auto]
                ptr is Some && ptr.unwrap().au == root.unwrap().au && 0 < ptr.unwrap().page
                    <= root.unwrap().page ==> self.next(ptr) is Some && self.next(ptr).unwrap().au
                    == root.unwrap().au,
        decreases self.the_rank_of(root),
    {
        if self.next(root) is None {
            assert(self.addr_supports_lsn(root.unwrap(), self.boundary_lsn));
//            assert(false);
        }
        if root.unwrap().page != 0 {
            self.nonfirst_properties(self.next(root), first);
        }
    }

    pub proof fn transitive_ranking(self, root: Address, later: Address, first: AU)
        requires
            self.pointer_is_upstream(Some(later), first),
            self.decodable(Some(root)),
            self.acyclic(),
            root.au != first,
            root.au == later.au,
            root.page <= later.page,
            self.internal_au_pages_fully_linked(),  // should be less than <= bc it's enough to prove termination, cause later is already < caller's root

        ensures
            self.the_rank_of(Some(root)) <= self.the_rank_of(Some(later)),
        decreases later.page,
    {
        if root == later {
//            assert(self.decodable(Some(later)));
            return ;
        }//Self::nonfirst_decodable(dv, Some(later), first);

        let prior = self.next(Some(later));
        //         assert( dv.entries.contains_key(later) );    // todo deleteme
        //         assert( dv.entries[later].prior_rec is Some );
        //         assert( prior is Some );
        //         assert( prior.unwrap().page + 1 == later.page );
        self.nonfirst_properties(Some(later), first);
        self.transitive_ranking(root, prior.unwrap(), first);
    }

    pub open spec fn has_unique_lsns(self) -> bool {
        forall|lsn, addr1, addr2|
            self.addr_supports_lsn(addr1, lsn) && self.addr_supports_lsn(addr2, lsn) ==> addr1
                == addr2
    }

    pub open spec fn pointer_is_upstream(self, root: Pointer, first: AU) -> bool {
        &&& self.decodable(root)
        &&& self.acyclic()
        &&& self.internal_au_pages_fully_linked()
        &&& self.has_unique_lsns()
        &&& root is Some ==> self.valid_first_au(first)
        &&& root is Some ==> self.upstream(root.unwrap())
    }

    pub open spec(checked) fn wf_addrs(self) -> bool {
        forall|addr| #[trigger] self.entries.contains_key(addr) ==> addr.wf()
    }

    pub open spec(checked) fn valid_first_au(self, first: AU) -> bool {
        exists|addr: Address|
            #![auto]
            addr.au == first && self.addr_supports_lsn(addr, self.boundary_lsn)
    }

    pub proof fn lemma_aus_hold_contiguous_lsns(self, root: Pointer, first: AU)
        requires
            self.pointer_is_upstream(root, first),
        ensures
            self.tj_at(root).au_domain_valid(self.build_lsn_au_index_au_walk(root, first)),
            aus_hold_contiguous_lsns(self.build_lsn_au_index_au_walk(root, first)),
        decreases self.the_rank_of(root),
    {
        let lsn_au_index = self.build_lsn_au_index_au_walk(root, first);
        match root {
            None => {},
            Some(addr) => {
                if addr.au == first {
                    self.lemma_aus_hold_contiguous_lsns_first_page(root, first);
                } else {
                    let bottom = first_page(root);
                    //                     let last_lsn = dv.entries[root.unwrap()].message_seq.seq_end;
                    let first_lsn = self.entries[bottom.unwrap()].message_seq.seq_start;
                    //                     let update = singleton_index(first_lsn, last_lsn, bottom.unwrap().au);
                    let prior_result = self.build_lsn_au_index_au_walk(self.next(bottom), first);
                    self.bottom_properties(root, first);
                    self.transitive_ranking(bottom.unwrap(), root.unwrap(), first);
                    self.lemma_aus_hold_contiguous_lsns(self.next(bottom), first);
                    assert forall|lsn1, lsn2, lsn3|
                        contiguous_lsns(lsn_au_index, lsn1, lsn2, lsn3) by {
                        if ({
                            &&& lsn1 <= lsn2 <= lsn3
                            &&& lsn_au_index.contains_key(lsn1)
                            &&& lsn_au_index.contains_key(lsn3)
                            &&& lsn_au_index[lsn1] == lsn_au_index[lsn3]
                        }) {
                            if lsn1 < first_lsn {  // recursive case
                                if !prior_result.contains_key(lsn3)  {  // lsn3 is in bottom.au, tho? Nope.
                                    self.lemma_next_au_doesnt_intersect(root, first, prior_result);
//                                    assert(false);
                                }
                                assert(contiguous_lsns(prior_result, lsn1, lsn2, lsn3));  // trigger
                            }
                        }
                    }
                }
            },
        }
    }

    pub closed spec(checked) fn index_honors_rank(
        self,
        root: Pointer,
        first: AU,
        au_index: LsnAUIndex,
    ) -> bool
        recommends
            self.decodable(root),
            self.acyclic(),
            self.internal_au_pages_fully_linked(),
    {
        forall|lsn, addr: Address|
            #![auto]
            au_index.contains_key(lsn) && addr.au == au_index[lsn] && self.addr_supports_lsn(
                addr,
                lsn,
            ) ==> self.the_rank_of(Some(addr)) <= self.the_rank_of(root)
    }

    pub proof fn nonfirst_pages(self, addr: Address, first: AU)
        requires
            self.pointer_is_upstream(Some(addr), first),
            addr.au != first,
        ensures
            self.boundary_lsn < self.entries[addr].message_seq.seq_start,
    {
        // assert( dv.boundary_lsn < dv.entries[addr].message_seq.seq_end );  // documentation; by pointer_is_upstream
        if self.entries[addr].message_seq.seq_start <= self.boundary_lsn {
            assert(self.addr_supports_lsn(addr, self.boundary_lsn));  // trigger
            //            assert( Self::valid_first_au(dv, addr.au) );  // documentation
            //            assert( Self::valid_first_au(dv, first) );    // documentation
//            assert(false);  // lsns unique
        }
    }

    pub proof fn build_lsn_addr_index_returns_upstream_pages(self, root: Pointer, first: AU)
        requires
            self.has_unique_lsns(),
            self.internal_au_pages_fully_linked(),
            self.buildable(root),
            self.valid_first_au(first),
        ensures
            ({
                let lsn_addr_index = self.build_lsn_addr_index(root);
                forall|lsn|
                    #![auto]
                    lsn_addr_index.contains_key(lsn) && lsn_addr_index[lsn].au != first
                        ==> self.pointer_is_upstream(Some(lsn_addr_index[lsn]), first)
            }),
        decreases self.the_rank_of(root),  // when self.buildable(root)

    {
        let lsn_addr_index = self.build_lsn_addr_index(root);
        if root is Some {
            self.build_lsn_addr_index_returns_upstream_pages(self.next(root), first);
            // ugly trigger block. want to just trigger on alpha-substituted definition of build_lsn_addr_index
            let curr_msgs = self.entries[root.unwrap()].message_seq;
            let start_lsn = math::max(self.boundary_lsn as int, curr_msgs.seq_start as int) as nat;
            let update = LikesJournal_v::singleton_index(
                start_lsn,
                curr_msgs.seq_end,
                root.unwrap(),
            );
            assert(lsn_addr_index == self.build_lsn_addr_index(self.next(root)).union_prefer_right(
                update,
            ));
            //             assert forall |lsn| lsn_addr_index.contains_key(lsn) && lsn_addr_index[lsn].au != first
            //             implies Self::pointer_is_upstream(dv, Some(lsn_addr_index[lsn]), first) by {
            // // //                 if update.contains_key(lsn) {
            // // //                 //if dv.build_lsn_addr_index(dv.next(root)).contains_key(lsn) {
            // // //                     assert( lsn_addr_index[lsn] == root.unwrap() );
            // // //                     assert( Self::pointer_is_upstream(dv, Some(lsn_addr_index[lsn]), first) );
            // // //                 } else {
            // // //                     assert( dv.build_lsn_addr_index(dv.next(root)).contains_key(lsn) );
            // // //                     assert( dv.build_lsn_addr_index(dv.next(root))[lsn] ==
            // // //                             lsn_addr_index[lsn] );
            // // //                     assert( dv.build_lsn_addr_index(dv.next(root))[lsn].au != first );
            // // //                     assert( Self::pointer_is_upstream(dv, Some(lsn_addr_index[lsn]), first) );
            // // //                 }
            //             }
        }
    }

    pub proof fn upstream_pages(self, earlier: Address, later: Address, first: AU)
        requires
            self.pointer_is_upstream(Some(later), first),
            later.au != first,
            earlier.au == later.au,
            earlier.page <= later.page,
        ensures
            self.pointer_is_upstream(Some(earlier), first),
        decreases later.page - earlier.page,
    {
        if earlier.page < later.page {
            let prior = later.previous();
            self.nonfirst_pages(later, first);
//            assert(self.upstream(prior));
//            assert(self.pointer_is_upstream(Some(prior), first));
            self.upstream_pages(earlier, prior, first);
        }
    }

    pub proof fn lemma_next_au_doesnt_intersect(
        self,
        root: Pointer,
        first: AU,
        prior_result: LsnAUIndex,
    )
        requires
            self.pointer_is_upstream(root, first),
            root is Some,
            root.unwrap().au != first,
            prior_result == self.build_lsn_au_index_au_walk(self.next(first_page(root)), first),
        ensures
            forall|lsn|
                #![auto]
                prior_result.contains_key(lsn) ==> prior_result[lsn] != root.unwrap().au,
    {
        let bottom = first_page(root);
        let prior_addr_index = self.tj_at(self.next(bottom)).build_lsn_addr_index();
        self.bottom_properties(root, first);
        self.build_lsn_addr_all_decodable(self.next(bottom));
        self.build_lsn_au_index_equiv_page_walk(self.next(bottom), first);
        self.build_lsn_au_index_page_walk_consistency(self.next(bottom));
        self.build_lsn_addr_index_returns_upstream_pages(self.next(bottom), first);
        assert forall|lsn| prior_result.contains_key(lsn) implies #[trigger]
        prior_result[lsn] != root.unwrap().au by {
            let addr = prior_addr_index[lsn];
            if addr.au == root.unwrap().au {
                if addr.au != first {
                    let addr0 = Address { au: addr.au, page: 0 };
                    let addrp = self.next(bottom).unwrap();
                    self.upstream_pages(addr0, addr, first);
                    self.transitive_ranking(addr0, addr, first);
                    let prior_last = (self.entries[addrp].message_seq.seq_end - 1) as nat;
                    assert(lsn <= prior_last) by {
                        reveal(TruncatedJournal::index_domain_valid);
                        self.build_lsn_addr_index_domain_valid(self.next(bottom));
                    }
                    self.tj_at(self.next(bottom)).build_lsn_addr_honors_rank(prior_addr_index);
                    assert(prior_addr_index.contains_key(prior_last));  // trigger build_lsn_addr_honors_rank
//                    assert(false);
                }
//                assert(addr.au == first);
//                assert(false);
            }
        }
    }

    // TODO(jonh): if we had spec ensures, this would be a nice conclusion to build_lsn_au_index_page_walk
    pub proof fn au_index_page_supports_lsn(self, root: Pointer, lsn: LSN)
        requires
            self.decodable(root),
            self.acyclic(),
            self.build_lsn_au_index_page_walk(root).contains_key(lsn),
        ensures
            exists|addr|
                #![auto]
                self.addr_supports_lsn(addr, lsn) && addr.au == self.build_lsn_au_index_page_walk(
                    root,
                )[lsn],
        decreases self.the_rank_of(root),
    {
        if root is Some {
            let curr_msgs = self.entries[root.unwrap()].message_seq;
            let update = singleton_index(
                math::max(self.boundary_lsn as int, curr_msgs.seq_start as int) as nat,
                curr_msgs.seq_end,
                root.unwrap().au,
            );
            if update.contains_key(lsn) {
                assert(self.addr_supports_lsn(root.unwrap(), lsn));  // witness to ensures exists trigger
            } else {
                self.au_index_page_supports_lsn(self.next(root), lsn);
            }
        }
    }

    pub proof fn first_contains_boundary(self, root: Pointer, first: AU)
        requires
            self.decodable(root),
            self.acyclic(),
            self.valid_first_au(first),
            self.has_unique_lsns(),
            root is Some,
            self.upstream(root.unwrap()),
        ensures
            self.build_lsn_au_index_page_walk(root)[self.boundary_lsn] == first,
    {
        let addr = choose|addr: Address|
            #![auto]
            addr.au == first && self.addr_supports_lsn(addr, self.boundary_lsn);
        self.build_lsn_au_index_page_walk_domain(root);
        self.au_index_page_supports_lsn(root, self.boundary_lsn);
    }

    pub proof fn lemma_aus_hold_contiguous_lsns_first_page(self, root: Pointer, first: AU)
        requires
            self.pointer_is_upstream(root, first),
            self.has_unique_lsns(),
            root is Some,
            root.unwrap().au == first,
        ensures
            ({
                // TODO sure want that super-let here, for lsn_au_index.
                let lsn_au_index = self.build_lsn_au_index_page_walk(root);
                &&& forall|lsn|
                    #![auto]
                    lsn_au_index.contains_key(lsn) ==> lsn_au_index[lsn] == root.unwrap().au
                    &&& self.tj_at(root).au_domain_valid(lsn_au_index)
                    &&& aus_hold_contiguous_lsns(lsn_au_index)
            }),
        decreases self.the_rank_of(root),
    {
        let lsn_au_index = self.build_lsn_au_index_page_walk(root);
        if root is None {
        } else if self.next(root) is None {
            assert(self.build_lsn_au_index_page_walk(self.next(root)) =~= Map::empty());  // trigger
        } else if root.unwrap().page == 0 {
            // If there's a valid pointer exiting here, and we're at page 0, then we're not the
            // first au, are we?
            //assert( dv.addr_supports_lsn(lsn_au_index[dv.boundary_lsn], dv.boundary_lsn) );
//            assert(exists|addr: Address|
//                #![auto]
//                addr.au == first && self.addr_supports_lsn(addr, self.boundary_lsn));
            let first_page = choose|addr: Address|
                #![auto]
                addr.au == first && self.addr_supports_lsn(addr, self.boundary_lsn);
//            assert(self.addr_supports_lsn(first_page, self.boundary_lsn));
            self.first_contains_boundary(root, first);
//            assert(lsn_au_index[self.boundary_lsn] == first);
            assert(self.entries[root.unwrap()].message_seq.seq_end
                <= self.entries[first_page].message_seq.seq_start) by {
                reveal(DiskView::pages_allocated_in_lsn_order);
            }
//            assert(false);
        } else {
            self.lemma_aus_hold_contiguous_lsns_first_page(self.next(root), first);  // recurse!
        }
    }

    pub proof fn addr_supports_lsn_consistent_with_index(self, index: LsnAUIndex, lsn: LSN, addr: Address)
        requires
            self.wf(),
            self.wf_addrs(),
            self.has_unique_lsns(),
            self.index_keys_exist_valid_entries(index),
            self.addr_supports_lsn(addr, lsn),
            index.contains_key(lsn),
        ensures
            index[lsn] == addr.au
    {
        let _ = self.instantiate_index_keys_exist_valid_entries(index, lsn);
    }
}

impl TruncatedJournal {
    pub open spec fn au_domain_valid(self, lsn_au_index: LsnAUIndex) -> bool {
        forall|lsn| lsn_au_index.contains_key(lsn) <==> (self.seq_start() <= lsn < self.seq_end())
    }

    pub open spec fn discard_old_tight(
        self,
        start_lsn: LSN,
        keep_addrs: Set<Address>,
        new: Self,
    ) -> bool
        recommends
            self.wf(),
    {
        &&& self.discard_old_cond(start_lsn, keep_addrs, new)
        &&& keep_addrs =~= new.disk_view.entries.dom()
    }

    #[verifier(recommends_by)]
    pub proof fn build_lsn_au_index_helper(self, first: AU) {
        match self.freshest_rec {
            None => {},
            Some(addr) => {
                if addr.au == first {
                } else {
                    self.disk_view.bottom_properties(self.freshest_rec, first);
                    self.disk_view.transitive_ranking(
                        self.freshest_rec.unwrap().first_page(),
                        self.freshest_rec.unwrap(),
                        first,
                    );
                }
            },
        }
    }

    pub open spec(checked) fn build_lsn_au_index(self, first: AU) -> LsnAUIndex
        recommends
            self.disk_view.pointer_is_upstream(self.freshest_rec, first),
    {
        recommends_by(Self::build_lsn_au_index_helper);
        self.disk_view.build_lsn_au_index_au_walk(self.freshest_rec, first)
    }

    pub proof fn build_lsn_au_index_ensures(self, first: AU)
        requires
            self.disk_view.wf_addrs(),
            self.disk_view.pointer_is_upstream(self.freshest_rec, first),
        ensures
            ({
                let index = self.build_lsn_au_index(first);
                &&& self.au_domain_valid(index)
                &&& aus_hold_contiguous_lsns(index)
                &&& self.disk_view.index_keys_exist_valid_entries(index)
                &&& self.freshest_rec is Some ==> {
                    &&& index.contains_key(self.seq_start())
                    &&& index[self.seq_start()] == first
                }
            }),
    {
        self.disk_view.lemma_aus_hold_contiguous_lsns(self.freshest_rec, first);
        self.disk_view.build_lsn_au_index_equiv_page_walk(self.freshest_rec, first);
        self.disk_view.build_lsn_au_index_page_walk_exist_valid_entries(self.freshest_rec);
        if self.freshest_rec is Some {
            self.disk_view.first_contains_boundary(self.freshest_rec, first);
        }
    }

    pub proof fn sub_disk_build_sub_lsn_au_index(self, first: AU, big: Self, big_first: AU)
        requires
            big.disk_view.wf_addrs(),
            big.disk_view.pointer_is_upstream(big.freshest_rec, big_first),
            self.disk_view.pointer_is_upstream(self.freshest_rec, first),
            self.disk_view.is_sub_disk(big.disk_view) || self.disk_view.is_sub_disk_with_newer_lsn(
                big.disk_view,
            ),
            self.seq_end() <= big.seq_end(),
        ensures
            self.build_lsn_au_index(first) <= big.build_lsn_au_index(big_first),
    {
        let index = self.build_lsn_au_index(first);
        let big_index = big.build_lsn_au_index(big_first);

        assert forall|addr| self.disk_view.entries.contains_key(addr) 
            ==> big.disk_view.entries.contains_key(addr) by {}
//        assert(self.disk_view.wf_addrs());

        self.build_lsn_au_index_ensures(first);
        big.build_lsn_au_index_ensures(big_first);
        assert(index.dom() <= big_index.dom());

        assert forall|lsn| index.contains_key(lsn) 
        implies #[trigger] index[lsn] == big_index[lsn] by {
            reveal(DiskView::index_keys_exist_valid_entries);
            let addr = choose|addr: Address|
                addr.wf() && addr.au == index[lsn] && #[trigger]
                self.disk_view.addr_supports_lsn(addr, lsn);
            assert(big.disk_view.addr_supports_lsn(addr, lsn));
        }
    }

    pub open spec(checked) fn valid_structure(self, index: LsnAUIndex, first: AU) -> bool {
        &&& self.wf()
        &&& self.disk_view.wf_addrs()
        &&& self.disk_view.pointer_is_upstream(self.freshest_rec, first)
        &&& self.disk_view.bounded_inactive_lsns(index, self.freshest_rec)
        &&& index == self.build_lsn_au_index(first)
    }

    pub open spec(checked) fn valid_subrange(self, index: LsnAUIndex, first: AU,
        sub_start: LSN, sub_freshest_rec: Pointer, sub_first: AU) -> bool
        recommends self.valid_structure(index, first)
    {
        let dv = self.disk_view;
        let sub_tj = dv.tj_at(sub_freshest_rec);

        &&& self.seq_start() <= sub_start
        &&& dv.decodable(sub_freshest_rec)
        &&& sub_freshest_rec is Some ==> sub_tj.seq_end() <= self.seq_end()
        &&& sub_freshest_rec is Some ==> sub_start < sub_tj.seq_end()
        &&& sub_freshest_rec is Some ==> {
            &&& index.contains_key(sub_start) 
            &&& index[sub_start] == sub_first
        }
    }

    pub proof fn subrange_preserves_pointer_is_upstream(self: Self, index: LsnAUIndex, first: AU, 
        sub_start: LSN, sub_freshest_rec: Pointer, sub_first: AU)
    requires 
        self.valid_structure(index, first),
        self.valid_subrange(index, first, sub_start, sub_freshest_rec, sub_first),
    ensures 
        self.disk_view.discard_old(sub_start).pointer_is_upstream(sub_freshest_rec, sub_first)
    {
        let dv = self.disk_view;
        let sub_dv = self.disk_view.discard_old(sub_start);

//        assert(sub_dv.decodable(sub_freshest_rec));
        assert(sub_dv.valid_ranking(dv.the_ranking()));
//        assert(sub_dv.acyclic());

        assert(sub_dv.internal_au_pages_fully_linked()) by {
            reveal(DiskView::pages_allocated_in_lsn_order);
        }

        assert(sub_dv.has_unique_lsns()) by {
            assert(forall|lsn, addr| sub_dv.addr_supports_lsn(addr, lsn) 
                ==> dv.addr_supports_lsn(addr, lsn));
        }

        if sub_freshest_rec is Some {
            self.build_lsn_au_index_ensures(first);
//            assert(index.contains_key(sub_start));
            let first_addr = dv.instantiate_index_keys_exist_valid_entries(index, sub_start);
            assert(sub_dv.addr_supports_lsn(first_addr, sub_start));
        }
    }

    pub proof fn sub_disk_preserves_pointer_is_upstream(self: Self, index: LsnAUIndex, first: AU,
        sub_start: LSN, sub_freshest_rec: Pointer, sub_first: AU) -> (sub_dv: DiskView)
    requires 
        self.valid_structure(index, first),
        self.valid_subrange(index, first, sub_start, sub_freshest_rec, sub_first),
    ensures
        ({
            let dv = self.disk_view;
            let sub_end = dv.tj_at(sub_freshest_rec).seq_end();
            let sub_lsns = Set::new(|lsn| sub_start <= lsn < sub_end);
            let sub_domain = dv.tight_domain(index.restrict(sub_lsns), sub_freshest_rec);
            &&& sub_dv == DiskView{boundary_lsn: sub_start, entries: dv.entries.restrict(sub_domain)}
            &&& sub_dv.pointer_is_upstream(sub_freshest_rec, sub_first)
            &&& sub_dv.build_lsn_au_index_au_walk(sub_freshest_rec, sub_first) == index.restrict(sub_lsns)
        })
    {
        let dv = self.disk_view;
        let sub_end = dv.tj_at(sub_freshest_rec).seq_end();
        let sub_lsns = Set::new(|lsn| sub_start <= lsn < sub_end);
        let sub_index = index.restrict(sub_lsns);

        let sub_domain = dv.tight_domain(sub_index, sub_freshest_rec);
        let sub_dv = DiskView{boundary_lsn: sub_start, entries: dv.entries.restrict(sub_domain)}; 

        self.build_lsn_au_index_ensures(first);

        reveal(DiskView::pages_allocated_in_lsn_order);
        assert forall|addr| #[trigger] sub_dv.entries.contains_key(addr)
        implies sub_dv.is_nondangling_pointer(
            sub_dv.entries[addr].cropped_prior(sub_dv.boundary_lsn),
        ) by {
            let head = dv.entries[addr];
            let prior_ptr = head.cropped_prior(sub_dv.boundary_lsn);
            if prior_ptr is Some {
                if addr.au == prior_ptr.unwrap().au {
                    if addr.after_page(prior_ptr.unwrap()) {
//                        assert(false);
                    }
                } else {
                    let lsn = head.message_seq.seq_start;
                    // equivalent to dv.entries[prior_ptr.unwrap()].message_seq.seq_end
                    let prior_lsn = (lsn - 1) as nat;
//                    assert(sub_dv.boundary_lsn < lsn);
                    reveal(DiskView::index_keys_exist_valid_entries);

                    if sub_index.contains_key(lsn) {
                        assert(sub_index.contains_key(prior_lsn));
                        assert(dv.addr_supports_lsn(prior_ptr.unwrap(), prior_lsn));
//                        assert(sub_dv.is_nondangling_pointer(prior_ptr));
                    } else if index.contains_key(lsn) {
//                        assert(lsn >= sub_end);
                        let in_range = choose |in_range| #[trigger] sub_index.contains_key(in_range) && sub_index[in_range] == addr.au;
//                        assert(in_range <= prior_lsn <= lsn);
//                        assert(index.contains_key(in_range));
//                        assert(index[in_range] == addr.au);
//                        assert(index[lsn] == addr.au);
//                        assert(index[prior_lsn] == addr.au); // prior_lsn also == next_ptr.unwrap().au
//                        assert(false);
                    } else {
//                        assert(dv.entries[addr].message_seq.contains(lsn)); // trigger
//                        assert(lsn < sub_dv.boundary_lsn);
//                        assert(false);
                    }
                }
            }
        }

//        assert(sub_dv.nondangling_pointers());

        if sub_freshest_rec is Some {
            let last_lsn = (sub_end - 1) as nat;
//            assert(dv.addr_supports_lsn(sub_freshest_rec.unwrap(), last_lsn));
            dv.addr_supports_lsn_consistent_with_index(index, last_lsn, sub_freshest_rec.unwrap());
            assert(sub_index.contains_key(last_lsn)); // trigger
//            assert(sub_dv.is_nondangling_pointer(sub_freshest_rec));

            // valid first_au
//            assert(index.contains_key(sub_start));
            let first_addr = dv.instantiate_index_keys_exist_valid_entries(index, sub_start);
//            assert(first_addr.au == index[sub_start]);
            assert(sub_index.contains_key(sub_start));
            assert(sub_dv.addr_supports_lsn(first_addr, sub_start));
//            assert(sub_dv.valid_first_au(index[sub_start]));
        }

//        assert(sub_dv.decodable(sub_freshest_rec));
        assert(sub_dv.valid_ranking(dv.the_ranking()));
//        assert(sub_dv.acyclic());
//        assert(sub_dv.internal_au_pages_fully_linked());
        assert(sub_dv.has_unique_lsns()) by {
            assert(forall|lsn, addr|
                sub_dv.addr_supports_lsn(addr, lsn) ==> dv.addr_supports_lsn(addr, lsn));
        }

//        assert(sub_dv.pointer_is_upstream(sub_freshest_rec, sub_first));

        let sub_tj = TruncatedJournal{disk_view: sub_dv, freshest_rec: sub_freshest_rec};
        sub_tj.build_lsn_au_index_ensures(sub_first);
        if sub_freshest_rec is Some {
            sub_tj.sub_disk_build_sub_lsn_au_index(sub_first, self, first);
//            assert(sub_tj.build_lsn_au_index(sub_first).dom() =~= sub_index.dom());  
        }
        assert(sub_tj.build_lsn_au_index(sub_first) =~= sub_index);
        sub_dv
    }

    pub proof fn sub_disk_preserves_bounded_inactive_lsns(self: Self, index: LsnAUIndex, first: AU,
        sub_tj: Self, sub_first: AU)
    requires
        self.valid_structure(index, first),
        sub_tj.disk_view.pointer_is_upstream(sub_tj.freshest_rec, sub_first),
        self.seq_start() <= sub_tj.seq_start(),
        sub_tj.seq_end() <= self.seq_end(),
        sub_tj.disk_view.is_sub_disk_with_newer_lsn(self.disk_view),
    ensures
        sub_tj.disk_view.bounded_inactive_lsns(sub_tj.build_lsn_au_index(sub_first), sub_tj.freshest_rec)
    {
        let dv = self.disk_view;
        let sub_dv = sub_tj.disk_view;
        let sub_index = sub_tj.build_lsn_au_index(sub_first);
    
        assert(forall |addr| sub_dv.entries.contains_key(addr) ==> dv.entries.contains_key(addr));
//        assert(sub_dv.wf_addrs());

        sub_tj.build_lsn_au_index_ensures(sub_first);
        sub_tj.sub_disk_build_sub_lsn_au_index(sub_first, self, first);
//        assert(sub_index <= index);

        assert forall|addr, lsn|
            ({
                &&& sub_dv.entries.dom().contains(addr)
                &&& sub_dv.entries[addr].message_seq.contains(lsn)
                &&& sub_index.values().contains(addr.au) 
                &&& !sub_index.contains_key(lsn)
                &&& sub_tj.freshest_rec is Some ==> !sub_tj.freshest_rec.unwrap().after_page(addr)
            })
        implies lsn < sub_dv.boundary_lsn
        by {
            let in_range_lsn = choose |in_range_lsn| sub_index.contains_key(in_range_lsn) 
                && #[trigger] sub_index[in_range_lsn] == addr.au;
            assert(index.contains_key(in_range_lsn));
//            assert(index[in_range_lsn] == addr.au);
//            assert(sub_tj.freshest_rec is Some);

            if lsn >= sub_tj.seq_end() {
                let last_lsn = (sub_tj.seq_end() - 1) as nat;
                self.build_lsn_au_index_ensures(first);
//                assert(index.contains_key(last_lsn)); // trigger
//                assert(dv.entries.contains_key(sub_tj.freshest_rec.unwrap())); // trigger
                dv.addr_supports_lsn_consistent_with_index(index, last_lsn, sub_tj.freshest_rec.unwrap());
     
                assert(addr.au != sub_tj.freshest_rec.unwrap().au) by {
                    reveal(DiskView::pages_allocated_in_lsn_order);
                }

                if index.contains_key(lsn) {
//                    assert(dv.entries.contains_key(addr));
//                    assert(dv.entries[addr].contains_lsn(dv.boundary_lsn, lsn));
                    dv.addr_supports_lsn_consistent_with_index(index, lsn, addr);
                    assert(contiguous_lsns(index, in_range_lsn, last_lsn, lsn));
//                    assert(index[last_lsn] == addr.au);
//                    assert(false);
                } else {
//                    assert(self.freshest_rec is Some);
                    if self.freshest_rec.unwrap().after_page(addr) {
                        let end = (self.seq_end() - 1) as nat;
//                        assert(index.contains_key(end));
                        dv.addr_supports_lsn_consistent_with_index(index, end, self.freshest_rec.unwrap());
//                        assert(in_range_lsn <= last_lsn <= end);
                        assert(contiguous_lsns(index, in_range_lsn, last_lsn, end));
//                        assert(index[last_lsn] == addr.au);
//                        assert(false);
                    } 
//                    assert(dv.entries.dom().contains(addr)); // trigger
//                    assert(lsn < dv.boundary_lsn);
//                    assert(lsn < sub_dv.boundary_lsn);
                }
            }
        }
    }
}

impl MiniAllocator {
    // next address for root
    pub open spec(checked) fn tight_next_addr(self, root: Pointer, addr: Address) -> bool {
        &&& self.can_allocate(addr)
        &&& (self.curr is None ==> {
            &&& self.allocs[addr.au].all_pages_free()
            &&& addr.page == 0
        })
        &&& (self.curr is Some && root is Some ==> addr == root.unwrap().next())
    }
}

state_machine!{ AllocationJournal {
    fields {
        pub journal: LinkedJournal::State,

        // lsnAUAddrIndex maps in-repr lsn's to their AU addr
        pub lsn_au_index: LsnAUIndex,

        // AU containing the first journal record, boundarylsn can be found somewhere in this AU
        // (We only record the AU here because that's what the implementation can efficiently
        // recover from lsn_au_index at discard time.)
        pub first: AU,

        pub mini_allocator: MiniAllocator,
    }

    pub enum Label
    {
        ReadForRecovery{messages: MsgHistory},
        FreezeForCommit{frozen_journal: JournalImage},
        QueryEndLsn{end_lsn: LSN},
        Put{messages: MsgHistory},
        DiscardOld{start_lsn: LSN, require_end: LSN, deallocs: Set<AU>},
        InternalAllocations{allocs: Set<AU>, deallocs: Set<AU>},
    }

    pub open spec(checked) fn linked_lbl(lbl: Label) -> LinkedJournal::Label {
        match lbl {
            Label::ReadForRecovery{messages} =>
                LinkedJournal::Label::ReadForRecovery{messages},
            Label::FreezeForCommit{frozen_journal} =>
                LinkedJournal::Label::FreezeForCommit{frozen_journal: frozen_journal.tj},
            Label::QueryEndLsn{end_lsn} =>
                LinkedJournal::Label::QueryEndLsn{end_lsn},
            Label::Put{messages} =>
                LinkedJournal::Label::Put{messages},
            Label::DiscardOld{start_lsn, require_end, deallocs} =>
                LinkedJournal::Label::DiscardOld{start_lsn, require_end},
            Label::InternalAllocations{allocs, deallocs} =>
                LinkedJournal::Label::Internal{},
        }
    }

    pub open spec(checked) fn wf(self) -> bool {
        &&& self.journal.wf()
        &&& self.tj().disk_view.wf_addrs()
        &&& self.mini_allocator.wf()
    }

    pub open spec(checked) fn accessible_aus(self) -> Set<AU> {
        self.lsn_au_index.values() + self.mini_allocator.allocs.dom()
    }

    transition!{ read_for_recovery(lbl: Label) {
        require lbl is ReadForRecovery;
        require LinkedJournal_v::LinkedJournal::State::next(pre.journal, pre.journal, Self::linked_lbl(lbl));
    } }

    // nat exists to force page record granularity for the end
    // can't specify arbitrary lsn end
    transition!{ freeze_for_commit(lbl: Label, depth: nat) {
        require lbl is FreezeForCommit;

        let frozen_journal = lbl->frozen_journal;
        let new_bdy = frozen_journal.tj.seq_start();

        require pre.tj().disk_view.can_crop(pre.tj().freshest_rec, depth);
        let cropped_tj = pre.tj().crop(depth);

        // figure out the frozen lsn range
        require cropped_tj.can_discard_to(new_bdy);
        let post_discard = cropped_tj.discard_old(new_bdy);
        let frozen_lsns = Set::new(|lsn: LSN| new_bdy <= lsn && lsn < post_discard.seq_end());
        let frozen_index = pre.lsn_au_index.restrict(frozen_lsns);
        // we can leave in pages prior to first
        // but can't keep pages beyond freshest rec in our frozen domain
        let frozen_addrs = cropped_tj.disk_view.tight_domain(frozen_index, frozen_journal.tj.freshest_rec);

        require cropped_tj.discard_old_tight(new_bdy, frozen_addrs, frozen_journal.tj);
        require frozen_journal.first == Self::new_first(frozen_journal.tj, pre.lsn_au_index, new_bdy);
    } }

    transition!{ query_end_lsn(lbl: Label) {
        require lbl is QueryEndLsn;
        require LinkedJournal_v::LinkedJournal::State::next(pre.journal, pre.journal, Self::linked_lbl(lbl));
    } }

    transition!{ put(lbl: Label, new_journal: LinkedJournal_v::LinkedJournal::State) {
        require lbl is Put;
        require LinkedJournal_v::LinkedJournal::State::next(pre.journal, new_journal, Self::linked_lbl(lbl));
        update journal = new_journal;
    } }

    // TODO old_first is really an abritrary value; remove the parameter (dependency)
    pub open spec(checked) fn new_first(tj: TruncatedJournal, lsn_au_index: LsnAUIndex, new_bdy: LSN) -> AU
    recommends
        tj.disk_view.is_nondangling_pointer(tj.freshest_rec),
    {
        let post_freshest_rec = if tj.seq_end() == new_bdy { None } else { tj.freshest_rec }; // matches defn at TruncatedJournal::discard_old
        if post_freshest_rec is Some && lsn_au_index.contains_key(new_bdy) {
            lsn_au_index[new_bdy]
        } else {
            arbitrary() // doesn't matter, would never reach here
        }
    }

    transition!{ discard_old(lbl: Label, new_journal: LinkedJournal::State) {
        require lbl is DiscardOld;

        let start_lsn = lbl->start_lsn;
        let require_end = lbl->require_end;
        let deallocs = lbl.arrow_DiscardOld_deallocs();

        require require_end == pre.journal.seq_end();
        require pre.tj().can_discard_to(start_lsn);

        let new_first = Self::new_first(pre.tj(), pre.lsn_au_index, start_lsn);
        let new_lsn_au_index = lsn_au_index_discard_up_to(pre.lsn_au_index, start_lsn);
        let discarded_aus = pre.lsn_au_index.values().difference(new_lsn_au_index.values());
        let keep_addrs = Set::new(|addr: Address| pre.tj().disk_view.entries.contains_key(addr) 
            && new_lsn_au_index.values().contains(addr.au));

        require deallocs == discarded_aus;
        require pre.tj().discard_old_tight(start_lsn, keep_addrs, new_journal.truncated_journal);

        require new_journal.unmarshalled_tail ==
            pre.journal.unmarshalled_tail.bounded_discard(start_lsn);

        update journal = new_journal;
        update lsn_au_index = new_lsn_au_index;
        update first = new_first;
        update mini_allocator = pre.mini_allocator.prune(discarded_aus);
        // note that these AUs refine to free (in the frozen freeset)
    } }

    transition!{ internal_journal_marshal(lbl: Label, cut: LSN, addr: Address, post_linked_journal: LinkedJournal::State) {
        require lbl is InternalAllocations;
        require lbl->allocs == Set::<AU>::empty();
        require lbl.arrow_InternalAllocations_deallocs() == Set::<AU>::empty();
        require pre.mini_allocator.tight_next_addr(pre.tj().freshest_rec, addr);

        // LinkedJournal conditions
        require pre.journal.unmarshalled_tail.seq_start < cut;
        require pre.journal.unmarshalled_tail.can_discard_to(cut);
        let marshalled_msgs = pre.journal.unmarshalled_tail.discard_recent(cut);
        require post_linked_journal.truncated_journal == pre.tj().append_record(addr, marshalled_msgs);
        require post_linked_journal.unmarshalled_tail == pre.journal.unmarshalled_tail.discard_old(cut);
        // End of LinkedJournal conditions

        update journal = post_linked_journal;
        update lsn_au_index = lsn_au_index_append_record(pre.lsn_au_index, marshalled_msgs, addr.au);
        update first = if pre.journal.truncated_journal.freshest_rec is Some { pre.first } else { addr.au };
        update mini_allocator = pre.mini_allocator.allocate(addr).observe(addr);
    } }

    transition!{ internal_mini_allocator_fill(lbl: Label) {
        require lbl is InternalAllocations;
        require let Label::InternalAllocations{allocs, deallocs} = lbl;
        require deallocs == Set::<AU>::empty();
        require allocs.disjoint(pre.mini_allocator.allocs.dom());
        require allocs.disjoint(pre.lsn_au_index.values()); // fresh from existing AUs

        update mini_allocator = pre.mini_allocator.add_aus(allocs);
    } }

    transition!{ internal_mini_allocator_prune(lbl: Label) {
        require lbl is InternalAllocations;
        require lbl->allocs == Set::<AU>::empty();
        require forall |au| lbl.arrow_InternalAllocations_deallocs().contains(au)
                ==> pre.mini_allocator.can_remove(au);

        // NOTE(JL): prune has very loose requirements
        update mini_allocator = pre.mini_allocator.prune(lbl.arrow_InternalAllocations_deallocs());
    } }

    transition!{ internal_no_op(lbl: Label) {
        require lbl is InternalAllocations;
        require lbl->allocs == Set::<AU>::empty();
        require lbl.arrow_InternalAllocations_deallocs() == Set::<AU>::empty();
    } }

    init!{ initialize(journal: LinkedJournal::State, image: JournalImage) {
        require image.valid_image();
        require LinkedJournal::State::initialize(journal, image.tj);

        let mini_allocator = MiniAllocator::empty();
        let lsn_au_index = image.tj.build_lsn_au_index(image.first);

        init journal = journal;
        init lsn_au_index = lsn_au_index;
        init first = image.first;
        init mini_allocator = mini_allocator;
    } }

    //////////////////////////////////////////////////////////////////////////////
    // AllocationJournalRefinement stuff
    //

    pub open spec(checked) fn tj(self) -> TruncatedJournal
    {
        self.journal.truncated_journal
    }

    pub open spec(checked) fn mini_allocator_follows_freshest_rec(root: Pointer, allocator: MiniAllocator) -> bool
    {
        allocator.curr is Some ==> {
            &&& root is Some
            &&& root.unwrap().au == allocator.curr.unwrap()
            // &&& forall |addr| freshest_rec.unwrap().after_page(addr) ==> #[trigger] allocator.can_allocate(addr)
        }
    }

    pub open spec(checked) fn disk_domain_not_free(dv: DiskView, allocator: MiniAllocator) -> bool
    {
        forall |addr| #[trigger] dv.entries.dom().contains(addr) ==> {
            &&& !allocator.can_allocate(addr)
        }
    }

    #[invariant]
    pub open spec(checked) fn inv(self) -> bool {
        &&& self.wf()
        &&& self.tj().disk_view.pointer_is_upstream(self.tj().freshest_rec, self.first)
        &&& self.tj().disk_view.bounded_inactive_lsns(self.lsn_au_index, self.tj().freshest_rec)
        &&& self.lsn_au_index == self.tj().build_lsn_au_index(self.first)

        &&& self.tj().disk_view.domain_tight_wrt_index(self.lsn_au_index, self.tj().freshest_rec)
        &&& Self::disk_domain_not_free(self.tj().disk_view, self.mini_allocator)
        &&& Self::mini_allocator_follows_freshest_rec(self.tj().freshest_rec, self.mini_allocator)
    }

    #[inductive(freeze_for_commit)]
    fn freeze_for_commit_inductive(pre: Self, post: Self, lbl: Label, depth: nat) {
        reveal(LinkedJournal::State::next);
        reveal(LinkedJournal::State::next_by );
    }

    #[inductive(read_for_recovery)]
    fn read_for_recovery_inductive(pre: Self, post: Self, lbl: Label) { }

    #[inductive(query_end_lsn)]
    fn query_end_lsn_inductive(pre: Self, post: Self, lbl: Label) { }

    #[inductive(put)]
    fn put_inductive(pre: Self, post: Self, lbl: Label, new_journal: LinkedJournal_v::LinkedJournal::State) {
        reveal(LinkedJournal::State::next);
        reveal(LinkedJournal::State::next_by);
    }

    #[inductive(internal_mini_allocator_fill)]
    fn internal_mini_allocator_fill_inductive(pre: Self, post: Self, lbl: Label) {
    }

    #[inductive(internal_mini_allocator_prune)]
    fn internal_mini_allocator_prune_inductive(pre: Self, post: Self, lbl: Label) {
    }

    #[inductive(discard_old)]
    fn discard_old_inductive(pre: Self, post: Self, lbl: Label, new_journal: LinkedJournal::State) {
//        assert( post.wf() );

        let start_lsn = lbl->start_lsn;
        let keep_addrs = Set::new(|addr: Address| pre.tj().disk_view.entries.contains_key(addr) 
            && post.lsn_au_index.values().contains(addr.au));

        pre.tj().discard_old_preserves_acyclicity(start_lsn, keep_addrs, post.tj());
//        assert( post.tj().disk_view.acyclic() );
        pre.tj().build_lsn_au_index_ensures(pre.first);

        let pre_dv = pre.tj().disk_view;
        let post_dv = post.tj().disk_view;

//        assert( post_dv.bounded_inactive_lsns(post.lsn_au_index, post.tj().freshest_rec) );
        assert( post_dv.internal_au_pages_fully_linked() ) by {
            reveal(DiskView::pages_allocated_in_lsn_order);
        }

        if post.tj().freshest_rec is Some {
            assert( post_dv.has_unique_lsns() ) by {
                assert forall |lsn, addr1, addr2| post_dv.addr_supports_lsn(addr1, lsn) && post_dv.addr_supports_lsn(addr2, lsn)
                implies addr1 == addr2 by {
                    assert(pre_dv.addr_supports_lsn(addr1, lsn) && pre_dv.addr_supports_lsn(addr2, lsn));
                }
            }

            assert( post_dv.valid_first_au(post.first) ) by {
//                assert(pre.lsn_au_index.contains_key(start_lsn));
                assert(post.lsn_au_index.contains_key(start_lsn));

                reveal(DiskView::index_keys_exist_valid_entries);
                let witness = choose |witness: Address| witness.wf() && witness.au == pre.lsn_au_index[start_lsn]
                    && #[trigger] pre_dv.addr_supports_lsn(witness, start_lsn);

//                assert(pre_dv.entries.contains_key(witness)); // trigger
//                assert(post_dv.entries.contains_key(witness));
                assert(post_dv.addr_supports_lsn(witness, start_lsn)); // trigger
            }

            assert(post.tj().disk_view.pointer_is_upstream(post.tj().freshest_rec, post.first));

            let repr = post.tj().build_lsn_au_index(post.first);
            pre_dv.build_lsn_au_index_equiv_page_walk(pre.tj().freshest_rec, pre.first);
            post_dv.build_lsn_au_index_equiv_page_walk(post.tj().freshest_rec, post.first);

            post_dv.build_lsn_au_index_page_walk_domain(post.tj().freshest_rec); // same domain
            assert( post.lsn_au_index.dom() =~= repr.dom() ); // needs more proof
            post_dv.build_lsn_au_index_page_walk_sub_disk(pre_dv, post.tj().freshest_rec); // index subset
        }
        assert( post.lsn_au_index =~= post.tj().build_lsn_au_index(post.first) ); // needs more proof
//        assert( post.inv() );
    }

    #[inductive(internal_journal_marshal)]
    fn internal_journal_marshal_inductive(pre: Self, post: Self, lbl: Label, cut: LSN, addr: Address, post_linked_journal: LinkedJournal::State) {
        let msgs = pre.journal.unmarshalled_tail.discard_recent(cut);
        let pre_dv = pre.tj().disk_view;
        let pre_root = pre.tj().freshest_rec;
        let post_dv = post.tj().disk_view;
        let post_root = post.tj().freshest_rec;

//        assert( post.wf() );
//        assert( post_dv.decodable(post_root) );
        assert( post_dv.valid_ranking(pre.tj().marshal_ranking(addr)) ); // witness, duped from linked journal
//        assert( post.tj().disk_view.acyclic() );

        pre.tj().build_lsn_au_index_ensures(pre.first);

        let update = singleton_index(msgs.seq_start, msgs.seq_end, addr.au);
//        assert( update.contains_key(msgs.seq_start) );
//        assert( update[msgs.seq_start] == addr.au );
        assert( post.lsn_au_index.contains_key(msgs.seq_start) );

        assert(post_dv.domain_tight_wrt_index(post.lsn_au_index, post_root)) by {
            assert forall |addr| #[trigger] post_dv.entries.dom().contains(addr)
            implies post.lsn_au_index.values().contains(addr.au)
            by {
                if pre_dv.entries.dom().contains(addr) {
                    let lsn = choose |lsn| #[trigger] pre.lsn_au_index.contains_key(lsn) && pre.lsn_au_index[lsn] == addr.au;
//                    assert( !update.contains_key(lsn) );
                    assert( post.lsn_au_index.contains_key(lsn)); // trigger
                }
            }
        }

//        assert(post_dv.bounded_inactive_lsns(post.lsn_au_index, post.tj().freshest_rec));

        assert( post_dv.valid_first_au(post.first) ) by {
            if pre_root is Some {
                let witness = choose |witness: Address| #![auto] witness.au == pre.first
                    && pre_dv.addr_supports_lsn(witness, post_dv.boundary_lsn);
                assert(post_dv.addr_supports_lsn(witness, post_dv.boundary_lsn));
            } else {
                assert(post_dv.addr_supports_lsn(addr, post_dv.boundary_lsn));
            }
        }

        assert( post_dv.has_unique_lsns() ) by {
            assert forall |lsn, addr1, addr2| post_dv.addr_supports_lsn(addr1, lsn) && post_dv.addr_supports_lsn(addr2, lsn)
            implies addr1 == addr2 by {
                if lsn < msgs.seq_start {
                    assert(pre_dv.addr_supports_lsn(addr1, lsn) && pre_dv.addr_supports_lsn(addr2, lsn));
                } else if addr1 != addr2 {
                    let pre_addr = if pre_dv.addr_supports_lsn(addr1, lsn) { addr1 } else { addr2 };
                    assert(pre_dv.entries[pre_addr].message_seq.contains(lsn));
//                    assert(false);
                }
            }
        }

        assert( post_dv.pages_allocated_in_lsn_order() ) by {
            reveal(DiskView::pages_allocated_in_lsn_order);
        }

//        assert( post_dv.pointer_is_upstream(post_root, post.first) );

        assert( post.lsn_au_index == post.tj().build_lsn_au_index(post.first) ) by {
            pre_dv.build_lsn_au_index_equiv_page_walk(pre_root, pre.first);
//            assert( pre.lsn_au_index == pre_dv.build_lsn_au_index_page_walk(pre_root) );

            pre_dv.build_lsn_au_index_page_walk_sub_disk(post_dv, pre_root);
//            assert( post_dv.build_lsn_au_index_page_walk(pre_root)
//                    == pre_dv.build_lsn_au_index_page_walk(pre_root) );

//            assert( post_dv.build_lsn_au_index_page_walk(post_root) ==
//                post_dv.build_lsn_au_index_page_walk(pre_root).union_prefer_right(update) );
            let au_update = singleton_index(msgs.seq_start, msgs.seq_end, addr.au);
//            assert( au_update == update );

//            assert( post.lsn_au_index == post_dv.build_lsn_au_index_page_walk(post_root) );
            pre_dv.build_commutes_over_append_record(pre_root, msgs, addr);
            post_dv.build_lsn_au_index_equiv_page_walk(post_root, post.first);
        }

//        assert( post.inv() );
    }

    #[inductive(internal_no_op)]
    fn internal_no_op_inductive(pre: Self, post: Self, lbl: Label) { }

    #[inductive(initialize)]
    fn initialize_inductive(post: Self, journal: LinkedJournal::State, image: JournalImage) {
//        assert( post.wf() );
//        assert( post.lsn_au_index == post.tj().build_lsn_au_index(post.first) );
//        assert( post.tj().disk_view.pointer_is_upstream(post.tj().freshest_rec, post.first) );
//        assert( Self::mini_allocator_follows_freshest_rec(post.tj().freshest_rec, post.mini_allocator) );
//        assert( post.inv() );
    }

    // NOTE(JL): temporary workaround
    pub proof fn inv_next(pre: Self, post: Self, lbl: Label)
    requires pre.inv(), Self::next(pre, post, lbl)
    ensures post.inv()
    {
        reveal(AllocationJournal::State::next);
        reveal(AllocationJournal::State::next_by);

        let step = choose |step| Self::next_by(pre, post, lbl, step);
        match step {
            AllocationJournal::Step::freeze_for_commit(depth) => {
                Self::freeze_for_commit_inductive(pre, post, lbl, depth);
            },
            AllocationJournal::Step::put(new_journal) => {
                Self::put_inductive(pre, post, lbl, new_journal);
            },
            AllocationJournal::Step::internal_mini_allocator_fill() => {
                Self::internal_mini_allocator_fill_inductive(pre, post, lbl);
            },
            AllocationJournal::Step::internal_mini_allocator_prune() => {
                Self::internal_mini_allocator_prune_inductive(pre, post, lbl);
            },
            AllocationJournal::Step::discard_old(new_journal) => {
                Self::discard_old_inductive(pre, post, lbl, new_journal);
            },
            AllocationJournal::Step::internal_journal_marshal(cut, addr, new_journal) => {
                Self::internal_journal_marshal_inductive(pre, post, lbl, cut, addr, new_journal);
            },
            _ => {
//                assert(post.inv());
            },
        }
    }

    // utility functions for refinement layers below

    pub proof fn frozen_journal_is_valid_image(pre: Self, post: Self, lbl: AllocationJournal::Label)
    requires pre.inv(), post.inv(), lbl is FreezeForCommit, Self::next(pre, post, lbl)
    ensures
        lbl->frozen_journal.valid_image(),
        lbl->frozen_journal.tj.seq_end() <= post.tj().seq_end()
    {
        reveal(AllocationJournal::State::next);
        reveal(AllocationJournal::State::next_by);

        let frozen_journal = lbl->frozen_journal;
        let step = choose |step| AllocationJournal::State::next_by(pre, post, lbl, step);
        let depth = step.get_freeze_for_commit_0();

        pre.tj().disk_view.pointer_after_crop_ensures(pre.tj().freshest_rec, depth);
        pre.tj().disk_view.pointer_after_crop_seq_end(pre.tj().freshest_rec, depth);
//        assert(frozen_journal.tj.seq_end() <= pre.tj().seq_end());

        pre.tj().build_lsn_au_index_ensures(pre.first);
        let sub_dv = pre.tj().sub_disk_preserves_pointer_is_upstream(pre.lsn_au_index, pre.first, 
            frozen_journal.tj.seq_start(), frozen_journal.tj.freshest_rec, frozen_journal.first);
        assert(sub_dv =~= frozen_journal.tj.disk_view);
        pre.tj().sub_disk_preserves_bounded_inactive_lsns(pre.lsn_au_index, pre.first, 
            frozen_journal.tj, frozen_journal.first);
    }

    pub proof fn subrange_preserves_valid_structure(self: Self, sub_start: LSN, sub_freshest_rec: Pointer, sub_first: AU)
    requires 
        self.tj().valid_structure(self.lsn_au_index, self.first),
        self.tj().valid_subrange(self.lsn_au_index, self.first, sub_start, sub_freshest_rec, sub_first),
    ensures ({
        let sub_dv = self.tj().disk_view.discard_old(sub_start);
        let sub_tj = sub_dv.tj_at(sub_freshest_rec);
        &&& sub_dv.pointer_is_upstream(sub_freshest_rec, sub_first)
        &&& sub_dv.bounded_inactive_lsns(sub_tj.build_lsn_au_index(sub_first), sub_freshest_rec)
    })
    {
        let sub_dv = self.tj().disk_view.discard_old(sub_start);
        let sub_tj = sub_dv.tj_at(sub_freshest_rec);
        self.tj().subrange_preserves_pointer_is_upstream(self.lsn_au_index, self.first, sub_start, sub_freshest_rec, sub_first);
        if sub_freshest_rec is Some {
            self.tj().sub_disk_preserves_bounded_inactive_lsns(self.lsn_au_index, self.first, sub_tj, sub_first);
        }
    }

//     #[verifier::spinoff_prover]  // flaky proof
//     pub proof fn discard_old_helper4(pre: Self, post: Self, lbl: Label, new_journal: LinkedJournal::State, xaddr: Address, zaddr: Address)
//     requires
//         Self::inv(pre),
//         Self::discard_old(pre, post, lbl, new_journal),
//         post.tj().disk_view.entries.contains_key(zaddr),
//         post.tj().seq_start() < post.tj().disk_view.entries[zaddr].message_seq.seq_start,
//         post.tj().freshest_rec is Some,
//         zaddr.au != pre.first,
//         zaddr.au != post.first,
//         xaddr.au == zaddr.au,
//         0 <= xaddr.page < zaddr.page,
//     ensures
//         post.tj().disk_view.entries.contains_key(xaddr),
//     decreases zaddr.page - xaddr.page
//     {
//         let pre_dv = pre.tj().disk_view;
//         let post_dv = post.tj().disk_view;
//         // Self::invoke_submodule_inv(pre, post);
//         // Note to Pranav: here's a good example of a deep layer violation!
//         let zpaged = post_dv.iptr(Some(zaddr));    // relies on LinkedJournal_Refinement
//         assert( zpaged is Some );
//         let zpaged = zpaged.unwrap();
//         let zlsn = post_dv.entries[zaddr].message_seq.seq_start;
//         let ylsn = (zlsn - 1) as nat;
// //         assert( post_dv.entries[zaddr].message_seq == zpaged.message_seq );
//         assert( post_dv.entries[zaddr].message_seq.seq_start != 0 );
//         assert( ylsn < post_dv.entries[zaddr].message_seq.seq_start );
//         // assert( post.journal.lsn_addr_index.contains_key(zlsn) && post.journal.lsn_addr_index[zlsn]==zaddr ) by {
//         //     assert( post_dv.addr_supports_lsn(zaddr, zlsn) );
//         //     //assert( post_dv.entries[zaddr].message_seq.contains(zlsn) );
//         // }
//         // assert( post.journal.lsn_addr_index.contains_key(zlsn) );

//         assert( post.tj().seq_start() <= zlsn < post.tj().seq_end() ) by {
//             reveal(TruncatedJournal::index_domain_valid);
//         }

//         // assert( post.journal.lsn_addr_index.contains_key(zlsn) );
//         assert( post_dv.entries[zaddr].message_seq.seq_start < post.tj().seq_end() ) by {
//         }
//         assert( ylsn < post.tj().seq_end() );
//         if ylsn < post.tj().seq_start() {
//             assert( zlsn == post.tj().seq_start() );
//             assert( false );
//         }
//         assert( post.tj().seq_start() <= ylsn );
//         assert( post.tj().seq_start() <= ylsn ) by {    // all redundant with prev line
//             if ylsn < post.tj().seq_start() {
//                 assert( post.lsn_au_index.contains_key(post_dv.boundary_lsn) );
//                 assert( post.lsn_au_index[post_dv.boundary_lsn] == zaddr.au );
//                 assert( false );
//             }
//             // argument about first
//         }

//         let yaddr = Address{au: zaddr.au, page: (zaddr.page - 1) as nat};
//         let y0lsn = post_dv.entries[yaddr].message_seq.seq_start;

//         assert( post.tj().seq_start() < y0lsn ) by {
//             if y0lsn <= post.tj().seq_start() {
//                 assert( y0lsn <= post_dv.boundary_lsn );
//                 assert( post_dv.boundary_lsn <= ylsn );

//                 // TODO(chris): if I replace the two lines above with this single assert, the proof
//                 // falls apart. That's ... extremely counterintuitive.
//                 // In fact, if I ADD this line, keeping those above, the proof falls apart!! That's
//                 // crazy.
//                 //assert( y0lsn <= post_dv.boundary_lsn <= ylsn );
//                 // ...maybe it's just flakiness. This proof seems EXTREMELY brittle.

//                 assert( contiguous_lsns(post.lsn_au_index, y0lsn, post_dv.boundary_lsn, ylsn) );
//                 assert( y0lsn <= post_dv.boundary_lsn <= ylsn );

// THIS PROOF IS HELLA FLAKY; address later
//                 assert( post_dv.entries[yaddr].message_seq.contains(y0lsn) );   //trigger

//                 // assert( post.journal.lsn_addr_index.contains_key(y0lsn) );
//                 // assert( post.journal.lsn_addr_index.dom().contains(y0lsn) );
//                 assert( post.lsn_au_index.contains_key(y0lsn) );
//                 assert( post.lsn_au_index.contains_key(ylsn) );
//                 assert( post.lsn_au_index[y0lsn] == post.lsn_au_index[ylsn] );
//                 assert( post.lsn_au_index.contains_key(post_dv.boundary_lsn) );
//                 assert( post.lsn_au_index[post_dv.boundary_lsn] == zaddr.au );
//                 assert( false );
//             }
//         }

//         //assert( Self::au_page_links_to_prior(pre_dv, Address{au: zaddr.au, page: zaddr.page}) );

// //         assert( Self::au_page_links_to_prior(pre_dv, zaddr) ); // trigger

//         if xaddr != yaddr {
//             assert( post.tj().seq_start() < y0lsn );
//             Self::discard_old_helper4(pre, post, lbl, new_journal, xaddr, yaddr);
//         }
//     }
} }  // state_machine


} // verus!
  // verus
