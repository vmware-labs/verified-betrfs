// Copyright 2018-2021 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, and University of Washington
// SPDX-License-Identifier: BSD-2-Clause

#![allow(unused_imports)]
use builtin::*;

use builtin_macros::*;
use state_machines_macros::state_machine;

use vstd::prelude::*;
use crate::abstract_system::StampedMap_v::LSN;
use crate::abstract_system::MsgHistory_v::*;
use crate::disk::GenericDisk_v::*;
use crate::journal::LinkedJournal_v;
use crate::journal::LinkedJournal_v::{LinkedJournal, DiskView, TruncatedJournal};
use crate::journal::LikesJournal_v;
use crate::journal::LikesJournal_v::{LikesJournal};
use crate::allocation_layer::AllocationJournal_v;
use crate::allocation_layer::AllocationJournal_v::*;

verus!{

impl AllocationJournal::Step {
    proof fn i(self) -> LikesJournal::Step {
        match self {
            Self::read_for_recovery() =>
                LikesJournal::Step::read_for_recovery(),
            Self::freeze_for_commit() =>
                LikesJournal::Step::freeze_for_commit(),
            Self::query_end_lsn() =>
                LikesJournal::Step::query_end_lsn(),
            Self::put(new_journal) =>
                LikesJournal::Step::put(new_journal),
            Self::discard_old(new_journal) =>
                LikesJournal::Step::discard_old(new_journal),
            Self::internal_journal_marshal(cut, addr, new_journal) =>
                LikesJournal::Step::internal_journal_marshal(cut, addr, new_journal),
            Self::internal_mini_allocator_fill() =>
                LikesJournal::Step::internal_no_op(),
            Self::internal_mini_allocator_prune() =>
                LikesJournal::Step::internal_no_op(),
            Self::internal_no_op() =>
                LikesJournal::Step::internal_no_op(),
            _ => { arbitrary() },   // TODO(travis): wart on the state machine language
        }
    }
}

impl AllocationJournal::Label {
    pub open spec(checked) fn i(self) -> LikesJournal::Label
    {
        match self {
            Self::ReadForRecovery{messages} =>
                LikesJournal::Label::ReadForRecovery{messages},
            Self::FreezeForCommit{frozen_journal} =>
                LikesJournal::Label::FreezeForCommit{frozen_journal: frozen_journal.tj},
            Self::QueryEndLsn{end_lsn} =>
                LikesJournal::Label::QueryEndLsn{end_lsn},
            Self::Put{messages} =>
                LikesJournal::Label::Put{messages},
            Self::DiscardOld{start_lsn, require_end, deallocs} =>
                LikesJournal::Label::DiscardOld{start_lsn, require_end},
            Self::InternalAllocations{allocs, deallocs} =>
                LikesJournal::Label::Internal{},
        }
    }
}

// impl DiskView{

//     // can crop
//     // if next is present, then next is the same

//     // representation


//     // pub proof fn build_tight_preserves_crop(self, root: Pointer, depth: nat)
//     // requires 
//     //     self.decodable(root),
//     //     self.acyclic(),
//     //     self.block_in_bounds(root),
//     // ensures 
//     //     self.build_tight(root).decodable(root),
//     //     self.build_tight(root).block_in_bounds(root),
//     //     self.build_tight(root).can_crop(root, depth) == self.can_crop(root, depth),
//     //     // self.build_tight(root).pointer_after_crop(root, depth) == self.pointer_after_crop(root, depth)
//     // decreases depth
//     // {
//     //     DiskView::tight_interp(self, root, self.build_tight(root));
//     //     if depth > 0 {
//     //         if root is Some {
//     //             self.build_tight_preserves_crop(self.next(root), (depth-1) as nat);

//     //             assert(self.build_tight(self.next(root)).can_crop(self.next(root), (depth-1) as nat) 
//     //                 == self.can_crop(self.next(root), (depth-1) as nat));

//     //             self.build_tight_shape(root);

//     //             if self.can_crop(root, depth) {
//     //                 assume(false);
//     //             } else if self.build_tight(root).can_crop(root, depth) {
//     //                 assert(root.is_Some());
//     //                 assert(self.build_tight(root).can_crop(self.next(root), (depth-1) as nat));
//     //                 assert(self.next(root) != root);


//     //                 // self.build_tight(self.next(root)) == Self{entries: self.build_tight(root).entries.remove(root.unwrap()), ..self})

//     //                 // self.build_tight(self.next(root)).can_crop(self.next(root), (depth-1) as nat) is false


//     //                 // assert(self.build_tight(root).next(root) == self.next(root));

//     //                 // assert(self.build_tight(self.next(root)).can_crop(self.next(root), (depth-1) as nat));

//     //                 // assert(self.build_tight(root).can_crop(self.next(root), (depth-1) as nat) == 
//     //                 //     self.can_crop(self.next(root), (depth-1) as nat)
//     //                 // );
//     //                 assert(false);
//     //             }
//     //     //         self.build_tight_shape(root);
//     //     //     }
//     //     //     // if self.next(root) is Some {
//     //     //     //     // we are saying this isn't decodable
//     //     //     //     self.build_tight_ranks(self.next(root));
//     //         } 
//     //     }
//     // }
// }

// The thrilling climax, the actual proof goal we want to use in lower
// refinement layers.
impl AllocationJournal::State {
    pub open spec(checked) fn i(self) -> LikesJournal::State
        recommends self.tj().decodable()
    {
        LikesJournal::State{
            journal: self.journal,
            lsn_addr_index: self.tj().build_lsn_addr_index()
        }
    }

    pub proof fn discard_old_refines(self, post: Self, lbl: AllocationJournal::Label, new_journal: LinkedJournal::State)
        requires self.inv(), post.inv(), Self::discard_old(self, post, lbl, new_journal)
        ensures LikesJournal::State::next_by(self.i(), post.i(), lbl.i(), LikesJournal::Step::discard_old(new_journal))
    {
        reveal(LikesJournal::State::next_by);
        assert(post.i().journal == new_journal);

        let start_lsn = lbl.get_DiscardOld_start_lsn();
        let require_end = lbl.get_DiscardOld_require_end();
        let keep_addrs = Set::new(|addr: Address| addr.wf() && post.lsn_au_index.values().contains(addr.au));

        let lsn_addr_index_post = LikesJournal_v::lsn_addr_index_discard_up_to(self.i().lsn_addr_index, start_lsn);
        let i_keep_addrs = lsn_addr_index_post.values();

        reveal(TruncatedJournal::index_domain_valid);

        if self.tj().freshest_rec is Some {
            self.tj().disk_view.build_lsn_addr_index_domain_valid(self.tj().freshest_rec);
        }

        post.tj().disk_view.sub_disk_with_newer_lsn_repr_index(self.tj().disk_view, post.tj().freshest_rec);
        assert(post.i().lsn_addr_index <= self.i().lsn_addr_index);

        LikesJournal_v::lsn_addr_index_discard_up_to_ensures(self.i().lsn_addr_index, start_lsn);
        assert(lsn_addr_index_post <= self.i().lsn_addr_index);

        if post.tj().freshest_rec is Some {
            post.tj().disk_view.build_lsn_addr_index_domain_valid(self.tj().freshest_rec);
        }
        assert(post.i().lsn_addr_index =~= lsn_addr_index_post);
        assert(self.lsn_au_index == self.tj().build_lsn_au_index(self.first));
        assert(lsn_addr_index_post.dom() =~= post.lsn_au_index.dom());

        self.tj().disk_view.build_lsn_au_index_equiv_page_walk(self.tj().freshest_rec, self.first);
        self.tj().disk_view.build_lsn_au_index_page_walk_consistency(self.tj().freshest_rec);
        self.tj().disk_view.build_lsn_addr_index_reflects_disk_view(self.tj().freshest_rec);
        assert(i_keep_addrs <= keep_addrs);

        assert(self.tj().discard_old_cond(start_lsn, i_keep_addrs, new_journal.truncated_journal));
    }

//     pub proof fn next_refines(self, post: Self, lbl: AllocationJournal::Label)
//     requires
//         self.inv(),
//         post.inv(),
//         AllocationJournal::State::next(self, post, lbl),
//     ensures
//         LikesJournal::State::next(self.i(), post.i(), lbl.i()),
//     {
//         reveal(LikesJournal::State::next_by);  // unfortunate defaults
//         reveal(LikesJournal::State::next);
//         reveal(AllocationJournal::State::next_by);
//         reveal(AllocationJournal::State::next);

//         let step = choose |step| AllocationJournal::State::next_by(self, post, lbl, step);
//         match step {
//             AllocationJournal::Step::read_for_recovery() => {
//                 self.read_for_recovery_refines(post, lbl);
//             },
//             AllocationJournal::Step::freeze_for_commit() => {
//                 assume( LikesJournal::State::next_by(self.i(), post.i(), lbl.i(), LikesJournal::Step::freeze_for_commit()) );
//             },
//             AllocationJournal::Step::query_end_lsn() => {
//                 assume( LikesJournal::State::next_by(self.i(), post.i(), lbl.i(), LikesJournal::Step::query_end_lsn()) );
//             },
//             AllocationJournal::Step::put(new_journal) => {
//                 assume( LikesJournal::State::next_by(self.i(), post.i(), lbl.i(), LikesJournal::Step::put(new_journal)) );
//             },
//             AllocationJournal::Step::discard_old(new_journal) => {
//                 self.discard_old_refines(post, lbl, new_journal);
//             },
//             AllocationJournal::Step::internal_journal_marshal(cut, addr, new_journal) => {
//                 assume( LikesJournal::State::next_by(self.i(), post.i(), lbl.i(), LikesJournal::Step::internal_journal_marshal(cut, addr, new_journal)) );
//             },
//             _ => {
//                 assert( LikesJournal::State::next_by(self.i(), post.i(), lbl.i(), LikesJournal::Step::internal_no_op()) );
//             },
//         }
//     }

}


} // verus!
