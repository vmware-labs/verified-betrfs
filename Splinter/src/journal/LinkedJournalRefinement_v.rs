// Copyright 2018-2024 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, University of Washington
// SPDX-License-Identifier: BSD-2-Clause
//
#![allow(unused_imports)]
use builtin::*;

use builtin_macros::*;
use state_machines_macros::state_machine;

use vstd::prelude::*;
use vstd::calc_macro::*;
use crate::abstract_system::StampedMap_v::LSN;
use crate::abstract_system::MsgHistory_v::*;
use crate::disk::GenericDisk_v::*;
use crate::journal::PagedJournal_v;
use crate::journal::PagedJournal_v::PagedJournal;
use crate::journal::LinkedJournal_v;
use crate::journal::LinkedJournal_v::*;

verus!{

impl DiskView {
    pub proof fn iptr_output_valid(self, ptr: Pointer)
    requires
        self.decodable(ptr),
        self.acyclic(),
        self.block_in_bounds(ptr),
    ensures
        self.iptr(ptr) is Some ==> self.iptr(ptr).unwrap().valid(self.boundary_lsn),
    decreases self.the_rank_of(ptr)
    {
        if ptr is Some {
            self.iptr_output_valid(self.next(ptr));
        }
    }

    #[verifier::spinoff_prover]
    pub proof fn discard_interp(self, lsn: LSN, post: Self, ptr: Pointer)
    requires
        self.wf(),
        self.acyclic(),
        self.boundary_lsn <= lsn,
        post == self.discard_old(lsn),
        self.block_in_bounds(ptr),
        post.block_in_bounds(ptr),
    ensures
        post.acyclic(),
        self.iptr(ptr) is Some ==> self.iptr(ptr).unwrap().valid(lsn),
        post.iptr(ptr) == PagedJournal_v::JournalRecord::discard_old_journal_rec(self.iptr(ptr), lsn),
    decreases if ptr is Some { self.the_ranking()[ptr.unwrap()]+1 } else { 0 }
    {
        self.iptr_output_valid(ptr);
        assert( post.valid_ranking(self.the_ranking()) );
        if ptr is Some && lsn < self.entries[ptr.unwrap()].message_seq.seq_start {
            self.discard_interp(lsn, post, post.next(ptr));
        }

        let result = PagedJournal_v::JournalRecord::discard_old_journal_rec(self.iptr(ptr), lsn);
        if post.iptr(ptr) is None {
//            assert( result is None );
        } else {
//            assert( result is Some );
            assert( post.iptr(ptr).unwrap() =~= result.unwrap() );
        }
    }

    // In Dafny, this entire lemma was unneeded; call sites could be replaced by this single line:
    //   assert( self.valid_ranking(big.the_ranking()) ); // witness
    pub proof fn sub_disk_ranking(self, big: DiskView)
    requires
        big.wf(),
        big.acyclic(),
        self.wf(),
        self.is_sub_disk(big),
    ensures
        self.acyclic(),
    {
        let ranking = big.the_ranking();
    // TODO(andrea): jon tried writing a contains_key == dom.contains broadcast_forall, but it
    // didn't solve this problem.
    // TODO(jonh): explain this to andrea
        assert( forall |addr| #[trigger] self.entries.contains_key(addr) ==> big.entries.dom().contains(addr) );
        assert( self.valid_ranking(big.the_ranking()) ); // witness
    }

    // TODO(jonh): how does this relate to IPtrFraming!?
    pub proof fn sub_disk_interp(self, big: DiskView, ptr: Pointer)
    requires
        big.wf(),
        big.acyclic(),
        self.wf(),
        self.is_sub_disk(big),
        self.boundary_lsn == big.boundary_lsn,
        self.is_nondangling_pointer(ptr),
    ensures
        self.acyclic(),
        self.iptr(ptr) == big.iptr(ptr),
    decreases if ptr is Some { big.the_ranking()[ptr.unwrap()]+1 } else { 0 } 
    {
//        assert( big.valid_ranking(big.the_ranking()) ); // witness; new in Verus
        self.sub_disk_ranking(big);
        if ptr is Some {
//            assert( big.entries.contains_key(ptr.unwrap()) );   // new trigger for valid_ranking
            self.sub_disk_interp(big, big.next(ptr));
        }
    }

    // pub proof fn she_nat_igans(depth: nat)
    // {
    //     if 0 < depth {
    //         assert( ((depth-1) as nat) < depth );
    //     }
    // }

    pub proof fn pointer_after_crop_commutes_with_interpretation(self, ptr: Pointer, bdy: LSN, depth: nat)
    requires
        self.decodable(ptr),
        self.acyclic(),
        self.block_in_bounds(ptr),
        bdy == self.boundary_lsn,
        self.can_crop(ptr, depth),
        self.pointer_after_crop(ptr, depth) is Some,
    ensures
        PagedJournal_v::JournalRecord::opt_rec_can_crop_head_records(self.iptr(ptr), bdy, depth),
        PagedJournal_v::JournalRecord::opt_rec_can_crop_head_records(self.iptr(ptr), bdy, depth+1),
        self.iptr(self.pointer_after_crop(ptr, depth))
            == PagedJournal_v::JournalRecord::opt_rec_crop_head_records(self.iptr(ptr), bdy, depth),
    decreases depth
    {
        // Got 36 lines into this proof before I discovered I was missing
        // this ensures which used to be attached to iptr, for free. :v/
        self.iptr_output_valid(ptr);

        if 0 == depth {
            // Dafny didn't need this trigger
            let pojr = self.iptr(ptr).unwrap().cropped_prior(bdy);
            if !PagedJournal_v::JournalRecord::opt_rec_can_crop_head_records(pojr, bdy, 0) {
//                 assert( false );
            }
        } else {
            self.pointer_after_crop_commutes_with_interpretation(self.entries[ptr.unwrap()].cropped_prior(bdy), bdy, (depth - 1) as nat);
        }
    }

    pub proof fn pointer_after_crop_commutes_with_interpretation_no_some(self, ptr: Pointer, depth: nat)
    requires
        self.decodable(ptr),
        self.acyclic(),
        self.block_in_bounds(ptr),
        self.can_crop(ptr, depth),
    ensures
        PagedJournal_v::JournalRecord::opt_rec_can_crop_head_records(self.iptr(ptr), self.boundary_lsn, depth),
        self.iptr(self.pointer_after_crop(ptr, depth))
            == PagedJournal_v::JournalRecord::opt_rec_crop_head_records(self.iptr(ptr), self.boundary_lsn, depth),
    decreases depth
    {
        self.iptr_output_valid(ptr);
        self.pointer_after_crop_ensures(ptr, depth);

        if 0 < depth {
            self.pointer_after_crop_commutes_with_interpretation_no_some(self.entries[ptr.unwrap()].cropped_prior(self.boundary_lsn), (depth - 1) as nat);
        }
    }

    pub proof fn discard_old_commutes(self, ptr: Pointer, new_bdy: LSN)
    requires
        self.decodable(ptr),
        self.acyclic(),
        self.block_in_bounds(ptr),
        self.boundary_lsn <= new_bdy,
        ptr is Some ==> new_bdy < self.entries[ptr.unwrap()].message_seq.seq_end,
    ensures
        self.discard_old(new_bdy).acyclic(),
        self.iptr(ptr) is Some ==> self.iptr(ptr).unwrap().valid(new_bdy), // discard_old_journal_rec prereq
        PagedJournal_v::JournalRecord::discard_old_journal_rec(self.iptr(ptr), new_bdy) == self.discard_old(new_bdy).iptr(ptr),
    decreases self.the_rank_of(ptr)
    {
        self.iptr_output_valid(ptr);
        assert( self.discard_old(new_bdy).valid_ranking(self.the_ranking()) );
        if ptr is Some {
            let next_ptr = self.entries[ptr.unwrap()].cropped_prior(new_bdy);
            self.iptr(ptr).unwrap().discard_valid(self.boundary_lsn, new_bdy);
            self.discard_old_commutes(next_ptr, new_bdy);
        }
    }

    #[verifier::spinoff_prover]
    pub proof fn iptr_framing(self, dv2: Self, ptr: Pointer)
    requires
        self.wf() && self.acyclic(),
        dv2.wf() && dv2.acyclic(),
        self.is_nondangling_pointer(ptr),
        self.is_sub_disk(dv2),
        self.boundary_lsn == dv2.boundary_lsn,
    ensures
        self.iptr(ptr) == dv2.iptr(ptr),
    decreases self.the_rank_of(ptr)
    {
        if ptr is Some {
            self.iptr_framing(dv2, self.next(ptr));
        }
    }
        
    pub proof fn build_tight_is_awesome(self, root: Pointer)
    requires
        self.decodable(root),
        self.acyclic(),
    ensures
        self.build_tight(root).is_sub_disk(self),
        self.build_tight(root).wf(),
        self.build_tight(root).acyclic(),
    decreases self.the_rank_of(root),
    {
        if root is Some {
            self.build_tight_is_awesome(self.next(root));
            // TODO(chris): weird that I have to leave both of these identical calls in place!
            assert( self.build_tight(root).is_sub_disk(self) ); // introduced trigger to mitigate flakiness
            self.build_tight(root).sub_disk_ranking(self);
        }
        self.build_tight(root).sub_disk_ranking(self);
    }

    pub proof fn build_tight_maintains_interpretation(self, root: Pointer)
    requires
        self.decodable(root),
        self.acyclic(),
    ensures
        // You know what build_tight_awesome is for? To package ensures conveniently with a spec(checked) fn!
        self.iptr(root) == self.build_tight(root).iptr(root)
    decreases self.the_rank_of(root),
    {
        self.build_tight_is_awesome(root);
        if root is Some {
            self.build_tight_maintains_interpretation(self.next(root));
            self.build_tight(root).iptr_framing(self, self.next(root));
//            assert( self.iptr(root) =~~= self.build_tight(root).iptr(root) );
        } else {
//            assert( self.iptr(root) =~~= self.build_tight(root).iptr(root) );
        }
    }
}

impl TruncatedJournal {
    pub open spec(checked) fn next(self) -> Self
    recommends
        self.wf(),
        self.freshest_rec is Some,
    {
        Self{ freshest_rec: self.disk_view.next(self.freshest_rec), ..self }
    }

    pub open spec(checked) fn i(self) -> (out: PagedJournal_v::TruncatedJournal)
    recommends
        self.decodable(),
    // ensures out.wf()
    {
        PagedJournal_v::TruncatedJournal{
            boundary_lsn: self.disk_view.boundary_lsn,
            freshest_rec: self.disk_view.iptr(self.freshest_rec),
        }
    }

    pub proof fn iwf(self)
    requires
        self.decodable(),
    ensures
        self.i().wf(),
    {
        self.disk_view.iptr_output_valid(self.freshest_rec);
    }

    pub proof fn mkfs_refines()
    ensures
        Self::mkfs().disk_view.acyclic(),
        Self::mkfs().i() =~= PagedJournal_v::mkfs(),
    {
        assert( Self::mkfs().disk_view.valid_ranking(map![]) );
    }

    pub proof fn discard_old_decodable(self, new_bdy: LSN)
    requires
        self.decodable(),
        self.can_discard_to(new_bdy),
    ensures
        self.discard_old(new_bdy).decodable(),
    {
        assert( self.disk_view.discard_old(new_bdy).valid_ranking(self.disk_view.the_ranking()) );
    }

    pub proof fn discard_interp(self, lsn: LSN, post: Self)
    requires
        self.wf(),
        self.disk_view.acyclic(),
        self.seq_start() <= lsn <= self.seq_end(),
        post == self.discard_old(lsn),
    ensures
        post.disk_view.acyclic(),
        self.i().discard_old_defn(lsn) == post.i(),
    {
//        assert( post.disk_view.valid_ranking(self.disk_view.the_ranking()) );
        self.disk_view.discard_interp(lsn, post.disk_view, post.freshest_rec);
    }

    pub proof fn discard_old_commutes(self, new_bdy: LSN)
    requires
        self.decodable(),
        self.can_discard_to(new_bdy),
    ensures
        self.discard_old(new_bdy).decodable(), //prereq
        self.i().can_discard_to(new_bdy), //prereq
        self.discard_old(new_bdy).i() == self.i().discard_old_defn(new_bdy),
    {
        assert( self.disk_view.discard_old(new_bdy).valid_ranking(self.disk_view.the_ranking()) );  // witness to Acyclic
        if new_bdy < self.seq_end() {
          self.disk_view.discard_old_commutes(self.freshest_rec, new_bdy);
        }
    }

// /home/autograder/foo.dfy(4,12): Info: Selected triggers:
//    {F(I(x))}, {f(x)}
//  Rejected triggers:
//    {I(x)} (may loop with "I(g(f(x)))")
//    {G(F(I(x)))} (more specific than {F(I(x))})
//    {I(g(f(x)))} (more specific than {g(f(x))}, {f(x)})
//    {g(f(x))} (more specific than {f(x)})
// /home/autograder/foo.dfy(2,13): Info: Selected triggers:
//    {F(I(x))}, {f(x)}
//  Rejected triggers:
//    {I(x)} (may loop with "I(f(x))")
//    {I(f(x))} (more specific than {f(x)})
// /home/autograder/foo.dfy(3,13): Info: Selected triggers:
//    {G(I(x))}, {g(x)}
//  Rejected triggers:
//    {I(x)} (may loop with "I(g(x))")
//    {I(g(x))} (more specific than {g(x)})

    pub proof fn commute_transitivity<L, H>(I: spec_fn(L)->H, f: spec_fn(L)->L, F: spec_fn(H)->H, g: spec_fn(L)->L, G: spec_fn(H)->H)
    requires
        // TODO(verus): Verus refused to guess a trigger here. I had to go run Dafny to see what it
        // chose. I wanted that automated experience so desperately I *went back to Dafny to get it*
        forall |x| I(f(x)) == #[trigger] F(I(x)),
        forall |x| I(g(x)) == #[trigger] G(I(x)),
    ensures
        forall |x| I(g(f(x))) == G(#[trigger] F(I(x))),
    {
    }

    pub proof fn can_crop_monotonic(self, depth: nat, more: nat)
    requires
        depth <= more,
        self.can_crop(more),
    ensures
        self.can_crop(depth),
    decreases depth
    {
        if 0 < depth {
            self.next().can_crop_monotonic((depth-1) as nat, (more-1) as nat);
        }
    }

    pub proof fn crop_decreases_seq_end(self, depth: nat)
    requires
        self.can_crop(depth),
    ensures
        depth == 0 ==> self.crop(depth).seq_end() == self.seq_end(),
        0 < depth ==> self.crop(depth).seq_end() < self.seq_end(),
    decreases depth
    {
        if 0 < depth {
            self.can_crop_monotonic((depth-1) as nat, depth);
            self.next().crop_decreases_seq_end((depth - 1) as nat);
        }
    }

    pub proof fn linked_tj_can_crop_implies_paged_tj_can_crop(self, depth: nat)
    requires
        self.decodable(),
        self.can_crop(depth),
    ensures
        self.i().can_crop(depth),
    decreases depth
    {
        self.iwf();
        if 0 < depth {
            self.crop(1).linked_tj_can_crop_implies_paged_tj_can_crop((depth -1) as nat);

            let irec = self.i().freshest_rec.unwrap(); 
            let bdy = self.i().boundary_lsn;

            // wow, weird: this triggering assertion cures the crop(1).can_crop assertion above, too
            // ...and obviates the need for crop_ensures and can_crop_monotonic? That's hella
            // suspcicous.
            assert(self.crop(1).freshest_rec ==
                self.disk_view.pointer_after_crop(self.disk_view.next(self.freshest_rec), 0));
        }
    }

    pub proof fn paged_tj_can_crop_implies_linked_tj_can_crop(self, depth: nat)
    requires
        self.decodable(),
        self.i().can_crop(depth),
    ensures
        self.can_crop(depth),
    decreases depth
    {
        if 0 < depth {
            self.next().paged_tj_can_crop_implies_linked_tj_can_crop((depth - 1) as nat);
//            self.can_crop_increment(depth);   // whoah, Dafny version needed this and Verus doesn't?
        }
    }

    pub proof fn crop_head_composed_with_discard_old_commutes(self, new_bdy: LSN, depth: nat)
    requires
        self.decodable(),
        self.can_crop(depth),
        // TODO(verus): want to mix a spec-ensures here!
        // ensures self.i().can_crop(depth),
        self.crop(depth).can_discard_to(new_bdy),
    ensures
        self.i().crop_head_records(depth).can_discard_to(new_bdy),    // spec(checked) prereq
        self.i().crop_head_records(depth).discard_old_defn(new_bdy) == self.crop(depth).discard_old(new_bdy).i(),
    {
        // Proof plan:
        // Show that both can_crop and discard_old commute with i; then apply a generic
        // commute_transitivity lemma to show that the composition of both itself commutes with i.
        let dummy = Self::mkfs();   // invalid inputs need to all map to a common value to make the
                                    // math work out
        let i = |tj: LinkedJournal_v::TruncatedJournal|
            if tj.decodable() { tj.i() } else { dummy.i() };
        let f = |tj: LinkedJournal_v::TruncatedJournal|
            if tj.decodable() && tj.can_crop(depth) { tj.crop(depth) } else { dummy };
        let g = |tj: LinkedJournal_v::TruncatedJournal|
            if tj.decodable() && tj.can_discard_to(new_bdy) { tj.discard_old(new_bdy) } else { dummy };
        let F = |itj: PagedJournal_v::TruncatedJournal|
            if PagedJournal_v::JournalRecord::opt_rec_can_crop_head_records(itj.freshest_rec, itj.boundary_lsn, depth)
                { itj.crop_head_records(depth) } else { dummy.i() };
        let G = |itj: PagedJournal_v::TruncatedJournal|
            if itj.wf() && itj.can_discard_to(new_bdy) { itj.discard_old_defn(new_bdy) } else { dummy.i() };
        
        Self::mkfs_refines();   // didn't need this in dafny (spec(checked) ensures?). Both foralls below
                                // depend on it.

        assert forall |tjx| i(f(tjx))== #[trigger] F(i(tjx)) by {
            if tjx.decodable() && tjx.can_crop(depth) {
                tjx.disk_view.pointer_after_crop_commutes_with_interpretation_no_some(tjx.freshest_rec, depth);
                tjx.crop_ensures(depth);  // new spec(checked) ensures
            } else {
                if tjx.decodable() {
                    if tjx.i().can_crop(depth) {
                        tjx.paged_tj_can_crop_implies_linked_tj_can_crop(depth);
                    }
                }
            }
        }

        // This 5-liner in Dafny involved 37 lines of debugging to find the 2 missing lines due to no
        // spec(checked) ensures
        assert forall |tjx| i(g(tjx))== #[trigger] G(i(tjx)) by {
            if tjx.decodable() && tjx.can_discard_to(new_bdy) {
                tjx.discard_old_commutes(new_bdy);
                tjx.iwf();  // new spec(checked) ensures
            } 
        }

        Self::commute_transitivity(i, f, F, g, G);

        self.crop_ensures(depth);   // typcial infuriating missing spec(checked) ensures
        self.crop(depth).discard_old_decodable(new_bdy);    // Dafny didn't need it ... which is surprising
        self.disk_view.pointer_after_crop_commutes_with_interpretation_no_some(self.freshest_rec, depth);   // Dafny didn't need it ... which is surprising
        self.i().crop_head_records_ensures(depth);  // typical infuriating missing spec(checked) ensures
        assert( G(F(i(self))) == self.i().crop_head_records(depth).discard_old_defn(new_bdy) ); // trigger

        self.linked_tj_can_crop_implies_paged_tj_can_crop(depth);
        self.crop_decreases_seq_end(depth);
    }
}

impl LinkedJournal::Label {
    pub open spec(checked) fn wf(self) -> bool
    {
        match self {
            Self::FreezeForCommit{frozen_journal} => frozen_journal.decodable(),
            _ => true,
        }
    }

    pub open spec(checked) fn i(self) -> PagedJournal::Label
    recommends
        self.wf(),
    {
        match self {
            Self::ReadForRecovery{messages} => PagedJournal::Label::ReadForRecovery{messages},
            Self::FreezeForCommit{frozen_journal} => PagedJournal::Label::FreezeForCommit{frozen_journal: frozen_journal.i()},
            Self::QueryEndLsn{end_lsn} => PagedJournal::Label::QueryEndLsn{end_lsn},
            Self::Put{messages} => PagedJournal::Label::Put{messages},
            Self::DiscardOld{start_lsn, require_end} => PagedJournal::Label::DiscardOld{start_lsn, require_end},
            Self::Internal{} => PagedJournal::Label::Internal{},
        }
    }

}

impl LinkedJournal::State {
    pub open spec(checked) fn i(self) -> PagedJournal::State
    {
        if self.wf() && self.truncated_journal.disk_view.acyclic() {
            PagedJournal::State{
                truncated_journal: self.truncated_journal.i(),
                unmarshalled_tail: self.unmarshalled_tail,
            }
        } else {
            //choose |v| PagedJournal::State::init(v)
            arbitrary()
        }
    }

    pub proof fn iwf(self)
    requires
        self.wf(),
        self.truncated_journal.disk_view.acyclic(),
    ensures
        self.i().wf(),
    {
        self.truncated_journal.iwf();
//        assert( self.i().truncated_journal.wf() );
    }

    pub proof fn freeze_for_commit_refines(self, post: Self, lbl: LinkedJournal::Label, step: LinkedJournal::Step)
    requires
        self.inv(),
        LinkedJournal::State::next_by(self, post, lbl, step),
        step.is_freeze_for_commit(),
    ensures
        PagedJournal::State::next(self.i(), post.i(), lbl.i()),
    {
        reveal(PagedJournal::State::next_by);    // unfortunate defaults
        reveal(PagedJournal::State::next);       // unfortunate defaults
        reveal(LinkedJournal::State::next_by);   // unfortunate defaults

        let fj = lbl->frozen_journal;
        let new_bdy = fj.disk_view.boundary_lsn;
        let depth = step.get_freeze_for_commit_0(); // ew. Using Steps in lemmas sucks. Another mismatch with Rust's
                                                    // match-everything-all-the-time style. Change Step() to Step{}?
        let tj = self.truncated_journal;
        let tjd = self.truncated_journal.disk_view;

        tjd.pointer_after_crop_commutes_with_interpretation_no_some(tj.freshest_rec, depth);
        tj.crop_head_composed_with_discard_old_commutes(new_bdy, depth);
        let cropped_ptr = tjd.pointer_after_crop(tj.freshest_rec, depth);
        let cropped_tj = LinkedJournal_v::TruncatedJournal{freshest_rec: cropped_ptr, disk_view: tjd};
        tjd.pointer_after_crop_ensures(tj.freshest_rec, depth); // another lost spec-ensures that wasted time digging up

        fj.iwf();  // another lost spec-ensures that wasted time digging up
        self.i().truncated_journal.crop_head_records_wf_lemma(depth); // another lost spec-ensures that wasted time digging up

        let post_discard = cropped_tj.discard_old(new_bdy);
        fj.disk_view.sub_disk_interp(post_discard.disk_view, post_discard.freshest_rec);

        assert( PagedJournal::State::next_by(self.i(), post.i(), lbl.i(), PagedJournal::Step::freeze_for_commit(depth)) );  // trigger
    }

    /// NOTE(Jialin): temp creation just to expose submodule inv
    pub proof fn inv_next(self, post: Self, lbl: LinkedJournal::Label, step: LinkedJournal::Step)
    requires
        self.inv(),
        LinkedJournal::State::next_by(self, post, lbl, step),
    ensures
        post.inv(),
    {
        reveal(LinkedJournal::State::next_by);   // unfortunate defaults
        match step {
            LinkedJournal::Step::discard_old(new_tj) =>  {
                Self::discard_old_inductive(self, post, lbl, new_tj);
            }
            LinkedJournal::Step::internal_journal_marshal(cut, addr) =>  {
                Self::internal_journal_marshal_inductive(self, post, lbl, cut, addr);
            }
            _ => { }
        }
    }

    pub proof fn discard_old_refines(self, post: Self, lbl: LinkedJournal::Label, step: LinkedJournal::Step)
    requires
        self.inv(),
        post.inv(),
        LinkedJournal::State::next_by(self, post, lbl, step),
        step.is_discard_old(),
    ensures
        PagedJournal::State::next(self.i(), post.i(), lbl.i()),
    {
        reveal(PagedJournal::State::next_by);    // unfortunate defaults
        reveal(PagedJournal::State::next);       // unfortunate defaults
        reveal(LinkedJournal::State::next_by);   // unfortunate defaults

        // self.inv_next(post, lbl, step);
        let lsn = lbl->start_lsn;

        if !(self.unmarshalled_tail.seq_start <= lsn) {
            let cropped_tj = self.truncated_journal.discard_old(lsn);
            self.truncated_journal.disk_view.discard_interp(lsn, cropped_tj.disk_view, self.truncated_journal.freshest_rec);
            // DiskView::tight_interp(cropped_tj.disk_view, cropped_tj.freshest_rec, post.truncated_journal.disk_view);
            post.truncated_journal.disk_view.sub_disk_interp(cropped_tj.disk_view, cropped_tj.freshest_rec);
        }
        assert( PagedJournal::State::next_by(self.i(), post.i(), lbl.i(), PagedJournal::Step::discard_old()) );  // trigger
    }

    pub proof fn next_refines(self, post: Self, lbl: LinkedJournal::Label)
    requires
        self.inv(),
        post.inv(),
        LinkedJournal::State::next(self, post, lbl),
    ensures
        PagedJournal::State::next(self.i(), post.i(), lbl.i()),
    {
        reveal(PagedJournal::State::next_by);    // unfortunate defaults
        reveal(PagedJournal::State::next);    // unfortunate defaults
        reveal(LinkedJournal::State::next_by);
        reveal(LinkedJournal::State::next);

        let step = choose |step| LinkedJournal::State::next_by(self, post, lbl, step);
//         assert( LinkedJournal::State::next_by(self, post, lbl, step) );
        // self.inv_next(post, lbl, step);
        match step {
            LinkedJournal::Step::read_for_recovery(depth) =>  {
                let tj = self.truncated_journal;
                let tjd = self.truncated_journal.disk_view;
                tjd.pointer_after_crop_commutes_with_interpretation(
                    tj.freshest_rec, tjd.boundary_lsn, depth);
                tjd.pointer_after_crop_ensures(tj.freshest_rec, depth); // GAAAAH weeks looking for this awful thing

                assert( PagedJournal::State::next_by(self.i(), post.i(), lbl.i(), PagedJournal::Step::read_for_recovery(depth)) );
            }
            LinkedJournal::Step::freeze_for_commit(depth) =>  {
                self.freeze_for_commit_refines(post, lbl, step);
            }
            LinkedJournal::Step::query_end_lsn() =>  {
                assert( PagedJournal::State::next_by(self.i(), post.i(), lbl.i(), PagedJournal::Step::query_end_lsn()) );
            }
            LinkedJournal::Step::put() =>  {
                assert( PagedJournal::State::next_by(self.i(), post.i(), lbl.i(), PagedJournal::Step::put()) );
            }
            LinkedJournal::Step::discard_old(_) =>  {
                self.discard_old_refines(post, lbl, step);
            }
            LinkedJournal::Step::internal_journal_marshal(cut, addr) =>  {
                self.truncated_journal.disk_view.iptr_framing(post.truncated_journal.disk_view, self.truncated_journal.freshest_rec);
                assert( PagedJournal::State::next_by(self.i(), post.i(), lbl.i(), PagedJournal::Step::internal_journal_marshal(cut)) ); // trigger
            }
            LinkedJournal::Step::internal_no_op() =>  {
                assert( PagedJournal::State::next_by(self.i(), post.i(), lbl.i(), PagedJournal::Step::internal_no_op()) );
            }
            _ => { assert(false); }
        }
    }

    pub proof fn init_refines(self, truncated_journal: TruncatedJournal) 
    requires LinkedJournal::State::initialize(self, truncated_journal)
    ensures PagedJournal::State::initialize(self.i(), truncated_journal.i())
    {
        truncated_journal.iwf();
    }
}

} // verus!
