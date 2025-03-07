// Copyright 2018-2024 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, University of Washington
// SPDX-License-Identifier: BSD-2-Clause

#![allow(unused_imports)]
use builtin::*;
use vstd::prelude::*;
use vstd::{map::*,multiset::*};
use crate::disk::GenericDisk_v::*;

verus!{
    pub type Likes = Multiset<Address>;

    pub type AULikes = Multiset<AU>;

    pub open spec(checked) fn no_likes() -> Likes
    {
        Multiset::empty()
    }

    pub open spec(checked) fn all_elems_single<V>(m: Multiset<V>) -> bool
    {
        forall |e| #[trigger] m.contains(e) ==> m.count(e) == 1
    }

    pub closed spec(checked) fn to_au_likes(likes: Likes) -> AULikes
        decreases likes.len()
    {
        if likes.is_empty() {
            Multiset::empty()
        } else {
            let e = likes.choose();
            to_au_likes(likes.remove(e)).insert(e.au)
        }
    }

    pub proof fn to_au_likes_domain(likes: Likes) 
        ensures 
            forall |addr| #[trigger] likes.contains(addr) ==> to_au_likes(likes).contains(addr.au),
            to_au_likes(likes).dom() == to_aus(likes.dom()),
        decreases likes.len()
    {
        if likes.len() > 0 {
            let e = likes.choose();
            to_au_likes_domain(likes.remove(e));

            assert forall |addr| #[trigger] likes.contains(addr)
            implies to_au_likes(likes).contains(addr.au)
            by {
                if addr != e {
                    assert(likes.remove(e).contains(addr)); // trigger
                    assert(to_au_likes(likes.remove(e)).contains(addr.au));
                    assert(to_au_likes(likes.remove(e)) <= to_au_likes(likes));
                }
            }

            to_aus_singleton(e);
            to_au_likes_singleton(e);
            assert(Multiset::singleton(e.au).dom() == set!{e.au});

            to_aus_additive(likes.remove(e).dom(), set!{e});
            assert(likes.dom() == likes.remove(e).dom() + set!{e});
            to_au_likes_commutative_over_add(likes.remove(e), Multiset::singleton(e));
            assert(to_au_likes(likes).dom() == to_au_likes(likes.remove(e)).dom() + to_au_likes(Multiset::singleton(e)).dom()); // trigger
        } else {
            assert(likes.dom() == Set::<Address>::empty());
            assert(to_au_likes(likes).dom() == Set::<AU>::empty());
            assert(to_aus(likes.dom()) == Set::<AU>::empty());
        }
    }

    pub proof fn to_au_likes_singleton(addr: Address) 
        ensures to_au_likes(Multiset::singleton(addr)) == Multiset::singleton(addr.au)
    {
        assert(Multiset::singleton(addr).choose() == addr);
        assert(Multiset::singleton(addr).remove(addr) =~= Multiset::empty());
        assert(to_au_likes(Multiset::empty()) == Multiset::<AU>::empty());
        // TODO: seems like we need to assert this rather than relying on the ensures?
        assert(to_au_likes(Multiset::singleton(addr)) == Multiset::singleton(addr.au));
    }

    // NOTE: same proof as buffer_likes_additive, would be better if we can 
    // generalize this
    #[verifier::spinoff_prover]
    pub proof fn to_au_likes_commutative_over_add(likes: Likes, delta: Likes)
        ensures to_au_likes(likes.add(delta)) =~= to_au_likes(likes).add(to_au_likes(delta))
        decreases likes.len() + delta.len()
    {
        let total = likes.add(delta);

        if likes.len() == 0 {
            assert(total =~= delta);
        } else if delta.len() == 0 {
            assert(total =~= likes);
        } else {
            assert(total.len() > 0);
            let e = total.choose();
            let sub_au_likes = to_au_likes(total.remove(e));

            to_au_likes_singleton(e);
            if likes.contains(e) {
                to_au_likes_commutative_over_add(likes.remove(e), delta);
                assert(total.remove(e) == likes.remove(e).add(delta));
                to_au_likes_commutative_over_add(likes.remove(e), Multiset::singleton(e));
                assert(likes.remove(e).add(Multiset::singleton(e)) == likes);
            } else {
                assert(delta.contains(e));
                to_au_likes_commutative_over_add(likes, delta.remove(e));
                assert(total.remove(e) == likes.add(delta.remove(e))); // trigger
                to_au_likes_commutative_over_add(delta.remove(e), Multiset::singleton(e));
                assert(delta.remove(e).add(Multiset::singleton(e)) == delta);
            }
        }
    }

    pub proof fn to_au_likes_commutative_over_sub(likes: Likes, delta: Likes)
    requires delta <= likes
    ensures to_au_likes(likes.sub(delta)) == to_au_likes(likes).sub(to_au_likes(delta))
    {
        to_au_likes_commutative_over_add(likes.sub(delta), delta);
        assert(likes.sub(delta).add(delta) == likes); // trigger
        assert(to_au_likes(likes.sub(delta)) == to_au_likes(likes).sub(to_au_likes(delta)));
    }


    // pub proof fn single_elems_add<V>(a: Multiset<V>, b: Multiset<V>)
    // requires 
    //     all_elems_single(a),
    //     all_elems_single(b),
    //     a.is_disjoint_from(b),
    // ensures
    //     all_elems_single(a.add(b)),
    //     a.add(b).dom() == a.dom() + b.dom()
    // {
    //     let r = a.add(b);
    //     assert forall |e| #[trigger] r.contains(e)
    //     implies r.count(e) == 1 by
    //     {
    //         assert(a.contains(e) || b.contains(e)); // trigger
    //     }
    // }

    // pub proof fn single_elems_sub<V>(a: Multiset<V>, b: Multiset<V>)
    // requires 
    //     all_elems_single(a),
    //     b <= a,
    // ensures
    //     all_elems_single(a.sub(b)),
    //     a.sub(b).dom() =~= a.dom() - b.dom()
    // {
    //     let r = a.sub(b);
    //     let r_dom = a.dom() - b.dom();
    //     assert forall |e| r.contains(e)
    //     implies r.count(e) == 1 && r_dom.contains(e) 
    //     by {
    //         assert(a.contains(e)); // trigger
    //     }
    // }

    // pub proof fn single_elems_eq<V>(a: Multiset<V>, b: Multiset<V>)
    // requires 
    //     all_elems_single(a),
    //     all_elems_single(b),
    //     a.dom() =~= b.dom(),
    // ensures
    //     a == b
    // {
    //     assert forall |v: V| a.count(v) == b.count(v)
    //     by {
    //         if a.contains(v) {
    //             assert(b.dom().contains(v)); 
    //             assert(b.contains(v)); // trigger
    //         } else if b.contains(v) {
    //             assert(a.dom().contains(v)); 
    //             assert(false);
    //         } 
    //     }
    //     assert(a =~= b);
    // }

    // pub proof fn single_elems_insert_ensures<V>(m: Multiset<V>, new: V)
    // requires all_elems_single(m), !m.contains(new)
    // ensures all_elems_single(m.insert(new))
    // {
    //     let post_m = m.insert(new);
    //     assert forall |e| #[trigger] post_m.contains(e)
    //     implies post_m.count(e) == 1
    //     by {
    //         if e != new {
    //             assert(m.contains(e)); // trigger
    //         }
    //     }
    // }

    // pub proof fn single_elems_subset<V>(a: Multiset<V>, b: Multiset<V>)
    // requires all_elems_single(a), all_elems_single(b), a.dom() <= b.dom()
    // ensures a <= b 
    // {
    //     assert forall |e| true
    //     implies a.count(e) <= b.count(e)
    //     by {
    //         if a.contains(e) {
    //             assert(a.dom().contains(e));
    //             assert(b.contains(e));
    //             assert(b.count(e) == a.count(e));
    //         }
    //     }
    // }

    // pub proof fn single_elems_disjoint<V>(a: Multiset<V>, b: Multiset<V>)
    // requires all_elems_single(a), all_elems_single(b), a.dom().disjoint(b.dom())
    // ensures a.is_disjoint_from(b), all_elems_single(a.add(b)),
    // {
    //     assert forall |e| true
    //     implies a.count(e) == 0 || b.count(e) == 0
    //     by {
    //         if a.count(e) > 0 {
    //             assert(a.dom().contains(e));
    //             assert(!b.dom().contains(e));
    //         }
    //     }
    //     assert(a.is_disjoint_from(b));

    //     assert forall |e| #[trigger] a.add(b).contains(e)
    //     implies a.add(b).count(e) == 1
    //     by {
    //         if a.contains(e) {
    //             assert(!b.contains(e));
    //         } else {
    //             assert(b.contains(e));
    //         }
    //     }
    // }
}
