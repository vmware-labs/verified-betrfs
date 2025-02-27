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
            Multiset::singleton(e.au).add(to_au_likes(likes.remove(e)))
        }
    }

    // to au likes says that they are identical
    // can ensure their len is the same
    // how do we ensure that the cardinality is the same when adding all aus together


    // have proof regarding the membership

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
