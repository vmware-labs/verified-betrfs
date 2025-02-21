// Copyright 2018-2024 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, University of Washington
// SPDX-License-Identifier: BSD-2-Clause

use builtin_macros::*;
use vstd::prelude::*;

verus! {

pub open spec(checked) fn union_seq_of_sets<A>(sets: Seq<Set<A>>) -> Set<A>
{
    sets.fold_left(Set::empty(), |u: Set<A>, s| u.union(s))
}

pub proof fn lemma_union_seq_of_sets_finite<A>(sets: Seq<Set<A>>)
    requires forall |i| 0 <= i < sets.len() ==> (#[trigger] sets[i]).finite()
    ensures union_seq_of_sets(sets).finite()
    decreases sets.len()
{
    if sets.len() > 0 {
        lemma_union_seq_of_sets_finite(sets.drop_last());
    }
}

pub proof fn lemma_set_subset_of_union_seq_of_sets<A>(sets: Seq<Set<A>>, a: A)
    requires exists |i| 0 <= i < sets.len() && (#[trigger] sets[i]).contains(a)
    ensures union_seq_of_sets(sets).contains(a)
    decreases sets.len()
{
//    assert(sets.len() > 0);
    assert(union_seq_of_sets(sets) == union_seq_of_sets(sets.drop_last()).union(sets.last()));
    let i = choose |i| 0 <= i < sets.len() && (#[trigger] sets[i]).contains(a);
    if i < sets.len() - 1 {
        assert(0 <= i < sets.drop_last().len() && (#[trigger] sets.drop_last()[i]).contains(a));
        lemma_set_subset_of_union_seq_of_sets(sets.drop_last(), a);
    }
}

pub proof fn lemma_union_seq_of_sets_contains<A>(sets: Seq<Set<A>>, a: A)
    requires union_seq_of_sets(sets).contains(a)
    ensures exists |i| 0 <= i < sets.len() && (#[trigger] sets[i]).contains(a)
    decreases sets.len()
{
//    assert(sets.len() > 0);
//    assert(union_seq_of_sets(sets) == union_seq_of_sets(sets.drop_last()).union(sets.last()));
    if sets.last().contains(a) {
    } else {
        lemma_union_seq_of_sets_contains(sets.drop_last(), a);
    }
}

pub proof fn lemma_to_set_distributes_over_plus<A>(a: Seq<A>, b: Seq<A>)
    ensures
        (a + b).to_set() == a.to_set().union(b.to_set())
{
    assert forall |x| a.to_set().union(b.to_set()).contains(x)
    implies #[trigger] (a + b).to_set().contains(x) by {
//        assert(a.to_set().contains(x) || b.to_set().contains(x));
        if (a.to_set().contains(x)) {
//            assert(a.contains(x));
            let i = a.index_of(x);
            assert((a + b)[i] == x);
        } else {
//            assert(b.to_set().contains(x));
//            assert(b.contains(x));
            let i = b.index_of(x);
            assert((a + b)[a.len() + i] == x);
        }
//        assert((a + b).contains(x));
    }
    assert((a + b).to_set() == a.to_set().union(b.to_set()));
}

pub proof fn lemma_subset_finite<A>(a: Set<A>, b: Set<A>)
    requires
        a.finite(),
        b <= a,
    ensures
        b.finite(),
{
    assert(b == a.intersect(b));
}

}
