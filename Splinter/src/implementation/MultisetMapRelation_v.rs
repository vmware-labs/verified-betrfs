#[allow(unused_imports)]    // lost in erasure
use builtin::*;
use vstd::prelude::*;

use vstd::{multiset::Multiset};

verus!{

pub open spec(checked) fn all_elems_single<V>(m: Multiset<V>) -> bool
{
    forall |e| #[trigger] m.contains(e) ==> m.count(e) == 1
}

pub open spec fn multiset_to_map<K,V>(kvs: Multiset<(K,V)>) -> Map<K, V>
{
    Map::new(
        |k| exists |pr| #[trigger] kvs.contains(pr) && pr.0 == k,
        |k| {let pr = choose |pr| #[trigger] kvs.contains(pr) && pr.0 == k; pr.1}
    )
}

// For when a multiset is used as a concurrently-accessible map, as we do in
// KVStoreTokenized::sync_requests.
pub open spec(checked) fn unique_keys<K,V>(m: Multiset<(K,V)>) -> bool
{
    &&& all_elems_single(m)
    &&& forall |p1,p2| #[trigger] m.contains(p1) && #[trigger] m.contains(p2) ==> p1==p2 || p1.0 != p2.0
}

pub proof fn unique_multiset_insert<K,V>(pre: Multiset<(K,V)>, k: K, v: V)
requires
    unique_keys(pre),
    forall |p| #[trigger] pre.contains(p) ==> p.0 != k,
ensures
    unique_keys(pre.insert((k,v))),
{
    let post = pre.insert((k,v));

    assert forall |e| #[trigger] post.contains(e) implies post.count(e) == 1 by {
        if e.0 == k {
            if pre.count(e) >= 1 {  // find contradiction
                assert( pre.contains(e) );  // trigger old all_elems_single
            }
        } else {
            assert( pre.contains(e) );  // trigger old all_elems_single
        }
    }
    assert forall |p1,p2| #[trigger] post.contains(p1) && #[trigger] post.contains(p2)
        implies p1==p2 || p1.0 != p2.0 by {
        if p1!=p2 && p1.0 == p2.0 { // find contradictions
            if p1.0 == k {
                if p1.1 == v {
                    assert( pre.contains(p2) ); // trigger unique_keys(pre)
                } else {
                    assert( pre.contains(p1) ); // trigger unique_keys(pre)
                }
            } else {
                // trigger unique_keys(pre)
                assert( pre.contains(p1) );
                assert( pre.contains(p2) );
            }
        }
    }
}

pub proof fn unique_multiset_remove<K,V>(pre: Multiset<(K,V)>, k: K, v: V)
requires
    unique_keys(pre),
    pre.contains((k,v)),
ensures
    unique_keys(pre.remove((k,v))),
{
    let post = pre.remove((k,v));

    assert forall |e| #[trigger] post.contains(e) implies post.count(e) == 1 by {
        assert( pre.contains(e) );  // trigger old all_elems_single
    }
    assert forall |p1,p2| #[trigger] post.contains(p1) && #[trigger] post.contains(p2)
        implies p1==p2 || p1.0 != p2.0 by {
        if p1!=p2 && p1.0 == p2.0 { // find contradiction
            // trigger unique_keys(pre)
            assert( pre.contains(p1) );
            assert( pre.contains(p2) );
        }
    }
}

pub proof fn multiset_map_membership<K,V>(kvs: Multiset<(K,V)>, k: K, v: V)
requires
    unique_keys(kvs),
    kvs.contains((k,v)),
ensures
    multiset_to_map(kvs).contains_key(k),
    multiset_to_map(kvs)[k] == v,
{
}

pub proof fn unique_multiset_map_insert_equiv<K,V>(pre: Multiset<(K,V)>, k: K, v: V)
requires
    unique_keys(pre),
    !multiset_to_map(pre).contains_key(k),
ensures
    unique_keys(pre.insert((k,v))),
    multiset_to_map(pre.insert((k,v))) == multiset_to_map(pre).insert(k,v),
{
    unique_multiset_insert(pre, k, v);

    let mpre = multiset_to_map(pre);
    let post = pre.insert((k,v));
    let mpost = multiset_to_map(post);
    assert forall |k2| #![auto] mpre.contains_key(k2) implies mpost.contains_key(k2) && mpost[k2] == mpre[k2] by {
        multiset_map_membership(post, k2, mpre[k2]);
    }
    assert forall |k2| #![auto] mpost.contains_key(k2) && k2 != k implies mpre.contains_key(k2) && mpre[k2] == mpost[k2] by {
        multiset_map_membership(pre, k2, mpost[k2]);
    }
    multiset_map_membership(post, k, v);

    let mpre_i = mpre.insert(k, v);
    assert forall |k0| mpre_i.contains_key(k0) implies mpost.contains_key(k0) by {
        if k0 != k {
            assert( pre.contains((k0,mpre_i[k0])) );    // trigger
        }
    }
    assert forall |k0| mpost.contains_key(k0) implies mpre_i.contains_key(k0) by {
        assert( post.contains((k0, mpost[k0])) );   // trigger
    }
    assert( mpost == mpre_i );  // extn
}

pub open spec fn multiset_map_singleton<K,V>(k: K, v: V) -> (out: Multiset<(K,V)>)
{
    Multiset::empty().insert((k,v))
}

pub proof fn multiset_map_singleton_ensures<K,V>(k: K, v: V)
ensures
    multiset_to_map(multiset_map_singleton(k,v)) == Map::empty().insert(k,v),
{
    unique_multiset_map_insert_equiv(Multiset::empty(), k, v);
    assert( multiset_to_map(Multiset::<(K,V)>::empty()) == Map::<K,V>::empty() );   // extn equality
}

pub proof fn unique_multiset_map_remove_equiv<K,V>(pre: Multiset<(K,V)>, k: K, v: V)
requires
    unique_keys(pre),
    pre.contains((k, v)),
ensures
    unique_keys(pre.remove((k,v))),
    multiset_to_map(pre.remove((k,v))) == multiset_to_map(pre).remove(k),
{
    unique_multiset_remove(pre, k, v);

    let mpre = multiset_to_map(pre);
    let post = pre.remove((k,v));
    let mpost = multiset_to_map(post);
    let mpre_r = mpre.remove(k);
    assert forall |k0| mpre_r.contains_key(k0) implies mpost.contains_key(k0) by {
        assert( post.contains((k0, mpre_r[k0])) );
    }
    assert forall |k0| mpost.contains_key(k0) implies mpre_r.contains_key(k0) by {
        assert( pre.contains((k0, mpost[k0])) );   // trigger
    }

    assert forall |k0| #![auto] mpost.contains_key(k0) implies mpost[k0] == mpre_r[k0] by {
        let pr = choose |pr| #![auto] post.contains(pr) && pr.0==k0;
        assert( pre.contains(pr) );  // trigger
    }
    assert( mpost == mpre_r );  // extn
}

}//verus!
