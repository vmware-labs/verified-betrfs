module HashTable {
  const L: nat

  type Key
  type Value

  function Hash(k: Key) : nat

  datatype KV =
      | KV(key: Key, value: Value)
      | Empty

  datatype Option<V> = Some(value: V) | None

  datatype M =
    | M(ghost s: map<nat, KV>,
        ghost m: map<Key, Option<Value>>)
    | Bot

  function map_union<K,V>(m1: map<K,V>, m2: map<K,V>) : map<K,V> {
    map k | k in m1.Keys + m2.Keys ::
        (if k in m1.Keys then m1[k] else m2[k])
  }

  function dot(a: M, b: M) : M {
    if a == Bot || b == Bot then
      Bot
    else if a.m.Keys !! b.m.Keys && a.s.Keys !! b.s.Keys then
      M(map_union(a.s, b.s), map_union(a.m, b.m))
    else
      Bot
  }

  function unit() : M {
    M(map[], map[])
  }

  lemma dot_commutative(a: M, b: M)
  ensures dot(a, b) == dot(b, a)
  {
    if a == Bot || b == Bot {
    } else if a.m.Keys !! b.m.Keys && a.s.Keys !! b.s.Keys {
      assert map_union(a.s, b.s) == map_union(b.s, a.s);
      assert map_union(a.m, b.m) == map_union(b.m, a.m);
    } else {
    }
  }

  lemma dot_associative(a: M, b: M, c: M)
  ensures dot(a, dot(b, c)) == dot(dot(a, b), c)
  {
    if dot(a, dot(b, c)) == Bot {
    } else {
    }
  }

  lemma dot_unit(a: M)
  ensures dot(a, unit()) == a
  {
  }

  predicate LBound(a: M)
  {
    && a != Bot
    && (forall i :: i in a.s ==> 0 <= i < L)
  }

  predicate KeysDistinct(a: M)
  {
    && a != Bot   
    && (forall i1, i2 :: i1 in a.s && i2 in a.s && i1 != i2
        && a.s[i1].KV?
        && a.s[i2].KV? ==> a.s[i1].key != a.s[i2].key)
  }

  predicate MapConsistent(a: M)
  {
    && a != Bot
    && (forall k :: k in a.m && a.m[k].Some? ==>
        exists i :: i in a.s && a.s[i] == KV(k, a.m[k].value))
  }

  predicate SlotsConsistent(a: M)
  {
    && a != Bot
    && (forall i :: i in a.s && a.s[i].KV? ==>
        a.s[i].key in a.m && a.m[a.s[i].key] != None)
  }

  predicate RangeFull(a: M, i: nat)
  requires a != Bot
  requires i in a.s
  requires a.s[i].KV?
  {
    forall j :: Hash(a.s[i].key) <= j <= i ==> j in a.s && a.s[j].KV?
  }

  predicate Contiguous(a: M)
  {
    && a != Bot
    && (forall i :: i in a.s && a.s[i].KV? ==>
        && Hash(a.s[i].key) <= i
        && RangeFull(a, i)
    )
  }

  predicate P(a: M)
  {
    && LBound(a)
    && KeysDistinct(a)
    && MapConsistent(a)
    && SlotsConsistent(a)
    && Contiguous(a)
  }

  function s(i: nat, e: KV) : M {
    M(map[i := e], map[])
  }

  function m(k: Key, v: Option<Value>) : M {
    M(map[], map[k := v])
  }

  predicate Full(a: M, k: Key, i: nat, j: nat)
  {
    && i <= j
    && a != Bot
    && (forall l :: i <= l < j ==> l in a.s && a.s[l].KV? && a.s[l].key != k)
    && (forall l :: l in a.s ==> i <= l < j)
    && a.m == map[]
  }

  lemma QueryFound(j: nat, k: Key, v0: Value, v: Option<Value>, p: M)
  requires P(dot(
    dot(s(j, KV(k, v0)), m(k, v)),
    p))
  ensures v == Some(v0)
  {
    var a := dot(dot(s(j, KV(k, v0)), m(k, v)), p);
    assert a.s[j].KV?;
    assert a.m[k].Some?;
    var i :| i in a.s && a.s[i] == KV(k, a.m[k].value);
    assert i == j;
  }

  lemma QueryReachedEnd(k: Key, a: M, v: Option<Value>, p: M)
  requires Full(a, k, Hash(k), L)
  requires P(dot(
    dot(a, m(k, v)),
    p))
  ensures v == None
  {
    var a := dot(dot(a, m(k, v)), p);
    if v.Some? {
      var i :| i in a.s && a.s[i] == KV(k, a.m[k].value);
      assert i >= L;
      assert i < L;
      assert false;
    }
  }

  lemma QueryNotFound(k: Key, a: M, v: Option<Value>, j: nat, p: M)
  requires Full(a, k, Hash(k), j)
  requires P(dot(
      dot(dot(a, s(j, Empty)), m(k, v)),
      p))
  ensures v == None
  {
    var a := dot(dot(dot(a, s(j, Empty)), m(k, v)), p);
    if v.Some? {
      var i :| i in a.s && a.s[i] == KV(k, a.m[k].value);
      if i < j {
        if i < Hash(k) {
          assert a.s[i].KV?;
          assert Hash(a.s[i].key) <= i;
          assert false;
        } else {
          assert false;
        }
      } else if i >= j {
        assert RangeFull(a, i);
        assert Hash(a.s[i].key) <= j <= i;
        assert a.s[j].KV?;
        assert false;
      }
      assert i == j;
      assert false;
    }
  }

  lemma UpdateExisting(j: nat, k: Key, v0: Option<Value>, v1: Value, v: Value, p: M)
  requires P(dot(dot(s(j, KV(k, v1)), m(k, v0)), p))
  ensures P(dot(dot(s(j, KV(k, v)), m(k, Some(v))), p))
  {
    var a := dot(dot(s(j, KV(k, v1)), m(k, v0)), p);
    var a' := dot(dot(s(j, KV(k, v)), m(k, Some(v))), p);

    assert P(a);

    assert forall i :: i in a'.s <==> i in a.s;
    assert forall k0 :: k0 in a'.m <==> k0 in a.m;

    assert LBound(a');
    assert KeysDistinct(a');

    assert MapConsistent(a') by {
      forall k0 | k0 in a'.m && a'.m[k0].Some?
      ensures exists i :: i in a'.s && a'.s[i] == KV(k0, a'.m[k0].value)
      {
        if k0 == k {
          assert j in a'.s && a'.s[j] == KV(k0, a'.m[k0].value);
        } else {
          var i :| i in a.s && a.s[i] == KV(k0, a.m[k0].value);
          assert i in a'.s && a'.s[i] == KV(k0, a'.m[k0].value);
        }
      }
    }

    assert SlotsConsistent(a');

    assert Contiguous(a') by {
      forall i | i in a'.s && a'.s[i].KV?
      ensures Hash(a'.s[i].key) <= i
      ensures RangeFull(a', i)
      {
        assert Hash(a.s[i].key) <= i;
        assert RangeFull(a, i);
        forall l | Hash(a'.s[i].key) <= l <= i ensures l in a'.s && a'.s[l].KV?
        {
        }
      }
    }
  }

  lemma UpdateNew(j: nat, k: Key, v0: Option<Value>, v: Value, a: M, p: M)
  requires Full(a, k, Hash(k), j)
  requires P(dot(dot(dot(a, s(j, Empty)), m(k, v0)), p))
  ensures P(dot(dot(dot(a, s(j, KV(k, v))), m(k, Some(v))), p))
  {
    var x := dot(dot(a, s(j, Empty)), m(k, v0));
    var y := dot(dot(a, s(j, KV(k, v))), m(k, Some(v)));
    var a := dot(x, p);
    var a' := dot(y, p);

    assert P(a);

    assert a' != Bot by {
      assert x != Bot;
      assert dot(x, p) != Bot;
    }

    assert forall i :: i in a'.s <==> i in a.s;
    assert forall k0 :: k0 in a'.m <==> k0 in a.m;

    assert LBound(a');
    assert KeysDistinct(a');

    assert MapConsistent(a') by {
      forall k0 | k0 in a'.m && a'.m[k0].Some?
      ensures exists i :: i in a'.s && a'.s[i] == KV(k0, a'.m[k0].value)
      {
        if k0 == k {
          assert j in a'.s && a'.s[j] == KV(k0, a'.m[k0].value);
        } else {
          var i :| i in a.s && a.s[i] == KV(k0, a.m[k0].value);
          assert i in a'.s && a'.s[i] == KV(k0, a'.m[k0].value);
        }
      }
    }

    assert SlotsConsistent(a');

    assert Contiguous(a') by {
      forall i | i in a'.s && a'.s[i].KV?
      ensures Hash(a'.s[i].key) <= i
      ensures RangeFull(a', i)
      {
        if i == j {
          assert Hash(a'.s[i].key) <= i;
          assert RangeFull(a', i);
        } else {
          assert Hash(a.s[i].key) <= i;
          assert RangeFull(a, i);
          forall l | Hash(a'.s[i].key) <= l <= i ensures l in a'.s && a'.s[l].KV?
          {
          }
        }
      }
    }
  }
}
