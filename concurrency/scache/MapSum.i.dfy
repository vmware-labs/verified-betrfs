module MapSum {
  function Choose<K(!new)>(m: map<K, nat>) : K
  requires m != map[]
  {
    var k :| k in m.Keys; k
  }

  function Sum<K(!new)>(m: map<K, nat>) : nat
  {
    if m == map[]
      then 0
      else (
        var k := Choose(m);
        Sum(m - {k}) + m[k]
      )
  }

  lemma SumInduct<K(!new)>(m: map<K, nat>, k: K, n: nat)
  requires k !in m
  ensures Sum(m[k := n]) == Sum(m) + n
  decreases |m|
  {
    assert m[k := n] != map[] by {
      assert k in m[k := n];
      var empty_map: map<K, nat> := map[];
      assert k !in empty_map;
    }
    var c := Choose(m[k := n]);
    if c == k {
      assert m[k := n] - {k} == m;
    } else {
      calc {
        Sum(m[k := n]);
        Sum(m[k := n] - {c}) + m[k := n][c];
        Sum(m[k := n] - {c}) + m[c];
        { assert m[k := n] - {c} == (m - {c})[k := n]; }
        Sum((m - {c})[k := n]) + m[c];
        {
          assert m == (m - {c})[c := m[c]];
          assert |m| == |m - {c}| + 1;
          assert |m - {c}| < |m|;
          SumInduct(m - {c}, k, n);
        }
        Sum(m - {c}) + n + m[c];
        {
          SumInduct(m - {c}, c, m[c]);
          assert (m - {c})[c := m[c]] == m;
        }
        Sum(m) + n;
      }
    }
  }

  lemma SumAllZeroesIsZero<K(!new)>(p: map<K, nat>)
  requires forall k | k in p :: p[k] == 0
  ensures Sum(p) == 0
  {
    if p == map[] {
    } else {
      var k := Choose(p);
      SumInduct(p - {k}, k, 0);
      assert (p - {k})[k := 0] == p;
      SumAllZeroesIsZero(p - {k});
    }
  }

  function GetOrZero<K(!new)>(m: map<K, nat>, k: K) : nat {
    if k in m then m[k] else 0
  }

  lemma SumAdditive<K(!new)>(m: map<K, nat>, p: map<K, nat>, q: map<K, nat>)
  requires forall k ::
    GetOrZero(p, k) + GetOrZero(q, k) == GetOrZero(m, k)
  ensures Sum(m) == Sum(p) + Sum(q)
  {
    if m == map[] {
      assert forall k | k in p :: GetOrZero(p, k) == 0 ==> p[k] == 0;
      assert forall k | k in q :: GetOrZero(q, k) == 0 ==> q[k] == 0;
      SumAllZeroesIsZero(p);
      SumAllZeroesIsZero(q);
      assert Sum(m) == Sum(p) + Sum(q);
    } else {
      var k := Choose(m);
      var m1 := m - {k};
      var p1 := p - {k};
      var q1 := q - {k};

      SumInduct(m1, k, m[k]); 
      assert m1[k := m[k]] == m;

      if k in p {
        SumInduct(p1, k, p[k]); 
        assert p1[k := p[k]] == p;
      } else {
        assert p1 == p;
      }

      if k in q {
        SumInduct(q1, k, q[k]); 
        assert q1[k := q[k]] == q;
      } else {
        assert q1 == q;
      }

      assert forall k :: GetOrZero(p, k) + GetOrZero(q, k) == GetOrZero(m, k)
          ==> GetOrZero(p1, k) + GetOrZero(q1, k) == GetOrZero(m1, k);
      SumAdditive(m1, p1, q1);

      assert GetOrZero(p, k) + GetOrZero(q, k) == GetOrZero(m, k);
    }
  }
}
