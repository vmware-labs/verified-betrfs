include "ResourceStateMachine.i.dfy"
include "Monoid.i.dfy"
include "MultisetLemmas.i.dfy"
include "../../lib/Base/Maps.i.dfy"
include "../../lib/Base/Multisets.i.dfy"

module SummaryMonoid refines MonoidMap {
  import opened KeyValueType
  import opened Options
  import opened Maps
  import MapIfc
  import HT = HTResource
  import Multisets
  import MultisetLemmas

  datatype QueryRes =
    | QueryFound(rid: int, key: Key, value: Option<Value>)
    | QueryUnknown(rid: int, key: Key)

  datatype Summary = Summary(
    ops: map<Key, Option<Value>>,
    stubs: multiset<HT.Stub>,
    queries: multiset<QueryRes>,
    removes: multiset<QueryRes>
  )

  type M = Summary

  function unit() : M {
    Summary(map[], multiset{}, multiset{}, multiset{})
  }

  function app_query(query: QueryRes, ops: map<Key, Option<Value>>) : QueryRes
  {
    match query {
      case QueryFound(_, _, _) => query
      case QueryUnknown(rid, key) => (
        if key in ops then (
          QueryFound(rid, key, ops[key])
        ) else (
          query
        )
      )
    }
  }

  function {:opaque} app_queries(
    queries: multiset<QueryRes>, ops: map<Key, Option<Value>>) : multiset<QueryRes>
  {
    Multisets.Apply((q) => app_query(q, ops), queries)
  }

  function add(x: M, y: M) : M {
    Summary(
        MapUnionPreferA(x.ops, y.ops),
        x.stubs + y.stubs,
        app_queries(x.queries, y.ops) + y.queries,
        app_queries(x.removes, y.ops) + y.removes)
  }

  lemma associative(x: M, y: M, z: M)
  ensures add(add(x, y), z) == add(x, add(y, z))
  {
    reveal_app_queries();
    calc {
      add(add(x, y), z).queries;
      app_queries(add(x, y).queries, z.ops) + z.queries;
      {
        calc {
          app_queries(add(x, y).queries, z.ops);
          app_queries(app_queries(x.queries, y.ops) + y.queries, z.ops);
          {
            Multisets.ApplyAdditive((q) => app_query(q, z.ops),
              app_queries(x.queries, y.ops),
              y.queries);
          }
          app_queries(app_queries(x.queries, y.ops), z.ops) + app_queries(y.queries, z.ops);
          {
            MultisetLemmas.ApplyCompose(
                (q) => app_query(q, y.ops),
                (q) => app_query(q, z.ops),
                (q) => app_query(q, MapUnionPreferA(y.ops, z.ops)), x.queries);
            //assert app_queries(app_queries(x.queries, y.ops), z.ops)
            //    == app_queries(x.queries, MapUnionPreferA(y.ops, z.ops));
          }
          app_queries(x.queries, MapUnionPreferA(y.ops, z.ops)) + app_queries(y.queries, z.ops);
        }
      }
      app_queries(x.queries, MapUnionPreferA(y.ops, z.ops)) + app_queries(y.queries, z.ops) + z.queries;
      {
        //assert add(y, z).ops == MapUnionPreferA(y.ops, z.ops);
        //assert add(y, z).queries == app_queries(y.queries, z.ops) + z.queries;
      }
      app_queries(x.queries, add(y, z).ops) + add(y, z).queries;
      add(x, add(y, z)).queries;
    }
    calc {
      add(add(x, y), z).removes;
      app_queries(add(x, y).removes, z.ops) + z.removes;
      {
        calc {
          app_queries(add(x, y).removes, z.ops);
          app_queries(app_queries(x.removes, y.ops) + y.removes, z.ops);
          {
            Multisets.ApplyAdditive((q) => app_query(q, z.ops),
              app_queries(x.removes, y.ops),
              y.removes);
          }
          app_queries(app_queries(x.removes, y.ops), z.ops) + app_queries(y.removes, z.ops);
          {
            MultisetLemmas.ApplyCompose(
                (q) => app_query(q, y.ops),
                (q) => app_query(q, z.ops),
                (q) => app_query(q, MapUnionPreferA(y.ops, z.ops)), x.removes);
            //assert app_queries(app_queries(x.removes, y.ops), z.ops)
            //    == app_queries(x.removes, MapUnionPreferA(y.ops, z.ops));
          }
          app_queries(x.removes, MapUnionPreferA(y.ops, z.ops)) + app_queries(y.removes, z.ops);
        }
      }
      app_queries(x.removes, MapUnionPreferA(y.ops, z.ops)) + app_queries(y.removes, z.ops) + z.removes;
      {
        //assert add(y, z).ops == MapUnionPreferA(y.ops, z.ops);
        //assert add(y, z).removes == app_queries(y.removes, z.ops) + z.removes;
      }
      app_queries(x.removes, add(y, z).ops) + add(y, z).removes;
      add(x, add(y, z)).removes;
    }
  }

  lemma add_unit(x: M)
  ensures add(x, unit()) == x
  ensures add(unit(), x) == x
  {
    reveal_app_queries();
    MultisetLemmas.ApplyId((q) => app_query(q, map[]), x.queries);
    MultisetLemmas.ApplyId((q) => app_query(q, map[]), x.removes);
  }

  type Q = Option<HT.Info>

  function get_summary(info: HT.Info) : Summary {
    match info {
      case Info(Empty(), Free()) => unit()
      case Info(Full(kv), Free()) => Summary(
        map[kv.key := Some(kv.val)],
        multiset{},
        multiset{},
        multiset{}
      )

      case Info(Empty(), Inserting(rid, ins_kv, init_key)) =>
        Summary(
          map[ins_kv.key := Some(ins_kv.val)],
          multiset{HT.Stub(rid, MapIfc.InsertOutput(true))},
          multiset{},
          multiset{}
        )

      case Info(Full(kv), Inserting(rid, ins_kv, init_key)) =>
        Summary(
          map[kv.key := Some(kv.val)][ins_kv.key := Some(ins_kv.val)],
          multiset{HT.Stub(rid, MapIfc.InsertOutput(true))},
          multiset{},
          multiset{}
        )

      case Info(Empty(), Removing(rid, remove_key)) =>
        Summary(
          map[remove_key := None],
          multiset{},
          multiset{},
          multiset{QueryUnknown(rid, remove_key)}
        )

      case Info(Full(kv), Removing(rid, remove_key)) =>
        Summary(
          map[kv.key := Some(kv.val)][remove_key := None],
          multiset{},
          multiset{},
          (if kv.key == remove_key
            then multiset{QueryFound(rid, remove_key, Some(kv.val))}
            else multiset{QueryUnknown(rid, remove_key)}
          )
        )

      case Info(_, RemoveTidying(rid, remove_key, found_value)) =>
        Summary(
          map[],
          multiset{},
          multiset{},
          multiset{QueryFound(rid, remove_key, Some(found_value))}
        )

      case Info(Empty(), Querying(rid, query_key)) =>
        Summary(
          map[],
          multiset{},
          multiset{QueryUnknown(rid, query_key)},
          multiset{}
        )

      case Info(Full(kv), Querying(rid, query_key)) =>
        Summary(
          map[kv.key := Some(kv.val)],
          multiset{},
          (if kv.key == query_key
            then multiset{QueryFound(rid, query_key, Some(kv.val))}
            else multiset{QueryUnknown(rid, query_key)}
          ),
          multiset{}
        )
    }
  }

  function f(q: Q) : M {
    match q {
      case Some(info) => get_summary(info)
      case None => unit()
    }
  }
}

module Interpretation {
  import opened ResourceStateMachine
  import opened Options
  import opened KeyValueType
  import opened Maps
  import S = SummaryMonoid
  import MultisetLemmas
  import Multisets

  function {:opaque} interp_wrt(table: seq<Option<HT.Info>>, e: int) : S.Summary
  requires Complete(table)
  requires 0 <= e < |table|
  {
    S.concat_map(table[e+1..] + table[..e+1])
  }

  predicate is_good_root(table: seq<Option<HT.Info>>, e: int)
  {
    && 0 <= e < |table|
    && table[e].Some?
    && table[e].value.entry.Empty?
    && !table[e].value.state.RemoveTidying?
  }

  /*lemma split_at_empty(table: seq<Option<HT.Info>>, e: int, a: int, b: int)
  requires 0 <= a <= e < b < |table|
  requires is_good_root(table, e)
  ensures S.concat_map(table[a..b])
      == S.add(
        S.concat_map(table[a..e]),
        S.concat_map(table[e+1..b]))
  {
    calc {
      S.concat_map(table[a..b]);
      {
        assert table[a..b] == table[a..e] + table[e..b];
        S.concat_map_additive(table[a..e], table[e..b]);
      }
      S.add(
        S.concat_map(table[a..e]),
        S.concat_map(table[e..b]));
      {
        assert [table[e]] + table[e+1..b] == table[e..b];
        S.concat_map_additive([table[e]], table[e+1..b]);
      }
      S.add(
        S.concat_map(table[a..e]),
        S.add(
          S.concat_map([table[e]]),
          S.concat_map(table[e+1..b])));
      {
        assert S.f(table[e]) == S.unit();
      }
      S.add(
        S.concat_map(table[a..e]),
        S.add(
          S.unit(),
          S.concat_map(table[e+1..b])));
      S.add(
        S.concat_map(table[a..e]),
        S.concat_map(table[e+1..b]));
    }
  }*/

  lemma get_singleton_for_key(t: seq<Option<HT.Info>>, key: Key)
  returns (i: int)
  requires key in S.concat_map(t).ops
  ensures 0 <= i < |t|
  ensures key in S.f(t[i]).ops
  {
    if |t| <= 1 {
      i := 0;
    } else {
      if key in S.f(t[|t|-1]).ops {
        i := |t| - 1;
      } else {
        assert t[..|t|-1] + [t[|t|-1]] == t;
        S.concat_map_additive(t[..|t|-1], [t[|t|-1]]);
        i := get_singleton_for_key(t[..|t|-1], key);
      }
    }
  }

  lemma get_singleton_for_query(t: seq<Option<HT.Info>>, q: S.QueryRes)
  returns (i: int, q': S.QueryRes)
  requires q in S.concat_map(t).queries
  ensures 0 <= i < |t|
  ensures q' in S.f(t[i]).queries
  ensures q.key == q'.key
  {
    if |t| <= 1 {
      i := 0;
      var q1 :| q1 in S.f(t[0]).queries;
      q' := q1;
    } else {
      if q in S.f(t[|t|-1]).queries {
        i := |t| - 1;
        q' := q;
      } else {
        assert t[..|t|-1] + [t[|t|-1]] == t;
        S.concat_map_additive(t[..|t|-1], [t[|t|-1]]);
        var x := S.concat_map(t[..|t|-1]);
        var y := S.f(t[|t|-1]);
        //assert q in S.app_queries(x.queries, y.ops);
        S.reveal_app_queries();
        var qr := MultisetLemmas.ApplyGetBackwards(
            (q) => S.app_query(q, y.ops), x.queries, q);
        i, q' := get_singleton_for_query(t[..|t|-1], qr);
      }
    }
  }

  lemma get_singleton_for_remove(t: seq<Option<HT.Info>>, q: S.QueryRes)
  returns (i: int, q': S.QueryRes)
  requires q in S.concat_map(t).removes
  ensures 0 <= i < |t|
  ensures q' in S.f(t[i]).removes
  ensures q.key == q'.key
  ensures q'.QueryFound? ==> q.QueryFound?
  {
    if |t| <= 1 {
      i := 0;
      var q1 :| q1 in S.f(t[0]).removes;
      q' := q1;
    } else {
      if q in S.f(t[|t|-1]).removes {
        i := |t| - 1;
        q' := q;
      } else {
        assert t[..|t|-1] + [t[|t|-1]] == t;
        S.concat_map_additive(t[..|t|-1], [t[|t|-1]]);
        var x := S.concat_map(t[..|t|-1]);
        var y := S.f(t[|t|-1]);
        //assert q in S.app_queries(x.queries, y.ops);
        S.reveal_app_queries();
        var qr := MultisetLemmas.ApplyGetBackwards(
            (q) => S.app_query(q, y.ops), x.removes, q);
        i, q' := get_singleton_for_remove(t[..|t|-1], qr);
      }
    }
  }

  lemma get_singleton_for_key_slice(t: seq<Option<HT.Info>>, key: Key, a: int, b: int)
  returns (i: int)
  requires 0 <= a <= b <= |t|
  requires key in S.concat_map(t[a..b]).ops
  ensures a <= i < b
  ensures key in S.f(t[i]).ops
  {
    var i1 := get_singleton_for_key(t[a..b], key);
    i := a + i1;
    assert t[a..b][i1] == t[i];
  }

  lemma get_singleton_for_query_slice(t: seq<Option<HT.Info>>, q: S.QueryRes, a: int, b: int)
  returns (i: int, q': S.QueryRes)
  requires 0 <= a <= b <= |t|
  requires q in S.concat_map(t[a..b]).queries
  ensures a <= i < b
  ensures q' in S.f(t[i]).queries
  ensures q.key == q'.key
  {
    var i1;
    i1, q' := get_singleton_for_query(t[a..b], q);
    i := a + i1;
    assert t[a..b][i1] == t[i];
  }

  lemma get_singleton_for_remove_slice(t: seq<Option<HT.Info>>, q: S.QueryRes, a: int, b: int)
  returns (i: int, q': S.QueryRes)
  requires 0 <= a <= b <= |t|
  requires q in S.concat_map(t[a..b]).removes
  ensures a <= i < b
  ensures q' in S.f(t[i]).removes
  ensures q.key == q'.key
  ensures q'.QueryFound? ==> q.QueryFound?
  {
    var i1;
    i1, q' := get_singleton_for_remove(t[a..b], q);
    i := a + i1;
    assert t[a..b][i1] == t[i];
  }


  lemma separated_segments_commute(table: seq<Option<HT.Info>>, e: int, f: int,
      a: int, b: int, c: int, d: int)
  requires Complete(table)
  requires InvTable(table)
  requires is_good_root(table, e)
  requires is_good_root(table, f)
  requires 0 <= a <= b <= |table|
  requires 0 <= c <= d <= |table|
  requires |table| == HT.FixedSize()
  requires e != f
  requires a != b ==>
           adjust(a, e+1)
        <= adjust(b-1, e+1)
        <= adjust(f, e+1)
  requires c != d ==>
           adjust(c, f+1)
        <= adjust(d-1, f+1)
        <= adjust(e, f+1)
  ensures S.add(S.concat_map(table[a..b]), S.concat_map(table[c..d]))
      == S.add(S.concat_map(table[c..d]), S.concat_map(table[a..b]))
  {
    if a == b {
      assert table[a..b] == [];
      S.add_unit(S.concat_map(table[c..d]));
      return;
    }
    if c == d {
      assert table[c..d] == [];
      S.add_unit(S.concat_map(table[a..b]));
      return;
    }

    var x := S.concat_map(table[a..b]);
    var y := S.concat_map(table[c..d]);
    var a1 := S.add(x, y);
    var a2 := S.add(y, x);

    assert a1.stubs == a2.stubs;

    assert a1.ops == a2.ops by {
      forall k | k in x.ops && k in y.ops
      ensures false
      {
        var i := get_singleton_for_key_slice(table, k, a, b);
        var j := get_singleton_for_key_slice(table, k, c, d);

        assert ValidHashInSlot(table, e, i);
        //assert ValidHashInSlot(table, e, j1);
        //assert ValidHashInSlot(table, f, i1);
        assert ValidHashInSlot(table, f, j);

        //assert ValidHashOrdering(table, e, i1, j1);
        //assert ValidHashOrdering(table, e, j1, i1);
        //assert ValidHashOrdering(table, f, i1, j1);
        //assert ValidHashOrdering(table, f, j1, i1);

        //assert ActionNotPastKey(table, e, i1, j1);
        //assert ActionNotPastKey(table, e, j1, i1);
        //assert ActionNotPastKey(table, f, i1, j1);
        //assert ActionNotPastKey(table, f, j1, i1);

        /*if table[i1].value.entry.Full? && table[i1].value.entry.kv.key == k {
          if table[j1].value.entry.Full? && table[j1].value.entry.kv.key == k {
            if e + 1 == |table| {
              if f+1 > c {
                assert adjust(c, f+1) <= adjust(e, f+1);
                assert adjust(c, f+1) == c + |table|;
                assert c + |table| <= adjust(e, f+1);
                assert c <= e;
                assert e < f+1;
                assert e == |table| - 1;
                assert f == |table| - 1;
                assert false;
              }
              assert a < b <= f+1 <= c < d <= |table|;
              assert false;
            } else if e + 1 == 1 {
              /*var e' := (if e < |table| - 1 then e + 1 else 0);
              var f' := (if f < |table| - 1 then f + 1 else 0);
              var h := HT.hash(table[i1].value.entry.kv.key) as int;
              assert adjust(h, f') <= adjust(j1, f');

              assert adjust(j1, f') < adjust(d, f');
              assert d != f';
              assert adjust(d, f') <= adjust(e', f');
              assert adjust(j1, f') < adjust(e', f');

              assert adjust(f', e') <= adjust(h, e');
              assert adjust(f', e+1) <= adjust(h, e+1);
              assert adjust(h, e+1) <= adjust(j1, e+1);*/

              assert false;
            } else {
              assert false;
            }
          } else {
            assert false;
          }
        } else {
          assert false;
        }*/
      }
    }

    assert a1.queries == a2.queries by {
      forall q, k | k in x.ops && q in y.queries && q.key == k
      ensures false
      {
        var i := get_singleton_for_key_slice(table, k, a, b);
        var j, q' := get_singleton_for_query_slice(table, q, c, d);

        assert ValidHashInSlot(table, e, i);
        assert ValidHashInSlot(table, f, j);
      }
      forall q, k | k in y.ops && q in x.queries && q.key == k
      ensures false
      {
        var i, q' := get_singleton_for_query_slice(table, q, a, b);
        var j := get_singleton_for_key_slice(table, k, c, d);

        assert ValidHashInSlot(table, e, i);
        assert ValidHashInSlot(table, f, j);
      }
      S.reveal_app_queries();
      MultisetLemmas.ApplyId((q) => S.app_query(q, x.ops), y.queries);
      MultisetLemmas.ApplyId((q) => S.app_query(q, y.ops), x.queries);
    }

    assert a1.removes == a2.removes by {
      forall q, k | k in x.ops && q in y.removes && q.key == k && q.QueryUnknown?
      ensures false
      {
        var i := get_singleton_for_key_slice(table, k, a, b);
        var j, q' := get_singleton_for_remove_slice(table, q, c, d);

        assert table[j].value.state.Removing?;

        assert ValidHashInSlot(table, e, i);
        assert ValidHashInSlot(table, f, j);
      }
      forall q, k | k in y.ops && q in x.removes && q.key == k && q.QueryUnknown?
      ensures false
      {
        var i, q' := get_singleton_for_remove_slice(table, q, a, b);
        var j := get_singleton_for_key_slice(table, k, c, d);

        assert ValidHashInSlot(table, e, i);
        assert ValidHashInSlot(table, f, j);
      }
      S.reveal_app_queries();
      MultisetLemmas.ApplyId((q) => S.app_query(q, x.ops), y.removes);
      MultisetLemmas.ApplyId((q) => S.app_query(q, y.ops), x.removes);
    }
  }

  lemma seq_ext<A>(a: seq<A>, b: seq<A>)
  requires |a| == |b|
  requires forall i | 0 <= i < |a| :: a[i] == b[i]
  ensures a == b
  {
  }

  lemma interp_wrt_independent_of_root_wlog(table: seq<Option<HT.Info>>, e: int, f: int)
  requires Complete(table)
  requires InvTable(table)
  requires is_good_root(table, e)
  requires is_good_root(table, f)
  requires e < f
  ensures interp_wrt(table, e) == interp_wrt(table, f)
  {
    calc {
      interp_wrt(table, e);
      { reveal_interp_wrt(); }
      S.concat_map(table[e+1..] + table[..e+1]);
      {
        S.concat_map_additive(table[e+1..], table[..e+1]);
      }
      S.add(
        S.concat_map(table[e+1..]),
        S.concat_map(table[..e+1]));
      {
        S.concat_map_additive(table[e+1..f+1], table[f+1..]);
        seq_ext(table[e+1..f+1] + table[f+1..], table[e+1..]);
      }
      S.add(
        S.add(
          S.concat_map(table[e+1..f+1]),
          S.concat_map(table[f+1..])
        ),
        S.concat_map(table[..e+1])
      );
      {
        separated_segments_commute(table, e, f, e+1, f+1, f+1, |table|);
        assert table[f+1..] == table[f+1..|table|];
      }
      S.add(
        S.add(
          S.concat_map(table[f+1..]),
          S.concat_map(table[e+1..f+1])
        ),
        S.concat_map(table[..e+1])
      );
      {
        S.associative(S.concat_map(table[f+1..]),
          S.concat_map(table[e+1..f+1]), S.concat_map(table[..e+1]));
      }
      S.add(
        S.concat_map(table[f+1..]),
        S.add(
          S.concat_map(table[e+1..f+1]),
          S.concat_map(table[..e+1])
        )
      );
      {
        separated_segments_commute(table, f, e, 0, e+1, e+1, f+1);
      }
      S.add(
        S.concat_map(table[f+1..]),
        S.add(
          S.concat_map(table[..e+1]),
          S.concat_map(table[e+1..f+1])
        )
      );
      {
        S.concat_map_additive(table[..e+1], table[e+1..f+1]);
        assert table[..e+1] + table[e+1..f+1] == table[..f+1];
      }
      S.add(
        S.concat_map(table[f+1..]),
        S.concat_map(table[..f+1])
      );
      {
        S.concat_map_additive(table[f+1..], table[..f+1]);
      }
      S.concat_map(table[f+1..] + table[..f+1]);
      { reveal_interp_wrt(); }
      interp_wrt(table, f);
    }
  }

  lemma interp_wrt_independent_of_root(table: seq<Option<HT.Info>>, e: int, f: int)
  requires Complete(table)
  requires InvTable(table)
  requires is_good_root(table, e)
  requires is_good_root(table, f)
  ensures interp_wrt(table, e) == interp_wrt(table, f)
  {
    if e < f {
      interp_wrt_independent_of_root_wlog(table, e, f);
    } else if e == f {
    } else {
      interp_wrt_independent_of_root_wlog(table, f, e);
    }
  }

  function {:opaque} interp(table: seq<Option<HT.Info>>) : S.Summary
  requires Complete(table)
  requires InvTable(table)
  requires TableQuantity(table) < |table|
  ensures forall e | is_good_root(table, e) :: interp(table) == interp_wrt(table, e)
  {
    var f := get_empty_cell(table);
    var res := interp_wrt(table, f);

    assert forall e | is_good_root(table, e) :: res == interp_wrt(table, e) by {
      forall e | is_good_root(table, e) ensures res == interp_wrt(table, e)
      {
        interp_wrt_independent_of_root(table, e, f);
      }
    }

    res
  }

  function interp_with_stubs(s: Variables) : S.Summary
  requires Inv(s)
  requires Complete(s.table)
  {
    var d := interp(s.table);
    d.(stubs := s.stubs)
  }


  lemma preserves_1(table: seq<Option<HT.Info>>,
      table': seq<Option<HT.Info>>,
      i: int,
      f: int)
  requires Complete(table)
  requires Complete(table')
  requires InvTable(table)
  requires InvTable(table')
  requires TableQuantity(table) < |table|
  requires TableQuantity(table') < |table'|
  requires forall j | 0 <= j < |table| && i != j :: table'[j] == table[j]
  requires 0 <= i < |table|
  requires S.f(table[i]) == S.f(table'[i])
  requires is_good_root(table, f);
  requires is_good_root(table', f);
  ensures interp(table) == interp(table')
  {
    calc {
      interp(table);
      interp_wrt(table, f);
      { reveal_interp_wrt(); }
      S.concat_map(table[f+1..] + table[..f+1]);
      {
        S.preserves_1_helper(table[f+1..] + table[..f+1],
            table'[f+1..] + table'[..f+1],
            if i >= f+1 then i - (f+1) else i + |table| - (f+1));
      }
      S.concat_map(table'[f+1..] + table'[..f+1]);
      { reveal_interp_wrt(); }
      interp_wrt(table', f);
      interp(table');
    }
  }

  lemma preserves_1_right(table: seq<Option<HT.Info>>,
      table': seq<Option<HT.Info>>,
      i: int,
      f: int,
      x: S.Summary)
  requires Complete(table)
  requires Complete(table')
  requires InvTable(table)
  requires InvTable(table')
  requires TableQuantity(table) < |table|
  requires TableQuantity(table') < |table'|
  requires forall j | 0 <= j < |table| && i != j :: table'[j] == table[j]
  requires 0 <= i < |table|
  requires S.f(table[i]) == S.add(S.f(table'[i]), x)
  requires is_good_root(table, f);
  requires is_good_root(table', f);
  requires forall k | 0 <= k < HT.FixedSize() && adjust(i, f+1) < adjust(k, f+1)
      :: S.commutes(x, S.f(table[k]))
  ensures interp(table) == S.add(interp(table'), x)
  {
    /*calc {
      interp(table);
      interp_wrt(table, f);
      { reveal_interp_wrt(); }
      S.concat_map(table[f+1..] + table[..f+1]);
      {
        S.preserves_1_helper(table[f+1..] + table[..f+1],
            table'[f+1..] + table'[..f+1],
            if i >= f+1 then i - (f+1) else i + |table| - (f+1));
      }
      S.concat_map(table'[f+1..] + table'[..f+1]);
      { reveal_interp_wrt(); }
      interp_wrt(table', f);
      interp(table');
    }*/
    assume false;
  }

  lemma preserves_1_left(table: seq<Option<HT.Info>>,
      table': seq<Option<HT.Info>>,
      i: int,
      f: int,
      x: S.Summary)
  requires Complete(table)
  requires Complete(table')
  requires InvTable(table)
  requires InvTable(table')
  requires TableQuantity(table) < |table|
  requires TableQuantity(table') < |table'|
  requires forall j | 0 <= j < |table| && i != j :: table'[j] == table[j]
  requires 0 <= i < |table|
  requires S.add(x, S.f(table[i])) == S.f(table'[i])
  requires is_good_root(table, f);
  requires is_good_root(table', f);
  requires forall k | 0 <= k < HT.FixedSize() && adjust(k, f+1) < adjust(i, f+1)
      :: S.commutes(x, S.f(table[k]))
  ensures S.add(x, interp(table)) == interp(table')
  {
    assume false;
  }

  lemma preserves_2(table: seq<Option<HT.Info>>,
      table': seq<Option<HT.Info>>,
      i: int,
      f: int)
  requires Complete(table)
  requires Complete(table')
  requires InvTable(table)
  requires InvTable(table')
  requires TableQuantity(table) < |table|
  requires TableQuantity(table') < |table'|
  requires 0 <= i < |table|
  requires var i' := (if i < |table| - 1 then i + 1 else 0);
           && S.add(S.f(table[i]), S.f(table[i'])) == S.add(S.f(table'[i]), S.f(table'[i']))
           && (forall j | 0 <= j < |table| && i != j && i' != j :: table'[j] == table[j])
  requires i != f
  requires is_good_root(table, f);
  requires is_good_root(table', f);
  ensures interp(table) == interp(table')
  {
    calc {
      interp(table);
      interp_wrt(table, f);
      { reveal_interp_wrt(); }
      S.concat_map(table[f+1..] + table[..f+1]);
      {
        S.preserves_2_helper(table[f+1..] + table[..f+1],
            table'[f+1..] + table'[..f+1],
            if i >= f+1 then i - (f+1) else i + |table| - (f+1));
      }
      S.concat_map(table'[f+1..] + table'[..f+1]);
      { reveal_interp_wrt(); }
      interp_wrt(table', f);
      interp(table');
    }
  }

  function map_remove_nones<K, V>(m: map<K, Option<V>>) : map<K, V> {
    map k | k in m && m[k].Some? :: m[k].value
  }

  function to_query_stub(q: S.QueryRes) : HT.Stub {
    match q {
      case QueryFound(rid, key, Some(value)) =>
          HT.Stub(rid, MapIfc.QueryOutput(Found(value)))
      case QueryFound(rid, key, None()) =>
          HT.Stub(rid, MapIfc.QueryOutput(NotFound))
      case QueryUnknown(rid, key) =>
          HT.Stub(rid, MapIfc.QueryOutput(NotFound))
    }
  }

  function apply_to_query_stub(m: multiset<S.QueryRes>) : multiset<HT.Stub> {
    Multisets.Apply(to_query_stub, m)
  }

  function to_remove_stub(q: S.QueryRes) : HT.Stub {
    match q {
      case QueryFound(rid, key, Some(value)) =>
          HT.Stub(rid, MapIfc.RemoveOutput(true))
      case QueryFound(rid, key, None()) =>
          HT.Stub(rid, MapIfc.RemoveOutput(false))
      case QueryUnknown(rid, key) =>
          HT.Stub(rid, MapIfc.RemoveOutput(false))
    }
  }

  function apply_to_remove_stub(m: multiset<S.QueryRes>) : multiset<HT.Stub> {
    Multisets.Apply(to_remove_stub, m)
  }

  lemma UsefulTriggers()
  ensures forall fn: S.QueryRes -> S.QueryRes :: Multisets.Apply(fn, multiset{}) == multiset{};
  ensures forall fn: S.QueryRes -> S.QueryRes, a :: Multisets.Apply(fn, multiset{a}) == multiset{fn(a)}
  {
    Multisets.reveal_Apply();
  }

  lemma InsertSkip_PreservesInterp(s: Variables, s': Variables, pos: nat)
  requires Inv(s)
  requires HT.InsertSkip(s, s', pos)
  ensures Inv(s')
  ensures interp(s.table) == interp(s'.table)
  {
    InsertSkip_PreservesInv(s, s', pos);
    var e := get_empty_cell(s.table);

    /*var table := s.table;
    var table' := s'.table;
    var pos' := if pos < |s.table| - 1 then pos + 1 else 0;

    var a := S.add(S.f(table[pos]), S.f(table[pos']));
    var b := S.add(S.f(table'[pos]), S.f(table'[pos']));*/

    //UsefulTriggers();
    S.reveal_app_queries();

    /*assert a.ops == b.ops;
    assert a.stubs == b.stubs;
    assert a.queries == b.queries;*/

    preserves_2(s.table, s'.table, pos, e);
  }


  lemma InsertSwap_PreservesInterp(s: Variables, s': Variables, pos: nat)
  requires Inv(s)
  requires HT.InsertSwap(s, s', pos)
  ensures Inv(s')
  ensures interp(s.table) == interp(s'.table)
  {
    InsertSwap_PreservesInv(s, s', pos);
    var e := get_empty_cell(s.table);
    S.reveal_app_queries();
    preserves_2(s.table, s'.table, pos, e);
  }

  lemma add_thing_with_no_ops(s: S.Summary, t: S.Summary)
  requires t.ops == map[]
  ensures S.add(s, t).ops == s.ops
  ensures S.add(s, t).stubs == s.stubs + t.stubs
  ensures S.add(s, t).queries == s.queries + t.queries
  ensures S.add(s, t).removes == s.removes + t.removes
  {
    S.reveal_app_queries();
    MultisetLemmas.ApplyId((q) => S.app_query(q, map[]), s.queries);
    MultisetLemmas.ApplyId((q) => S.app_query(q, map[]), s.removes);
  }

  lemma InsertDone_PreservesInterp(s: Variables, s': Variables, pos: nat)
  requires Inv(s)
  requires HT.InsertDone(s, s', pos)
  ensures Inv(s')
  ensures interp(s.table).ops == interp(s'.table).ops
  ensures interp(s.table).stubs == interp(s'.table).stubs + multiset{HT.Stub(s.table[pos].value.state.rid, MapIfc.InsertOutput(true))}
  ensures interp(s.table).queries == interp(s'.table).queries
  ensures interp(s.table).removes == interp(s'.table).removes
  {
    InsertDone_PreservesInv(s, s', pos);
    var e := get_empty_cell(s'.table);
    S.reveal_app_queries();

    var x := S.Summary(map[],
        multiset{HT.Stub(s.table[pos].value.state.rid, MapIfc.InsertOutput(true))},
        multiset{}, multiset{});

    forall y ensures S.commutes(x, y) {
      MultisetLemmas.ApplyId((q) => S.app_query(q, map[]), x.queries);
      MultisetLemmas.ApplyId((q) => S.app_query(q, map[]), x.removes);
      MultisetLemmas.ApplyId((q) => S.app_query(q, map[]), y.queries);
      MultisetLemmas.ApplyId((q) => S.app_query(q, map[]), y.removes);
    }

    preserves_1_right(s.table, s'.table, pos, e, x);
    add_thing_with_no_ops(interp(s'.table), x);
  }

  lemma InsertUpdate_PreservesInterp(s: Variables, s': Variables, pos: nat)
  requires Inv(s)
  requires HT.InsertUpdate(s, s', pos)
  ensures Inv(s')
  ensures interp(s.table).ops == interp(s'.table).ops
  ensures interp(s.table).stubs == interp(s'.table).stubs + multiset{HT.Stub(s.table[pos].value.state.rid, MapIfc.InsertOutput(true))}
  ensures interp(s.table).queries == interp(s'.table).queries
  ensures interp(s.table).removes == interp(s'.table).removes
  {
    InsertUpdate_PreservesInv(s, s', pos);
    var e := get_empty_cell(s'.table);
    S.reveal_app_queries();

    var x := S.Summary(map[],
        multiset{HT.Stub(s.table[pos].value.state.rid, MapIfc.InsertOutput(true))},
        multiset{}, multiset{});

    forall y ensures S.commutes(x, y) {
      MultisetLemmas.ApplyId((q) => S.app_query(q, map[]), x.queries);
      MultisetLemmas.ApplyId((q) => S.app_query(q, map[]), x.removes);
      MultisetLemmas.ApplyId((q) => S.app_query(q, map[]), y.queries);
      MultisetLemmas.ApplyId((q) => S.app_query(q, map[]), y.removes);
    }

    preserves_1_right(s.table, s'.table, pos, e, x);
    add_thing_with_no_ops(interp(s'.table), x);

  }

  lemma QuerySkip_PreservesInterp(s: Variables, s': Variables, pos: nat)
  requires Inv(s)
  requires HT.QuerySkip(s, s', pos)
  ensures Inv(s')
  ensures interp(s.table) == interp(s'.table)
  {
    QuerySkip_PreservesInv(s, s', pos);
    var e := get_empty_cell(s.table);
    S.reveal_app_queries();

    var table := s.table;
    var table' := s'.table;
    var pos' := if pos < |s.table| - 1 then pos + 1 else 0;

    var a := S.add(S.f(table[pos]), S.f(table[pos']));
    var b := S.add(S.f(table'[pos]), S.f(table'[pos']));

    UsefulTriggers();
    S.reveal_app_queries();

    assert a.ops == b.ops;
    assert a.stubs == b.stubs;
    assert a.queries == b.queries;

    preserves_2(s.table, s'.table, pos, e);
  }

  lemma QueryDone_PreservesInterp(s: Variables, s': Variables, pos: nat)
  requires Inv(s)
  requires HT.QueryDone(s, s', pos)
  ensures Inv(s')
  ensures interp(s.table).ops == interp(s'.table).ops
  ensures interp(s.table).stubs == interp(s'.table).stubs
  ensures interp(s.table).queries == interp(s'.table).queries + multiset{S.QueryFound(
      s.table[pos].value.state.rid, s.table[pos].value.state.key,
      Some(s.table[pos].value.entry.kv.val))}
  ensures interp(s.table).removes == interp(s'.table).removes
  {
    QueryDone_PreservesInv(s, s', pos);
    var e := get_empty_cell(s'.table);
    S.reveal_app_queries();
    UsefulTriggers();

    var x := S.Summary(map[],
        multiset{},
        multiset{S.QueryFound(
          s.table[pos].value.state.rid, s.table[pos].value.state.key,
          Some(s.table[pos].value.entry.kv.val))},
        multiset{});

    preserves_1_right(s.table, s'.table, pos, e, x);
    add_thing_with_no_ops(interp(s'.table), x);
  }

  lemma QueryNotFound_PreservesInterp(s: Variables, s': Variables, pos: nat)
  requires Inv(s)
  requires HT.QueryNotFound(s, s', pos)
  ensures Inv(s')
  ensures interp(s.table).ops == interp(s'.table).ops
  ensures interp(s.table).stubs == interp(s'.table).stubs
  ensures interp(s.table).queries == interp(s'.table).queries + multiset{S.QueryUnknown(
      s.table[pos].value.state.rid, s.table[pos].value.state.key)}
  ensures interp(s.table).removes == interp(s'.table).removes

  {
    QueryNotFound_PreservesInv(s, s', pos);
    var e := get_empty_cell(s.table);
    S.reveal_app_queries();
    UsefulTriggers();

    var x := S.Summary(map[],
        multiset{},
        multiset{S.QueryUnknown(
          s.table[pos].value.state.rid, s.table[pos].value.state.key)},
        multiset{});
    forall k | 0 <= k < HT.FixedSize() && adjust(pos, e+1) < adjust(k, e+1)
    ensures S.commutes(x, S.f(s.table[k]))
    {
      assert ValidHashInSlot(s.table, e, pos);
      assert ValidHashOrdering(s.table, e, pos, k);
      assert ValidHashInSlot(s.table, pos, k);
      //assert !(s.table[k].value.entry.Full? && s.table[k].value.entry.kv.key == 
      //    s.table[pos].value.state.key);
    }

    preserves_1_right(s.table, s'.table, pos, e, x);
    add_thing_with_no_ops(interp(s'.table), x);
  }

  lemma RemoveSkip_PreservesInterp(s: Variables, s': Variables, pos: nat)
  requires Inv(s)
  requires HT.RemoveSkip(s, s', pos)
  ensures Inv(s')
  ensures interp(s.table) == interp(s'.table)
  {
    RemoveSkip_PreservesInv(s, s', pos);
    var e := get_empty_cell(s.table);
    S.reveal_app_queries();
    UsefulTriggers();
    preserves_2(s.table, s'.table, pos, e);
  }

  lemma RemoveFoundIt_PreservesInterp(s: Variables, s': Variables, pos: nat)
  requires Inv(s)
  requires HT.RemoveFoundIt(s, s', pos)
  ensures Inv(s')
  ensures map_remove_nones(interp(s.table).ops)
       == map_remove_nones(interp(s'.table).ops)
  ensures interp(s.table).stubs == interp(s'.table).stubs
  ensures apply_to_query_stub(interp(s.table).queries)
       == apply_to_query_stub(interp(s'.table).queries)
  ensures apply_to_remove_stub(interp(s.table).removes)
       == apply_to_remove_stub(interp(s'.table).removes)
  {
    RemoveFoundIt_PreservesInv(s, s', pos);
    var e := get_empty_cell(s.table);
    S.reveal_app_queries();
    UsefulTriggers();

    var x := S.Summary(map[s.table[pos].value.state.key := None],
        multiset{}, multiset{}, multiset{});

    forall k | 0 <= k < HT.FixedSize() && adjust(pos, e+1) < adjust(k, e+1)
    ensures S.commutes(x, S.f(s.table[k]))
    {
      assert ValidHashInSlot(s.table, e, pos);
      assert ValidHashOrdering(s.table, e, pos, k);
      assert ValidHashInSlot(s.table, pos, k);
      //assert ValidHashInSlot(s'.table, e, pos);
      //assert ValidHashOrdering(s'.table, e, pos, k);
      //assert ValidHashInSlot(s'.table, pos, k);
      /*assert !(s.table[k].value.entry.Full? && s.table[k].value.entry.kv.key == 
          s.table[pos].value.state.key
          && !s.table[k].value.state.RemoveTidying?);*/

      assert ActionNotPastKey(s.table, e, pos, k);
      //assert ActionNotPastKey(s.table, e, k, pos);

      /*assert !(s.table[k].value.state.Querying? && s.table[k].value.state.key == 
          s.table[pos].value.state.key
          && !s.table[k].value.state.RemoveTidying?);

      assert !(s.table[k].value.state.Removing? && s.table[k].value.state.key == 
          s.table[pos].value.state.key
          && !s.table[k].value.state.RemoveTidying?);*/

      /*var m1 := S.add(x, S.f(s.table[k]));
      var m2 := S.add(S.f(s.table[k]), x);
      assert m1.ops == m2.ops;
      assert m1.stubs == m2.stubs;
      assert m1.queries == m2.queries;
      assert m1.removes == m2.removes;*/
    }

    preserves_1_right(s.table, s'.table, pos, e, x);

    calc {
      apply_to_query_stub(interp(s.table).queries);
      //Multisets.Apply(to_query_stub, interp(s.table).queries);
      {
        assert interp(s.table).queries
            == Multisets.Apply((q) => S.app_query(q, x.ops), interp(s'.table).queries);
      //}
      //Multisets.Apply(to_query_stub, Multisets.Apply((q) => S.app_query(q, x.ops), interp(s'.table).queries));
      //{
        MultisetLemmas.apply_eq_1_2(
            interp(s'.table).queries,
            to_query_stub,
            (q) => S.app_query(q, x.ops),
            to_query_stub);
      }
      //Multisets.Apply(to_query_stub, interp(s'.table).queries);
      apply_to_query_stub(interp(s'.table).queries);
    }
    calc {
      apply_to_remove_stub(interp(s.table).removes);
      {
        assert interp(s.table).removes
            == Multisets.Apply((q) => S.app_query(q, x.ops), interp(s'.table).removes);
        MultisetLemmas.apply_eq_1_2(
            interp(s'.table).removes,
            to_remove_stub,
            (q) => S.app_query(q, x.ops),
            to_remove_stub);
      }
      apply_to_remove_stub(interp(s'.table).removes);
    }
  }

  lemma RemoveTidy_PreservesInterp(s: Variables, s': Variables, pos: nat)
  requires Inv(s)
  requires HT.RemoveTidy(s, s', pos)
  ensures Inv(s')
  ensures interp(s.table) == interp(s'.table)
  {
    RemoveTidy_PreservesInv(s, s', pos);
    var e := get_empty_cell(s.table);
    S.reveal_app_queries();
    UsefulTriggers();
    preserves_2(s.table, s'.table, pos, e);
  }

  lemma RemoveDone_PreservesInterp(s: Variables, s': Variables, pos: nat)
  requires Inv(s)
  requires HT.RemoveDone(s, s', pos)
  ensures Inv(s')
  ensures interp(s.table).ops == interp(s'.table).ops
  ensures interp(s.table).stubs == interp(s'.table).stubs
  ensures interp(s.table).queries == interp(s'.table).queries
  ensures interp(s.table).removes == interp(s'.table).removes + multiset{S.QueryFound(
      s.table[pos].value.state.rid, s.table[pos].value.state.initial_key,
      Some(s.table[pos].value.state.found_value))}
  {
    RemoveDone_PreservesInv(s, s', pos);
    var e := get_empty_cell(s.table);
    S.reveal_app_queries();
    UsefulTriggers();

    var x := S.Summary(map[],
        multiset{},
        multiset{},
        multiset{S.QueryFound(
          s.table[pos].value.state.rid, s.table[pos].value.state.initial_key,
          Some(s.table[pos].value.state.found_value))});

    /*forall k | 0 <= k < HT.FixedSize() && adjust(pos, e+1) < adjust(k, e+1)
    ensures S.commutes(x, S.f(s.table[k]))
    {
      assert ValidHashInSlot(s.table, e, pos);
      assert ValidHashOrdering(s.table, e, pos, k);
      assert ValidHashInSlot(s.table, pos, k);
    }*/

    preserves_1_right(s.table, s'.table, pos, e, x);
    add_thing_with_no_ops(interp(s'.table), x);
  }

  lemma RemoveNotFound_PreservesInterp(s: Variables, s': Variables, pos: nat)
  requires Inv(s)
  requires HT.RemoveNotFound(s, s', pos)
  ensures Inv(s')
  ensures map_remove_nones(interp(s.table).ops)
       == map_remove_nones(interp(s'.table).ops)
  ensures interp(s.table).stubs == interp(s'.table).stubs
  ensures apply_to_query_stub(interp(s.table).queries)
       == apply_to_query_stub(interp(s'.table).queries)
  ensures apply_to_remove_stub(interp(s.table).removes)
       == apply_to_remove_stub(interp(s'.table).removes)
        + multiset{HT.Stub(s.table[pos].value.state.rid, MapIfc.RemoveOutput(false))};

  {
    RemoveNotFound_PreservesInv(s, s', pos);
    var e := get_empty_cell(s.table);
    S.reveal_app_queries();
    UsefulTriggers();

    /*var x := S.Summary(map[],
        multiset{},
        multiset{},
        multiset{S.QueryFound(
          s.table[pos].value.state.rid, s.table[pos].value.state.key,
          None)});*/

    var x := S.Summary(map[s.table[pos].value.state.key := None],
        multiset{}, multiset{},
        multiset{S.QueryUnknown(
          s.table[pos].value.state.rid, s.table[pos].value.state.key)});

    /*assert s.table[pos].value.entry.Full? ==>
        s.table[pos].value.entry.kv.key != s.table[pos].value.state.key;

    var m1 := S.f(s.table[pos]);
    var m2 := S.add(S.f(s'.table[pos]), x);
    assert m1.ops == m2.ops;
    assert m1.stubs == m2.stubs;
    assert m1.queries == m2.queries;
    assert m1.removes == m2.removes;*/

    forall k | 0 <= k < HT.FixedSize() && adjust(pos, e+1) < adjust(k, e+1)
    ensures S.commutes(x, S.f(s.table[k]))
    {
      assert ValidHashInSlot(s.table, e, pos);
      assert ValidHashOrdering(s.table, e, pos, k);
      assert ValidHashInSlot(s.table, pos, k);
      assert ActionNotPastKey(s.table, e, pos, k);
    }

    preserves_1_right(s.table, s'.table, pos, e, x);

    calc {
      apply_to_query_stub(interp(s.table).queries);
      {
        assert interp(s.table).queries
            == Multisets.Apply((q) => S.app_query(q, x.ops), interp(s'.table).queries);
        MultisetLemmas.apply_eq_1_2(
            interp(s'.table).queries,
            to_query_stub,
            (q) => S.app_query(q, x.ops),
            to_query_stub);
      }
      apply_to_query_stub(interp(s'.table).queries);
    }

    calc {
      apply_to_remove_stub(interp(s.table).removes);
      Multisets.Apply(to_remove_stub, interp(s.table).removes);
      {
        assert interp(s.table).removes
            == Multisets.Apply((q) => S.app_query(q, x.ops), interp(s'.table).removes)
        + multiset{S.QueryUnknown(
          s.table[pos].value.state.rid, s.table[pos].value.state.key)};
      }
      Multisets.Apply(to_remove_stub, Multisets.Apply((q) => S.app_query(q, x.ops), interp(s'.table).removes)
        + multiset{S.QueryUnknown(
          s.table[pos].value.state.rid, s.table[pos].value.state.key)});
      {
        Multisets.ApplyAdditive(to_remove_stub, 
            Multisets.Apply((q) => S.app_query(q, x.ops), interp(s'.table).removes),
            multiset{S.QueryUnknown(s.table[pos].value.state.rid, s.table[pos].value.state.key)});
        assert to_remove_stub(S.QueryUnknown(s.table[pos].value.state.rid, s.table[pos].value.state.key)) == HT.Stub(s.table[pos].value.state.rid, MapIfc.RemoveOutput(false));
        Multisets.ApplySingleton(to_remove_stub, S.QueryUnknown(s.table[pos].value.state.rid, s.table[pos].value.state.key));
      }
      Multisets.Apply(to_remove_stub, Multisets.Apply((q) => S.app_query(q, x.ops), interp(s'.table).removes))
        + multiset{HT.Stub(s.table[pos].value.state.rid, MapIfc.RemoveOutput(false))};
      {
        MultisetLemmas.apply_eq_1_2(
            interp(s'.table).removes,
            to_remove_stub,
            (q) => S.app_query(q, x.ops),
            to_remove_stub);
      }
      Multisets.Apply(to_remove_stub, interp(s'.table).removes)
        + multiset{HT.Stub(s.table[pos].value.state.rid, MapIfc.RemoveOutput(false))};
      apply_to_remove_stub(interp(s'.table).removes)
        + multiset{HT.Stub(s.table[pos].value.state.rid, MapIfc.RemoveOutput(false))};
    }
  }

  lemma ProcessInsertTicket_ChangesInterp(s: Variables, s': Variables, ticket: HT.Ticket)
  requires Inv(s)
  requires HT.ProcessInsertTicket(s, s', ticket)
  ensures Inv(s')
  ensures map_remove_nones(interp(s'.table).ops)
       == map_remove_nones(interp(s.table).ops)[ticket.input.key := ticket.input.value]
  ensures interp(s'.table).stubs == interp(s.table).stubs
      + multiset{HT.Stub(ticket.rid, MapIfc.InsertOutput(true))}
  ensures interp(s'.table).queries == interp(s.table).queries
  ensures interp(s'.table).removes == interp(s.table).removes
  {
    ProcessInsertTicket_PreservesInv(s, s', ticket);
    var e := get_empty_cell(s.table);
    S.reveal_app_queries();
    UsefulTriggers();

    var x := S.Summary(map[ticket.input.key := Some(ticket.input.value)],
        multiset{HT.Stub(ticket.rid, MapIfc.InsertOutput(true))},
        multiset{}, multiset{});

    var pos := HT.hash(ticket.input.key) as int;

    /*var a := S.add(x, S.f(s.table[pos]));
    var b := S.f(s'.table[pos]);
    assert a.ops == b.ops;
    assert a.stubs == b.stubs;
    assert a.queries == b.queries;
    assert a.removes == b.removes;*/

    forall k | 0 <= k < HT.FixedSize() && adjust(k, e+1) < adjust(pos, e+1)
    ensures S.commutes(x, S.f(s.table[k]))
    {
      assert ValidHashInSlot(s.table, e, k);
      assert ValidHashOrdering(s.table, e, k, pos);
      assert ValidHashInSlot(s.table, pos, k);
      assert ValidHashInSlot(s.table, k, pos);
      assert ActionNotPastKey(s.table, e, k, pos);
      assert ActionNotPastKey(s.table, e, pos, k);
    }

    preserves_1_left(s.table, s'.table, pos, e, x);
  }

  lemma ProcessQueryTicket_ChangesInterp(s: Variables, s': Variables, ticket: HT.Ticket)
  requires Inv(s)
  requires HT.ProcessQueryTicket(s, s', ticket)
  ensures Inv(s')
  ensures interp(s'.table).ops == interp(s.table).ops
  ensures interp(s'.table).stubs == interp(s.table).stubs
  //ensures interp(s'.table).queries
  //     == interp(s.table).queries + multiset{S.QueryUnknown(ticket.rid, ticket.input.key)}
  ensures ticket.input.key !in map_remove_nones(interp(s.table).ops) ==>
        apply_to_query_stub(interp(s'.table).queries)
         == apply_to_query_stub(interp(s.table).queries)
          + multiset{HT.Stub(ticket.rid, MapIfc.QueryOutput(NotFound))}
  ensures ticket.input.key in map_remove_nones(interp(s.table).ops) ==>
        apply_to_query_stub(interp(s'.table).queries)
         == apply_to_query_stub(interp(s.table).queries)
          + multiset{HT.Stub(ticket.rid, MapIfc.QueryOutput(Found(
              map_remove_nones(interp(s.table).ops)[ticket.input.key]
          )))}
  ensures interp(s'.table).removes == interp(s.table).removes
  {
    ProcessQueryTicket_PreservesInv(s, s', ticket);
    var e := get_empty_cell(s.table);
    S.reveal_app_queries();
    UsefulTriggers();

    var x := S.Summary(map[],
        multiset{},
        multiset{S.QueryUnknown(ticket.rid, ticket.input.key)},
        multiset{});

    var pos := HT.hash(ticket.input.key) as int;

    forall k | 0 <= k < HT.FixedSize() && adjust(k, e+1) < adjust(pos, e+1)
    ensures S.commutes(x, S.f(s.table[k]))
    {
      assert ValidHashInSlot(s.table, e, k);
      assert ValidHashOrdering(s.table, e, k, pos);
      assert ValidHashInSlot(s.table, pos, k);
      assert ValidHashInSlot(s.table, k, pos);
      assert ActionNotPastKey(s.table, e, k, pos);
      assert ActionNotPastKey(s.table, e, pos, k);
    }

    preserves_1_left(s.table, s'.table, pos, e, x);

    if ticket.input.key !in map_remove_nones(interp(s.table).ops) {
      calc {
        apply_to_query_stub(interp(s'.table).queries);
        apply_to_query_stub(S.add(x, interp(s.table)).queries);
        apply_to_query_stub(S.app_queries(x.queries, interp(s.table).ops) + interp(s.table).queries);
        {
          Multisets.ApplyAdditive(to_query_stub,
            S.app_queries(x.queries, interp(s.table).ops), interp(s.table).queries);
        }
        apply_to_query_stub(S.app_queries(x.queries, interp(s.table).ops))
          + apply_to_query_stub(interp(s.table).queries);
        {
          //assert to_query_stub(S.app_query(S.QueryUnknown(ticket.rid, ticket.input.key),
          //    interp(s.table).ops))
          //  == HT.Stub(ticket.rid, MapIfc.QueryOutput(NotFound));
          //assert S.app_queries(x.queries, interp(s.table).ops)
          //    == multiset{S.app_query(S.QueryUnknown(ticket.rid, ticket.input.key),
          //    interp(s.table).ops)};
          Multisets.ApplySingleton(to_query_stub, S.app_query(S.QueryUnknown(ticket.rid, ticket.input.key), interp(s.table).ops));
          //assert apply_to_query_stub(S.app_queries(x.queries, interp(s.table).ops))
          //    == apply_to_query_stub(multiset{S.app_query(S.QueryUnknown(ticket.rid, ticket.input.key), interp(s.table).ops)})
          //    == multiset{HT.Stub(ticket.rid, MapIfc.QueryOutput(NotFound))};
        }
        apply_to_query_stub(interp(s.table).queries)
          + multiset{HT.Stub(ticket.rid, MapIfc.QueryOutput(NotFound))};
      }
    } else {
      calc {
        apply_to_query_stub(interp(s'.table).queries);
        apply_to_query_stub(S.add(x, interp(s.table)).queries);
        apply_to_query_stub(S.app_queries(x.queries, interp(s.table).ops) + interp(s.table).queries);
        {
          Multisets.ApplyAdditive(to_query_stub,
            S.app_queries(x.queries, interp(s.table).ops), interp(s.table).queries);
        }
        apply_to_query_stub(S.app_queries(x.queries, interp(s.table).ops))
          + apply_to_query_stub(interp(s.table).queries);
        {
          Multisets.ApplySingleton(to_query_stub, S.app_query(S.QueryUnknown(ticket.rid, ticket.input.key), interp(s.table).ops));
        }
        apply_to_query_stub(interp(s.table).queries)
          + multiset{HT.Stub(ticket.rid, MapIfc.QueryOutput(Found(
              map_remove_nones(interp(s.table).ops)[ticket.input.key]
          )))};
      }
    }
  }

  lemma ProcessRemoveTicket_ChangesInterp(s: Variables, s': Variables, ticket: HT.Ticket)
  requires Inv(s)
  requires HT.ProcessRemoveTicket(s, s', ticket)
  ensures Inv(s')
  ensures map_remove_nones(interp(s'.table).ops)
       == MapRemove1(map_remove_nones(interp(s.table).ops), ticket.input.key)
  ensures interp(s'.table).stubs == interp(s.table).stubs
  ensures interp(s'.table).queries == interp(s.table).queries
  ensures ticket.input.key !in map_remove_nones(interp(s.table).ops) ==>
        apply_to_remove_stub(interp(s'.table).removes)
         == apply_to_remove_stub(interp(s.table).removes)
          + multiset{HT.Stub(ticket.rid, MapIfc.RemoveOutput(false))}
  ensures ticket.input.key in map_remove_nones(interp(s.table).ops) ==>
        apply_to_remove_stub(interp(s'.table).removes)
         == apply_to_remove_stub(interp(s.table).removes)
          + multiset{HT.Stub(ticket.rid, MapIfc.RemoveOutput(true))}
  {
    ProcessRemoveTicket_PreservesInv(s, s', ticket);
    var e := get_empty_cell(s.table);
    S.reveal_app_queries();
    UsefulTriggers();

    var x := S.Summary(map[ticket.input.key := None],
        multiset{},
        multiset{},
        multiset{S.QueryUnknown(ticket.rid, ticket.input.key)});

    var pos := HT.hash(ticket.input.key) as int;

    forall k | 0 <= k < HT.FixedSize() && adjust(k, e+1) < adjust(pos, e+1)
    ensures S.commutes(x, S.f(s.table[k]))
    {
      assert ValidHashInSlot(s.table, e, k);
      assert ValidHashOrdering(s.table, e, k, pos);
      assert ValidHashInSlot(s.table, pos, k);
      assert ValidHashInSlot(s.table, k, pos);
      assert ActionNotPastKey(s.table, e, k, pos);
      assert ActionNotPastKey(s.table, e, pos, k);
    }

    preserves_1_left(s.table, s'.table, pos, e, x);

    if ticket.input.key !in map_remove_nones(interp(s.table).ops) {
      calc {
        apply_to_remove_stub(interp(s'.table).removes);
        apply_to_remove_stub(S.add(x, interp(s.table)).removes);
        apply_to_remove_stub(S.app_queries(x.removes, interp(s.table).ops) + interp(s.table).removes);
        {
          Multisets.ApplyAdditive(to_remove_stub,
            S.app_queries(x.removes, interp(s.table).ops), interp(s.table).removes);
        }
        apply_to_remove_stub(S.app_queries(x.removes, interp(s.table).ops))
          + apply_to_remove_stub(interp(s.table).removes);
        {
          Multisets.ApplySingleton(to_remove_stub, S.app_query(S.QueryUnknown(ticket.rid, ticket.input.key), interp(s.table).ops));
        }
        apply_to_remove_stub(interp(s.table).removes)
          + multiset{HT.Stub(ticket.rid, MapIfc.RemoveOutput(false))};
      }
    } else {
      calc {
        apply_to_remove_stub(interp(s'.table).removes);
        apply_to_remove_stub(S.add(x, interp(s.table)).removes);
        apply_to_remove_stub(S.app_queries(x.removes, interp(s.table).ops) + interp(s.table).removes);
        {
          Multisets.ApplyAdditive(to_remove_stub,
            S.app_queries(x.removes, interp(s.table).ops), interp(s.table).removes);
        }
        apply_to_remove_stub(S.app_queries(x.removes, interp(s.table).ops))
          + apply_to_remove_stub(interp(s.table).removes);
        {
          Multisets.ApplySingleton(to_remove_stub, S.app_query(S.QueryUnknown(ticket.rid, ticket.input.key), interp(s.table).ops));
        }
        apply_to_remove_stub(interp(s.table).removes)
          + multiset{HT.Stub(ticket.rid, MapIfc.RemoveOutput(true))};
      }
    }
  }
}
