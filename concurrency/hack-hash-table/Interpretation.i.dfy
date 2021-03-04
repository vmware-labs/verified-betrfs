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
    queries: multiset<QueryRes>
  )

  type M = Summary

  function unit() : M {
    Summary(map[], multiset{}, multiset{})
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
        app_queries(x.queries, y.ops) + y.queries)
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
  }

  lemma add_unit(x: M)
  ensures add(x, unit()) == x
  ensures add(unit(), x) == x
  {
    reveal_app_queries();
    MultisetLemmas.ApplyId((q) => app_query(q, map[]), x.queries);
  }

  type Q = Option<HT.Info>

  function get_summary(info: HT.Info) : Summary {
    match info {
      case Info(Empty(), Free()) => unit()
      case Info(Full(kv), Free()) => Summary(
        map[kv.key := Some(kv.val)],
        multiset{},
        multiset{}
      )

      case Info(Empty(), Inserting(rid, ins_kv)) =>
        Summary(
          map[ins_kv.key := Some(ins_kv.val)],
          multiset{HT.Stub(rid, MapIfc.InsertOutput)},
          multiset{}
        )

      case Info(Full(kv), Inserting(rid, ins_kv)) =>
        Summary(
          map[kv.key := Some(kv.val)][ins_kv.key := Some(ins_kv.val)],
          multiset{HT.Stub(rid, MapIfc.InsertOutput)},
          multiset{}
        )

      case Info(Empty(), Removing(rid, remove_key)) =>
        Summary(
          map[remove_key := None],
          multiset{HT.Stub(rid, MapIfc.RemoveOutput)},
          multiset{}
        )

      case Info(Full(kv), Removing(rid, remove_key)) =>
        Summary(
          map[kv.key := Some(kv.val)][remove_key := None],
          multiset{HT.Stub(rid, MapIfc.RemoveOutput)},
          multiset{}
        )

      case Info(_, RemoveTidying(rid)) =>
        Summary(
          map[],
          multiset{HT.Stub(rid, MapIfc.RemoveOutput)},
          multiset{}
        )

      case Info(Empty(), Querying(rid, query_key)) =>
        Summary(
          map[],
          multiset{},
          multiset{QueryUnknown(rid, query_key)}
        )

      case Info(Full(kv), Querying(rid, query_key)) =>
        Summary(
          map[kv.key := Some(kv.val)],
          multiset{},
          (if kv.key == query_key
            then multiset{QueryFound(rid, query_key, Some(kv.val))}
            else multiset{QueryUnknown(rid, query_key)}
          )
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
  import S = SummaryMonoid
  import MultisetLemmas

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

  lemma separated_segments_commute(table: seq<Option<HT.Info>>, e: int, f: int,
      a: int, b: int, c: int, d: int)
  requires Complete(table)
  requires InvTable(table)
  requires is_good_root(table, e)
  requires is_good_root(table, f)
  requires 0 <= a < b <= |table|
  requires 0 <= c < d <= |table|
  requires |table| == HT.FixedSize()
  requires e != f
  requires adjust(a, e+1)
        <= adjust(b-1, e+1)
        <= adjust(f, e+1)
  requires adjust(c, f+1)
        <= adjust(d-1, f+1)
        <= adjust(e, f+1)
  ensures S.add(S.concat_map(table[a..b]), S.concat_map(table[c..d]))
      == S.add(S.concat_map(table[c..d]), S.concat_map(table[a..b]))
  {

    var x := S.concat_map(table[a..b]);
    var y := S.concat_map(table[c..d]);
    var a1 := S.add(x, y);
    var a2 := S.add(y, x);

    assert a1.stubs == a2.stubs;

    assert a1.ops == a2.ops by {
      forall k | k in x.ops && k in y.ops
      ensures false
      {
        var i := get_singleton_for_key(table[a..b], k);
        var j := get_singleton_for_key(table[c..d], k);

        var i1 := a + i;
        assert table[a..b][i] == table[i1];

        var j1 := c + j;
        assert table[c..d][j] == table[j1];

        assert ValidHashInSlot(table, e, i1);
        //assert ValidHashInSlot(table, e, j1);
        //assert ValidHashInSlot(table, f, i1);
        assert ValidHashInSlot(table, f, j1);

        //assert ValidHashOrdering(table, e, i1, j1);
        //assert ValidHashOrdering(table, e, j1, i1);
        //assert ValidHashOrdering(table, f, i1, j1);
        //assert ValidHashOrdering(table, f, j1, i1);

        //assert InsertionNotPastKey(table, e, i1, j1);
        //assert InsertionNotPastKey(table, e, j1, i1);
        //assert InsertionNotPastKey(table, f, i1, j1);
        //assert InsertionNotPastKey(table, f, j1, i1);

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
      }
      assume false;
    }
  }

  /*lemma separated_segments_commute(table: seq<Option<HT.Info>>, e: int, f: int,
      a: int, b: int, c: int, d: int)
  requires Complete(table)
  requires InvTable(table)
  requires is_good_root(table, e)
  requires is_good_root(table, f)
  requires 0 <= a <= b < |table|
  requires 0 <= c <= d < |table|
  requires adjust(a, e+1)
        <= adjust(b, e+1)
        <= adjust((if f < |table| - 1 then f + 1 else 0), e + 1)
        <= adjust(c, e+1)
        <= adjust(d, e+1)
  ensures S.add(S.concat_map(table[a..b]), S.concat_map(table[c..d]))
      == S.add(S.concat_map(table[c..d]), S.concat_map(table[a..b]))
  {
    assume e != f;

    var x := S.concat_map(table[a..b]);
    var y := S.concat_map(table[c..d]);
    var a1 := S.add(x, y);
    var a2 := S.add(y, x);

    assert a1.stubs == a2.stubs;

    assert a1.ops == a2.ops by {
      forall k | k in x.ops && k in y.ops
      ensures false
      {
        var i := get_singleton_for_key(table[a..b], k);
        var j := get_singleton_for_key(table[c..d], k);

        var i1 := a + i;
        assert table[a..b][i] == table[i1];

        var j1 := c + j;
        assert table[c..d][j] == table[j1];

        assert ValidHashInSlot(table, e, i1);
        assert ValidHashInSlot(table, e, j1);
        assert ValidHashInSlot(table, f, i1);
        assert ValidHashInSlot(table, f, j1);

        assert ValidHashOrdering(table, e, i1, j1);
        assert ValidHashOrdering(table, e, j1, i1);
        assert ValidHashOrdering(table, f, i1, j1);
        assert ValidHashOrdering(table, f, j1, i1);

        assert InsertionNotPastKey(table, e, i1, j1);
        assert InsertionNotPastKey(table, e, j1, i1);
        assert InsertionNotPastKey(table, f, i1, j1);
        assert InsertionNotPastKey(table, f, j1, i1);

        if table[i1].value.entry.Full? && table[i1].value.entry.kv.key == k {
          if table[j1].value.entry.Full? && table[j1].value.entry.kv.key == k {
            if e + 1 == |table| {
              assert false;
            } else if e + 1 == 1 {
              var e' := (if e < |table| - 1 then e + 1 else 0);
              var f' := (if f < |table| - 1 then f + 1 else 0);
              var h := HT.hash(table[i1].value.entry.kv.key) as int;
              assert adjust(h, f') <= adjust(j1, f');

              assert adjust(j1, f') < adjust(d, f');
              assert d != f';
              assert adjust(d, f') <= adjust(e', f');
              assert adjust(j1, f') < adjust(e', f');

              assert adjust(f', e') <= adjust(h, e');
              assert adjust(f', e+1) <= adjust(h, e+1);
              assert adjust(h, e+1) <= adjust(j1, e+1);

              assert false;
            } else {
              assert false;
            }
          } else {
            assert false;
          }
        } else {
          assert false;
        }
      }
    }

    assume false;

    assert a1.queries == a2.queries by {
    }
  }*/

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
        assert table[e+1..f+1] + table[f+1..] == table[e+1..];
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
        separated_segments_commute(table, e, f, 0, e+1, e+1, f+1);
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
}
