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

  lemma preserves_2(table: seq<Option<HT.Info>>,
      table': seq<Option<HT.Info>>,
      i: int,
      f: int)
  requires Complete(table)
  requires Complete(table')
  requires InvTable(table)
  requires InvTable(table')
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

  /*lemma UsefulTriggers()
  ensures forall fn: S.QueryRes ~> S.QueryRes :: Multisets.Apply(fn, multiset{}) == multiset{};
  ensures forall fn: S.QueryRes ~> S.QueryRes, a :: Multisets.Apply(fn, multiset{a}) == multiset{fn(a)}
  {
  }*/

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


  lemma InsertDone_PreservesInterp(s: Variables, s': Variables, pos: nat)
  requires Inv(s)
  requires HT.InsertDone(s, s', pos)
  ensures Inv(s')
  ensures interp(s.table) == interp(s'.table)
  {
    InsertDone_PreservesInv(s, s', pos);
    var e := get_empty_cell(s.table);
    S.reveal_app_queries();

    assert S.f(s.table[pos]).ops == S.f(s'.table[pos]).ops;
    assert S.f(s.table[pos]).stubs == S.f(s'.table[pos]).stubs;
    assert S.f(s.table[pos]).queries == S.f(s'.table[pos]).queries;

    preserves_1(s.table, s'.table, pos, e);
  }

  /*

  lemma InsertUpdate_PreservesInterp(s: Variables, s': Variables, pos: nat)
  requires Inv(s)
  requires HT.InsertUpdate(s, s', pos)
  ensures Inv(s')
  ensures interp(s.table) == interp(s'.table)
  {
    InsertUpdate_PreservesInv(s, s', pos);
    var e := get_empty_cell(s.table);
    S.reveal_app_queries();


    preserves_1(s.table, s'.table, pos, e);
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
    preserves_2(s.table, s'.table, pos, e);
  }

  lemma QueryDone_PreservesInterp(s: Variables, s': Variables, pos: nat)
  requires Inv(s)
  requires HT.QueryDone(s, s', pos)
  ensures Inv(s')
  ensures interp(s.table) == interp(s'.table)
  {
    QueryDone_PreservesInv(s, s', pos);
    var e := get_empty_cell(s.table);
    S.reveal_app_queries();
    preserves_1(s.table, s'.table, pos, e);
  }

  lemma QueryNotFound_PreservesInterp(s: Variables, s': Variables, pos: nat)
  requires Inv(s)
  requires HT.QueryNotFound(s, s', pos)
  ensures Inv(s')
  ensures interp(s.table) == interp(s'.table)
  {
    QueryNotFound_PreservesInv(s, s', pos);
    var e := get_empty_cell(s.table);
    S.reveal_app_queries();
    preserves_2(s.table, s'.table, pos, e);
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
    preserves_2(s.table, s'.table, pos, e);
  }

  lemma RemoveFoundIt_PreservesInterp(s: Variables, s': Variables, pos: nat)
  requires Inv(s)
  requires HT.RemoveFoundIt(s, s', pos)
  ensures Inv(s')
  ensures interp(s.table) == interp(s'.table)
  {
    RemoveFoundIt_PreservesInv(s, s', pos);
    var e := get_empty_cell(s.table);
    S.reveal_app_queries();
    preserves_2(s.table, s'.table, pos, e);
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
    preserves_2(s.table, s'.table, pos, e);
  }

  lemma RemoveDone_PreservesInterp(s: Variables, s': Variables, pos: nat)
  requires Inv(s)
  requires HT.RemoveDone(s, s', pos)
  ensures Inv(s')
  ensures interp(s.table) == interp(s'.table)
  {
    RemoveDone_PreservesInv(s, s', pos);
    var e := get_empty_cell(s.table);
    S.reveal_app_queries();
    preserves_1(s.table, s'.table, pos, e);
  }*/
}
