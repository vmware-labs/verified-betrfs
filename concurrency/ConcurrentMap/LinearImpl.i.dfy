// Copyright 2018-2021 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, and University of Washington
// SPDX-License-Identifier: BSD-2-Clause

include "../../lib/Base/Option.s.dfy"
include "ConcurrentLinearHashTable.i.dfy"
include "../../lib/Lang/LinearSequence.i.dfy"

abstract module TrustedConcurrencyPrimitives {
  import opened Options

  ///////////////
  // Thread ID

  type ThreadID /*ghost*/
  type Thread /*ghost*/
  function tid(t: Thread) : ThreadID

  ///////////////
  // Yield/phases

  type Phase /*ghost*/
  predicate is_rising(p: Phase)

  type YieldGlobals /*ghost*/ /* impl defined */
  predicate Inv(yg: YieldGlobals) /* impl defined */

  /*ghost*/ method do_yield(
      linear /*ghost*/ yg: YieldGlobals,
      linear /* ghost */ p: Phase)
  returns (
      linear /*ghost*/ yg': YieldGlobals,
      linear /* ghost*/ p': Phase)
  requires Inv(yg)
  ensures Inv(yg')
  ensures is_rising(p')

  ///////////////
  // Mutex library

  type Mutex<V> /*ghost*/
  type MutexRef<V>
  predicate {:axiom} mutex_ref<V>(m: Mutex<V>, ref: MutexRef<V>)

  function {:axiom} mutex_has<V>(m: Mutex<V>) : Option<ThreadID>
  function {:axiom} mutex_value<V>(m: Mutex<V>) : V
  requires mutex_has(m) == None

  method {:axiom} new_mutex<V>(linear v: V)
  returns (linear /*ghost*/ m: Mutex<V>, ref: MutexRef<V>)
  ensures mutex_ref(m, ref)
  ensures mutex_has(m) == None
  ensures mutex_value(m) == v

  method {:axiom} acquire_mutex<V>(
      ref: MutexRef<V>,
      /*ghost*/ linear m: Mutex<V>,
      /*ghost*/ linear t: Thread,
      /*ghost*/ linear p: Phase)
  returns (
    linear v: V,
    /*ghost*/ linear m': Mutex<V>,
    /*ghost*/ linear t': Thread,
    /*ghost*/ linear p': Phase
  )
  requires mutex_ref(m, ref)
  requires is_rising(p)
  ensures mutex_ref(m', ref)
  ensures is_rising(p')
  ensures t' == t
  ensures mutex_has(m) == None
  ensures mutex_has(m') == Some(tid(t))
  ensures v == mutex_value(m)

  method {:axiom} release_mutex<V>(
      ref: MutexRef<V>,
      linear v: V,
      /*ghost*/ linear m: Mutex<V>,
      /*ghost*/ linear t: Thread,
      /*ghost*/ linear p: Phase)
  returns (
    /*ghost*/ linear m': Mutex<V>,
    /*ghost*/ linear t': Thread,
    /*ghost*/ linear p': Phase
  )
  requires mutex_ref(m, ref)
  requires mutex_has(m) == Some(tid(t))
  ensures mutex_ref(m', ref)
  ensures t' == t
  ensures mutex_has(m') == None
  ensures mutex_value(m') == v
}

module AppSpec {
  import ConcurrentMap
  import L = LocalConcurrentLinearHashTable

  type Key = ConcurrentMap.Key
  type Value = ConcurrentMap.Value

  datatype Source<S> = Source(x: int) // TODO make opaque
  {
    function state() : S
  }
  type AbstractGlobalState = Source<L.SharedVariables>
  type AbstractLocalState = Source<L.ThreadState>

  // TODO this needs to track the thread id
  datatype QueryPlace = Start | Mid(key: Key) | End(key: Key, value: Value)

  linear datatype QueryTransitionTracker =
      QueryTransitionTracker(x: int) // TODO make opaque
  {
    function place() : QueryPlace
  }

  /*ghost*/ method {:axiom} transfer_QueryInit(
        linear tt: QueryTransitionTracker,
        linear global: AbstractGlobalState,
        linear local: AbstractLocalState,
        ghost g': L.SharedVariables,
        ghost l': L.ThreadState,
        key: Key
  )
  returns (
      /*ghost*/ linear tt' : QueryTransitionTracker,
      /*ghost*/ linear global': AbstractGlobalState,
      /*ghost*/ linear local': AbstractLocalState
  ) 
  requires L.QueryInit(global.state(), g', local.state(), l', key)
  requires tt.place() == Start
  ensures tt.place() == Mid(key)
  ensures global'.state() == g'
  ensures local'.state() == l'

  /*ghost*/ method {:axiom} transfer_QueryAdvance(
        linear tt: QueryTransitionTracker,
        linear global: AbstractGlobalState,
        linear local: AbstractLocalState,
        ghost g': L.SharedVariables,
        ghost l': L.ThreadState
  )
  returns (
      linear tt' : QueryTransitionTracker,
      linear global': AbstractGlobalState,
      linear local': AbstractLocalState
  ) 
  requires L.QueryAdvance(global.state(), g', local.state(), l')
  ensures tt'.place() == tt.place()
  ensures global'.state() == g'
  ensures local'.state() == l'

  /*ghost*/ method {:axiom} transfer_QueryComplete(
        linear tt: QueryTransitionTracker,
        linear global: AbstractGlobalState,
        linear local: AbstractLocalState,
        ghost g': L.SharedVariables,
        ghost l': L.ThreadState,
        value: Value
  )
  returns (
      linear tt' : QueryTransitionTracker,
      linear global': AbstractGlobalState,
      linear local': AbstractLocalState
  ) 
  requires L.QueryComplete(global.state(), g', local.state(), l', value)
  requires tt.place().Mid?
  ensures tt'.place() == End(tt.place().key, value)
  ensures global'.state() == g'
  ensures local'.state() == l'
}

module Impl refines TrustedConcurrencyPrimitives {
  import L = LocalConcurrentLinearHashTable
  import AppSpec
  import opened LinearSequence_i
  import opened LinearSequence_s
  import opened NativeTypes

  // global state, accessible by any thread
  // Leaves open the question of how this gets initialized
  type HashTable = seq<MutexRef<L.Item>>
  function method hash_table() : (ht: HashTable)
  ensures |ht| > 0

  linear datatype YieldGlobals = YieldGlobals(
      linear mutexes: lseq<Mutex<L.Item>>,
      linear abstractGlobalState: AppSpec.AbstractGlobalState
  )

  predicate Inv(yg: YieldGlobals)
  {
    var ht := hash_table();
    && |ht| == |yg.mutexes|
    && |ht| == |yg.abstractGlobalState.state().table|
    && (forall i | 0 <= i < |ht| :: lseq_has(yg.mutexes)[i])
    && (forall i | 0 <= i < |ht| :: mutex_ref(yg.mutexes[i], ht[i]))
    && (forall i | 0 <= i < |ht| ::
        mutex_has(yg.mutexes[i]) == None
        && yg.abstractGlobalState.state().table[i]
          == mutex_value(yg.mutexes[i])
        )
  }

  method query(
    key: AppSpec.Key,
    /*ghost*/ linear t: Thread,
    /*ghost*/ linear p: Phase,
    /*ghost*/ linear yg: YieldGlobals,
    /*ghost*/ linear tt: AppSpec.QueryTransitionTracker,
    /*ghost*/ linear local: AppSpec.AbstractLocalState)
  returns (
    res: AppSpec.Value,
    linear p': Phase,
    linear t': Thread,
    linear yg': YieldGlobals,
    linear tt': AppSpec.QueryTransitionTracker,
    linear local': AppSpec.AbstractLocalState
  )
  requires tt.place() == AppSpec.Start
  requires Inv(yg)
  requires local.state() == L.Idle
  ensures tt'.place() == AppSpec.End(key, res)
  ensures Inv(yg')
  ensures tid(t') == tid(t)
  {
    var ht := hash_table();
    var slot := L.SlotForKey(|ht|, key);

    linear var YieldGlobals(mutexes, abstractGlobalState) := yg;

    assert L.QueryInit(abstractGlobalState.state(), abstractGlobalState.state(),
        L.Idle, L.ThreadState.Query(key, slot), key);
    linear var tt1, abstractGlobalState1, local1 := AppSpec.transfer_QueryInit(tt, abstractGlobalState, local, abstractGlobalState.state(), L.ThreadState.Query(key, slot), key);

    linear var yg1 := YieldGlobals(mutexes, abstractGlobalState1);

    res, p', t', yg', tt', local' := query_loop(key, slot, p, t, yg1, tt1, local1);
  }

  method clone<V>(shared v: V) returns (v': V)
  ensures v' == v

  method query_loop(
    key: AppSpec.Key,
    slot: L.Slot,
    linear p: Phase,
    linear t: Thread,
    linear yg: YieldGlobals,
    linear tt: AppSpec.QueryTransitionTracker,
    linear local: AppSpec.AbstractLocalState
  )
  returns (
    res: AppSpec.Value,
    linear p': Phase,
    linear t': Thread,
    linear yg': YieldGlobals,
    linear tt': AppSpec.QueryTransitionTracker,
    linear local': AppSpec.AbstractLocalState
  )
  requires is_rising(p)
  requires Inv(yg)
  requires local.state() == L.ThreadState.Query(key, slot)
  requires tt.place() == AppSpec.Mid(key)
  requires 0 <= slot.slot < |hash_table()|
  ensures tt'.place() == AppSpec.End(key, res)
  ensures Inv(yg')
  decreases |hash_table()| - slot.slot
  {
    /*ghost*/ linear var p1;
    /*ghost*/ linear var p2;
    /*ghost*/ linear var p3;
    /*ghost*/ linear var t1;
    /*ghost*/ linear var t2;
    /*ghost*/ linear var tt1;
    /*ghost*/ linear var m1;
    /*ghost*/ linear var m2;
    /*ghost*/ linear var abstractGlobalState1;
    /*ghost*/ linear var yg1;

    var ht := hash_table();

    // lseq_give and lseq_take are built to use uint64
    // would make sense to use nat-versions since it's ghost anyway
    assume slot.slot < 0x1_0000_0000_0000_0000;

    linear var YieldGlobals(mutexes, abstractGlobalState) := yg;
    linear var mutexes1, m := lseq_take(mutexes, slot.slot as uint64);

    linear var lentry;
    lentry, m1, t1, p1 := acquire_mutex(ht[slot.slot], m, t, p);

    //assert entry == I(s).table[slot.slot];

    var entry := clone(lentry);

    m2, t2, p2 := release_mutex(ht[slot.slot], lentry, m1, t1, p1);

    linear var mutexes2 := lseq_give(mutexes1, slot.slot as uint64, m2);

    //assert entry == I(s).table[slot.slot];

    if entry.Empty? {
      assume false; // TODO support returning None for 'not found'
      p' := p2;
      yg' := YieldGlobals(mutexes2, abstractGlobalState);
      tt' := tt;
      t' := t2;
      local' := local;
    } else if entry.key == key {
      if entry.Tombstone? {
        assume false; // TODO support returning None for 'not found'
        p' := p2;
        yg' := YieldGlobals(mutexes2, abstractGlobalState);
        tt' := tt;
        t' := t2;
        local' := local;
      } else {
        p' := p2;
        res := entry.value;

        tt', abstractGlobalState1, local' := AppSpec.transfer_QueryComplete(
          tt,
          abstractGlobalState,
          local,
          abstractGlobalState.state(),
          L.Idle,
          res);

        yg' := YieldGlobals(mutexes2, abstractGlobalState1);
        t' := t2;
      }
    } else {
      // TODO support returning None for 'not found' if you reach the end
      assume slot.slot + 1 < |ht|;

      var slot' := L.Slot(slot.slot + 1);

      //assert L.QueryAdvance(old(I(s)), I(s), L.ThreadState.Query(key, slot), L.ThreadState.Query(key, slot'));
      tt1, abstractGlobalState1, local' := AppSpec.transfer_QueryAdvance(
        tt,
        abstractGlobalState,
        local,
        abstractGlobalState.state(),
        L.ThreadState.Query(key, slot'));

      //assert Inv(s, source1);
      //assert source1.local() == L.ThreadState.Query(key, slot');
      //assert tt1.place() == AppSpec.Mid(key);

      yg1 := YieldGlobals(mutexes2, abstractGlobalState1);

      yg', p3 := do_yield(yg1, p2);

      res, p', t', yg', tt', local' :=
          query_loop(key, slot', p3, t2, yg', tt1, local');
    }
  }
}
