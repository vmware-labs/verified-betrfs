include "../../lib/Base/Option.s.dfy"
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

  ///////////////
  // Compare-and-exchange library

  type Cell<V>
  type CellRef<V>
  predicate {:axiom} cell_ref<V>(c: Cell<V>, ref: CellRef<V>)

  function {:axiom} cell_value<V>(c: Cell<V>) : V

  method {:axiom} new_cell<V>(v: V)
  returns (linear /*ghost*/ c: Cell<V>, ref: CellRef<V>)
  ensures cell_ref(c, ref)
  ensures cell_value(c) == v

  method {:axiom} compare_and_set<V>(
    ref: CellRef<V>,
    /*ghost*/ linear c: Cell<V>,
    old_v: V,
    new_v: V,
    linear p: Phase)
  returns (
    did_set: bool,
    /*ghost*/ linear c': Cell<V>,
    linear p': Phase)
  requires cell_ref(c, ref)
  requires is_rising(p)
  ensures cell_ref(c', ref)
  ensures did_set ==> cell_value(c) == old_v && cell_value(c') == new_v
  ensures !did_set ==> cell_value(c) != old_v && cell_value(c') == cell_value(c)
}

module StateObjects {
  datatype Status = Unmatched | Reading | Clean | Dirty | Writing

  type Data

  datatype StateObject =
    | DiskBlockMatch(disk_idx: nat, cache_idx: nat)
    | DiskBlockUnmatched(disk_idx: nat)
    | CacheState(cache_idx: nat, data: Data, status: Status)

  method transform(linear cache_state: StateObject, linear unm: StateObject)
  returns (linear cache_state': StateObject, linear ma: StateObject)
  requires cache_state.CacheState?
  requires cache_state.status == Unmatched
  requires unm.DiskBlockUnmatched?

  ensures cache_state' == cache_state.(status := Reading)
  ensures ma == DiskBlockMatch(unm.disk_idx, cache_state.cache_idx)
}

module Impl refines TrustedConcurrencyPrimitives {
  import opened StateObjects

  import opened LinearSequence_i
  import opened LinearSequence_s
  import opened NativeTypes

  linear datatype CacheEntry = CacheEntry(
    linear data: Data,
    status: Status,
    linear r: StateObject)

  datatype Cache = Cache(
    disk_idx_to_cache_idx: seq<CellRef<int>>,
    cache_data: seq<MutexRef<CacheEntry>>
  )

  const cache: Cache;

  linear datatype DiskEntry = DiskEntry(
      linear cache_idx_cell: Cell<int>,
      linear r: StateObject)

  linear datatype YieldGlobals = YieldGlobals(
      //linear mutexes: lseq<Mutex<L.Item>>,
      //linear abstractGlobalState: AppSpec.AbstractGlobalState
      linear disk_entries: lseq<DiskEntry>,
      linear cache_entries: lseq<Mutex<CacheEntry>>
  )

  predicate DiskEntryInv(entry: DiskEntry, i: int)
  {
    && (entry.r.DiskBlockMatch? || entry.r.DiskBlockUnmatched?)
    && entry.r.disk_idx == i
    && (entry.r.DiskBlockMatch? ==>
      && 0 <= entry.r.cache_idx < |cache.cache_data|
      && cell_value(entry.cache_idx_cell) == entry.r.cache_idx
    )
    && (entry.r.DiskBlockUnmatched? ==> cell_value(entry.cache_idx_cell) == -1)
  }

  predicate CacheEntryInv(entry: CacheEntry, i: nat)
  {
    entry.r == CacheState(i, entry.data, entry.status)
  }

  predicate Inv(yg: YieldGlobals)
  {
    && |yg.disk_entries| == |cache.disk_idx_to_cache_idx|
    && |yg.cache_entries| == |cache.cache_data|
    && (forall i | 0 <= i < |yg.disk_entries| :: i in yg.disk_entries)
    && (forall i | 0 <= i < |yg.cache_entries| :: i in yg.cache_entries)
    && (forall i | 0 <= i < |yg.disk_entries| :: DiskEntryInv(yg.disk_entries[i], i))
    && (forall i | 0 <= i < |yg.disk_entries| ::
        cell_ref(yg.disk_entries[i].cache_idx_cell, cache.disk_idx_to_cache_idx[i]))
    && (forall i | 0 <= i < |yg.cache_entries| ::
        mutex_has(yg.cache_entries[i]).None? ==>
          CacheEntryInv(mutex_value(yg.cache_entries[i]), i))
    && (forall i | 0 <= i < |yg.cache_entries| ::
        mutex_ref(yg.cache_entries[i], cache.cache_data[i]))
  }

  method page_in(
      linear yg: YieldGlobals,
      linear p: Phase,
      linear t: Thread,
      disk_idx: int,
      cache_idx: int)
  returns (
      linear yg': YieldGlobals,
      linear p': Phase,
      linear t': Thread)
  requires is_rising(p)
  requires 0 <= disk_idx < |cache.disk_idx_to_cache_idx| < 0x1_0000_0000_0000_0000
  requires 0 <= cache_idx < |cache.cache_data| < 0x1_0000_0000_0000_0000
  requires Inv(yg)
  ensures Inv(yg')
  {
    linear var YieldGlobals(disk_entries, cache_entries) := yg;

    linear var mutexes, m := lseq_take(cache_entries, cache_idx as uint64);
    linear var cells, de := lseq_take(disk_entries, disk_idx as uint64);

    linear var cache_entry, m1, t1, p1 := acquire_mutex(cache.cache_data[cache_idx], m, t, p);

    if cache_entry.status != Unmatched {
      // bail out
      linear var m2, t2, p2 := release_mutex(cache.cache_data[cache_idx], cache_entry, m1, t1, p1);

      linear var mutexes1 := lseq_give(mutexes, cache_idx as uint64, m2);
      linear var cells1 := lseq_give(cells, disk_idx as uint64, de);
      yg' := YieldGlobals(cells1, mutexes1);
      t' := t2;
      p' := p2;
    } else {
      assert DiskEntryInv(de, disk_idx);

      var compare_and_set_succ;
      linear var DiskEntry(c, o) := de;
      linear var c', p2;
      compare_and_set_succ, c', p2 := compare_and_set(
            cache.disk_idx_to_cache_idx[disk_idx],
            c,
            -1, cache_idx,
            p1);

      linear var cache_entry';
      linear var o';

      if compare_and_set_succ {
        //if !o.DiskBlockUnmatched? {
        //  assert o.DiskBlockMatch?;
        //}

        linear var CacheEntry(data, status, r) := cache_entry;

        linear var r';
        r', o' := transform(r, o);

        cache_entry' := CacheEntry(data, Reading, r');
      } else {
        cache_entry' := cache_entry;
        o' := o;
      }

      linear var m2, t3, p3 := release_mutex(cache.cache_data[cache_idx], cache_entry', m1, t1, p2);

      linear var mutexes1 := lseq_give(mutexes, cache_idx as uint64, m2);
      linear var cells1 :=
          lseq_give(cells, disk_idx as uint64, DiskEntry(c', o'));
      yg' := YieldGlobals(cells1, mutexes1);
      t' := t3;
      p' := p3;
    }
  }
}
