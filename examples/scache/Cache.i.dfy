include "AtomicRefcount.i.dfy"
include "AtomicStatus.i.dfy"

module CacheImpl {
  import opened Constants
  import opened AtomicStatusImpl
  import opened AtomicRefcountImpl
  import opened Ptrs
  import opened LinearMaybe

  datatype Cache = Cache(
    data: seq<Ptr>,
    status: seq<AtomicStatus>,
    read_refcounts: seq<seq<AtomicRefcount>>
  )

  predicate Inv(c: Cache)
  {
    && |c.data| == CacheSize()
    && |c.status| == CacheSize()
    && (forall i | 0 <= i < CacheSize() ::
       atomic_status_inv(c.status[i], c.data[i]))
    && |c.read_refcounts| == NThreads()
    && (forall j | 0 <= j < NThreads() ::
        |c.read_refcounts[j]| == CacheSize())
    && (forall j, i | 0 <= j < NThreads() && 0 <= i < CacheSize() ::
        atomic_refcount_inv(c.read_refcounts[j][i], c.data[i], j))
  }

  method take_write_lock(c: Cache, cache_idx: int)
  returns (linear w: ReadWriteLockResources.Q)
  requires Inv(c)
  requires 0 <= cache_idx < CacheSize()
  decreases *
  {
    linear var w_maybe := empty();
    var success := false;

    while !success 
    invariant success ==> w_maybe == give(
        ReadWriteLockResources.WritePendingAwaitBack(c.data[cache_idx]))
    invariant !success ==> !has(w_maybe)
    decreases *
    {
      var _ := discard(w_maybe);
      success, w_maybe := try_set_write_lock(
          c.status[cache_idx], c.data[cache_idx]);
    }

    w := unwrap(w_maybe);

    success := false;

    while !success 
    invariant !success ==> w ==
        ReadWriteLockResources.WritePendingAwaitBack(c.data[cache_idx])
    invariant success ==> w ==
        ReadWriteLockResources.WritePending(c.data[cache_idx], 0)
    decreases *
    {
      success, w := try_check_writeback_isnt_set(
          c.status[cache_idx], c.data[cache_idx], w);
    }

    var j := 0;
    while j < NThreads()
    invariant 0 <= j <= NThreads()
    invariant w == 
        ReadWriteLockResources.WritePending(c.data[cache_idx], j)
    {
      success := false;

      while !success 
      invariant !success ==> w ==
          ReadWriteLockResources.WritePending(c.data[cache_idx], j)
      invariant success ==> w ==
          ReadWriteLockResources.WritePending(c.data[cache_idx], j+1)
      decreases *
      {
        success, w := is_refcount_zero(c.read_refcounts[j][cache_idx],
            c.data[cache_idx], j, w);
      }

      j := j + 1;
    }
  }
}
