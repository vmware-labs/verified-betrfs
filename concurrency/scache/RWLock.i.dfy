include "Ext.i.dfy"
include "Constants.i.dfy"
include "FullMap.i.dfy"
include "../../lib/Base/Option.s.dfy"

module RWLockExt refines SimpleExt {
  import opened Constants
  import opened Options
  import opened FullMaps

  /*
   * We consider two bits of the status field, ExcLock and WriteBack.
   *
   * ExcLock and WriteBack. Of course, 'ExcLock'
   * and 'WriteBack' should be exclusive operations;
   * When both flags are set,
   * it should be interpreted as the 'ExcLock' being
   * pending, with the 'WriteBack' being active.
   *
   * Those 2 bits gives 2x2 = 4 states. We then have 2 more:
   * Unmapped and Reading.
   *
   * NOTE: in retrospect, it might have made sense to have this
   * just be a struct of 5-6 booleans.
   */
  datatype Flag =
    | Unmapped
    | Reading
    | Reading_ExcLock
    | Available
    | WriteBack
    | WriteBack_PendingExcLock
    | PendingExcLock
    | ExcLock_Clean
    | ExcLock_Dirty

  type ThreadId = nat

  // Standard flow for obtaining a 'shared' lock

  datatype SharedState =
    | SharedPending(t: ThreadId)              // inc refcount
    | SharedPending2(t: ThreadId)             // !free & !writelocked
    | SharedObtained(t: ThreadId, b: Base.M)  // !reading

  // Standard flow for obtaining an 'exclusive' lock

  datatype ExcState = 
    | ExcNone
      // set ExcLock bit:
    | ExcPendingAwaitWriteBack(t: int)
      // check WriteBack bit unset
      //   and `visited` of the refcounts
    | ExcPending(t: int, visited: int, clean: bool)
    | ExcObtained(t: int, clean: bool)

  // Flow for the phase of reading in a page from disk.
  // This is a special-case flow, because it needs to be performed
  // on the way to obtaining a 'shared' lock, but it requires
  // exclusive access to the underlying memory and resources.
  // End-game for this flow is to become an ordinary 'shared' lock

  datatype ReadState =
    | ReadNone
    | ReadPending                   // set status bit to ExcLock | Reading
    | ReadPendingCounted(t: int)    // inc refcount
    | ReadObtained(t: int)          // clear ExcLock bit

  datatype M = M(
    flags: Option<Flag>,
    stored_value: Option<Base.M>,
    refCounts: map<ThreadId, nat>,

    sharedState: FullMap<SharedState, nat>,
    exc: ExcState,
    read: ReadState,

    // Flow for the phase of doing a write-back.
    // Special case in part because it can be initiated by any thread
    // and completed by any thread (not necessarily the same one).
    
    writeback: bool              // set WriteBack status bit
  )

  type F = M

  function unit() : F
  {
    M(None, None, map[], zero_map(), ExcNone, ReadNone, false)
  }

  predicate dot_defined(a: F, b: F)
  {
    && !(a.flags.Some? && b.flags.Some?)
    && !(a.stored_value.Some? && b.stored_value.Some?)
    && a.refCounts.Keys !! b.refCounts.Keys
    && (a.exc.ExcNone? || b.exc.ExcNone?)
    && (a.read.ReadNone? || b.read.ReadNone?)
    && !(a.writeback && b.writeback)
  }

  function dot(a: F, b: F) : F
    //requires dot_defined(a, b)
  {
    M(
      if a.flags.Some? then a.flags else b.flags,
      if a.stored_value.Some? then a.stored_value else b.stored_value,
      (map k | k in a.refCounts.Keys + b.refCounts.Keys ::
          if k in a.refCounts.Keys then a.refCounts[k] else b.refCounts[k]),
      add_fns(a.sharedState, b.sharedState),
      if !a.exc.ExcNone? then a.exc else b.exc,
      if !a.read.ReadNone? then a.read else b.read,
      a.writeback || b.writeback
    ) 
  }

  lemma dot_unit(x: F)
  ensures dot_defined(x, unit())
  ensures dot(x, unit()) == x
  {
  }

  lemma commutative(x: F, y: F)
  //requires dot_defined(x, y)
  ensures dot_defined(y, x)
  ensures dot(x, y) == dot(y, x)
  {
  }

  lemma associative(x: F, y: F, z: F)
  //requires dot_defined(y, z)
  //requires dot_defined(x, dot(y, z))
  ensures dot_defined(x, y)
  ensures dot_defined(dot(x, y), z)
  ensures dot(x, dot(y, z)) == dot(dot(x, y), z)
  {
    assume false;
  }

  function IsSharedRefFor(t: nat) : (SharedState) -> bool
  {
    (ss: SharedState) => ss.t == t
  }

  function CountSharedRefs(m: FullMap<SharedState, nat>, t: nat) : nat
  {
    SumFilter(IsSharedRefFor(t), m)
  }

  function CountAllRefs(state: F, t: nat) : nat
  {
    CountSharedRefs(state.sharedState, t)

      + (if state.exc.ExcPendingAwaitWriteBack?
            || state.exc.ExcPending?
            || state.exc.ExcObtained?
         then 1 else 0)

      + (if state.read.ReadPendingCounted?
            || state.read.ReadObtained?
         then 1 else 0)
  }

  predicate Inv(state: F)
  {
    && state != unit() ==> (
      && state.flags.Some?
      && (state.exc.ExcPendingAwaitWriteBack? ==>
        && state.read.ReadNone?
        && -1 <= state.exc.t < NUM_THREADS
      )
      && (state.exc.ExcPending? ==>
        && state.read == ReadNone
        && !state.writeback
        && 0 <= state.exc.visited <= NUM_THREADS
        && -1 <= state.exc.t < NUM_THREADS
      )
      && (state.exc.ExcObtained? ==>
        && state.read == ReadNone
        && !state.writeback
        && -1 <= state.exc.t < NUM_THREADS
      )
      && (state.writeback ==>
        && state.read == ReadNone
      )
      && (state.read.ReadPending? ==>
        && !state.writeback
      )
      && (state.read.ReadPendingCounted? ==>
        && !state.writeback
        && 0 <= state.read.t < NUM_THREADS
      )
      && (
        state.read.ReadObtained? ==> 0 <= state.read.t < NUM_THREADS
      )
      && (state.exc.ExcObtained? ==> state.stored_value.None?)
      && (!state.read.ReadNone? ==> state.stored_value.None?)
      && (!state.exc.ExcObtained? && state.read.ReadNone?
          ==> state.stored_value.Some?)
      //&& (state.stored_value.Some? ==>
      //  state.stored_value.value.is_handle(key)
      //)
      && (forall t | 0 <= t <= NUM_THREADS
        :: t in state.refCounts && state.refCounts[t] == CountAllRefs(state, t))
    )
  }

  function Interp(a: F) : Base.M
    //requires Inv(a)

  predicate InternalNext(f: F, f': F)
  predicate CrossNext(f: F, f': F, b: Base.M, b': Base.M)

  lemma interp_unit()
  ensures Inv(unit()) && Interp(unit()) == Base.unit()

  lemma internal_step_preserves_interp(p: F, f: F, f': F)
  //requires InternalNext(f, f')
  //requires dot_defined(f, p)
  //requires Inv(dot(f, p))
  ensures dot_defined(f', p)
  ensures Inv(dot(f', p))
  ensures Interp(dot(f', p)) == Interp(dot(f, p))

  lemma cross_step_preserves_interp(p: F, f: F, f': F, b: Base.M, b': Base.M)
  //requires CrossNext(f, f', b, b')
  //requires dot_defined(f, p)
  //requires Inv(dot(f, p))
  //requires Base.dot_defined(Interp(dot(f, p)), b)
  ensures dot_defined(f', p)
  ensures Inv(dot(f', p))
  ensures Base.dot_defined(Interp(dot(f', p)), b')
  ensures Base.dot(Interp(dot(f', p)), b')
       == Base.dot(Interp(dot(f, p)), b)

}
