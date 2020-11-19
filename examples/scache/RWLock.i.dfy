include "ArrayPtr.s.dfy"
include "../../lib/Lang/NativeTypes.s.dfy"
include "Constants.i.dfy"

module ReadWriteLockResources {
  import Ptrs
  import opened NativeTypes
  import opened Constants

  /*
   * We consider two bits of the status field, WriteLock and WriteBack.
   * To avoid confusion, I simply call them 'Write' and 'Back'.
   *
   * Write and Back. Of course, 'Write'
   * and 'Back' should be exclusive operations;
   * When both flags are set,
   * it should be interpreted as the 'Write' being
   * pending, with the 'Back' being in progress.
   */
  datatype Flag =
    | Free
    | Back
    | Write
    | Back_PendingWrite

  datatype Q =
    | FlagsField(ptr: Ptrs.Ptr, flags: Flag)
    | ReadRefCount(ptr: Ptrs.Ptr, t: int, refcount: uint8)

    | ReadPending(ptr: Ptrs.Ptr, t: int)
    | ReadObtained(ptr: Ptrs.Ptr, t: int)
    
    | BackObtained(ptr: Ptrs.Ptr)

    | WritePendingAwaitBack(ptr: Ptrs.Ptr)
    | WritePending(ptr: Ptrs.Ptr, visited: int)
    | WriteObtained(ptr: Ptrs.Ptr)

  datatype QStep =
    | TakeBackStep(ptr: Ptrs.Ptr)
    | TakeWrite(ptr: Ptrs.Ptr)
    | TakeWriteAwaitBack(ptr: Ptrs.Ptr)

  predicate TakeBack(a: multiset<Q>, b: multiset<Q>, ptr: Ptrs.Ptr)
  {
    && a == multiset{ FlagsField(ptr, Free) }
    && b == multiset{
      FlagsField(ptr, Back),
      BackObtained(ptr)
    }
  }

  predicate TakeWrite(a: multiset<Q>, b: multiset<Q>, ptr: Ptrs.Ptr)
  {
    && a == multiset{ FlagsField(ptr, Free) }
    && b == multiset{
      FlagsField(ptr, Write),
      WritePendingAwaitBack(ptr)
    }
  }

  predicate TakeWriteAwaitBack(a: multiset<Q>, b: multiset<Q>, ptr: Ptrs.Ptr)
  {
    && a == multiset{ FlagsField(ptr, Back) }
    && b == multiset{
      FlagsField(ptr, Back_PendingWrite),
      WritePendingAwaitBack(ptr)
    }
  }

  predicate TakeWriteFinishBack(a: multiset<Q>, b: multiset<Q>, ptr: Ptrs.Ptr, fl: Flag)
  {
    // The 'free' case cannot actually occur, but it's convenient to allow it.
    && (fl == Write || fl == Free)
    && a == multiset{
      FlagsField(ptr, fl),
      WritePendingAwaitBack(ptr)
    }
    && b == multiset{
      FlagsField(ptr, fl),
      WritePending(ptr, 0)
    }
  }

  predicate TakeWriteCheckReadZero(a: multiset<Q>, b: multiset<Q>, ptr: Ptrs.Ptr, idx: int)
  {
    && a == multiset{
      WritePending(ptr, idx),
      ReadRefCount(ptr, idx, 0) 
    }
    && b == multiset{
      WritePending(ptr, idx + 1),
      ReadRefCount(ptr, idx, 0) 
    }
  }

  predicate TakeWriteFinish(a: multiset<Q>, b: multiset<Q>, ptr: Ptrs.Ptr)
  {
    && a == multiset{
      WritePending(ptr, NThreads())
    }
    && b == multiset{
      WriteObtained(ptr)
    }
  }

  predicate TakeRead(a: multiset<Q>, b: multiset<Q>, ptr: Ptrs.Ptr, t: int, r: uint8)
  {
    && a == multiset{
      ReadRefCount(ptr, t, r)
    }
    && a == multiset{
      ReadRefCount(ptr, t, if r == 255 then 0 else r+1),
      ReadPending(ptr, t)
    }
  }

  predicate TakeReadFinish(a: multiset<Q>, b: multiset<Q>, ptr: Ptrs.Ptr, t: int, r: uint8, fl: Flag)
  {
    && (fl == Free || fl == Back)
    && a == multiset{
      ReadPending(ptr, t),
      FlagsField(ptr, fl)
    }
    && a == multiset{
      ReadObtained(ptr, t)
    }
  }

  predicate TakeReadBail(a: multiset<Q>, b: multiset<Q>, ptr: Ptrs.Ptr, t: int, r: uint8)
  {
    && a == multiset{
      ReadRefCount(ptr, t, r),
      ReadPending(ptr, t)
    }
    && b == multiset{
      ReadRefCount(ptr, t, if r == 0 then 255 else r-1)
    }
  }

  method transform_TakeBack(ptr: Ptrs.Ptr, linear s: Q)
  returns (linear t: Q, linear u: Q)
  requires s == FlagsField(ptr, Free)
  ensures t == FlagsField(ptr, Back)
  ensures u == BackObtained(ptr)

  method transform_TakeWrite(ptr: Ptrs.Ptr, linear s: Q)
  returns (linear t: Q, linear u: Q)
  requires s == FlagsField(ptr, Free)
  ensures t == FlagsField(ptr, Write)
  ensures u == WritePendingAwaitBack(ptr)

  method transform_TakeWriteAwaitBack(ptr: Ptrs.Ptr, linear s: Q)
  returns (linear t: Q, linear u: Q)
  requires s == FlagsField(ptr, Back)
  ensures t == FlagsField(ptr, Back_PendingWrite)
  ensures u == WritePendingAwaitBack(ptr)

  method transform_TakeWriteFinishBack(ptr: Ptrs.Ptr, fl: Flag, linear s1: Q, linear s2: Q)
  returns (linear t1: Q, linear t2: Q)
  requires fl == Write || fl == Free
  requires s1 == FlagsField(ptr, fl)
  requires s2 == WritePendingAwaitBack(ptr)
  ensures t1 == FlagsField(ptr, fl)
  ensures t2 == WritePending(ptr, 0)

  method transform_TakeWriteCheckReadZero(ptr: Ptrs.Ptr, idx: int, linear s1: Q, linear s2: Q)
  returns (linear t1: Q, linear t2: Q)
  requires s1 == ReadRefCount(ptr, idx, 0)
  requires s2 == WritePending(ptr, idx)
  ensures t1 == ReadRefCount(ptr, idx, 0)
  ensures t2 == WritePending(ptr, idx + 1)
}
