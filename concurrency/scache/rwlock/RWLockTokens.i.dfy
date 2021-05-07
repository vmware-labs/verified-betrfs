include "RWLock.dfy"

module RWLockSimpleExtPCM refines SimpleExtPCM {
  import SE = RWLockExt
}

module RWLockExtToken refines SimpleExtToken {
  import SEPCM = RWLockSimpleExtPCM
  import opened RWLockExt
  import opened Options

  glinear method perform_TakeWriteback(glinear central: Token)
  returns (glinear central': Token, wb_handle': Token)
  requires central.get().central.CentralState?
  requires central.get().central.flag == Available
  requires central.get() == CentralHandle(central.get().central)
  ensures central'.get() == CentralHandle(central.get().central.(flag := Writeback))
  ensures wb_handle'.get() == WritebackHandle(WritebackObtained(central.get().central.stored_value))
  ensures wb_handle'.loc() == central'.loc() == central.loc()
  {
    ghost var a := CentralHandle(central.get().central.(flag := Writeback));
    ghost var b := WritebackHandle(WritebackObtained(central.get().central.stored_value));
  }

  glinear method perform_ReleaseWriteback(m: M, m': M)
  {
    && m.central.CentralState?
    && m.writeback.WritebackObtained?

    && m == dot(
      CentralHandle(m.central),
      WritebackHandle(m.writeback)
    )

    && (m.central.flag == Writeback ==>
      m' == CentralHandle(m.central.(flag := Available))
    )
    && (m.central.flag == Writeback_PendingExcLock ==>
      m' == CentralHandle(m.central.(flag := PendingExcLock))
    )
  }

  glinear method perform_ThreadlessExc(m: M, m': M)
  {
    && m.central.CentralState?
    && (m.central.flag == Available || m.central.flag == Writeback)

    && m == CentralHandle(m.central)
    && m' == dot(
      CentralHandle(m.central.(flag := 
          if m.central.flag == Available then PendingExcLock else Writeback_PendingExcLock)),
      ExcHandle(ExcPendingAwaitWriteback(-1, m.central.stored_value))
    )
  }

  glinear method perform_SharedToExc(m: M, m': M, ss: SharedState)
  {
    && m.central.CentralState?
    && (m.central.flag == Available || m.central.flag == Writeback)
    && ss.SharedObtained?

    && m == dot(
      CentralHandle(m.central),
      SharedHandle(ss)
    )
    && m' == dot(
      CentralHandle(m.central.(flag := 
          if m.central.flag == Available then PendingExcLock else Writeback_PendingExcLock)),
      ExcHandle(ExcPendingAwaitWriteback(ss.t, ss.b))
    )
  }

  glinear method perform_TakeExcLockFinishWriteback(m: M, m': M, clean: bool)
  {
    && m.central.CentralState?
    && m.exc.ExcPendingAwaitWriteback?
    && m.central.flag != Writeback && m.central.flag != Writeback_PendingExcLock
    && m == dot(
      CentralHandle(m.central),
      ExcHandle(m.exc)
    )
    && m' == dot(
      CentralHandle(m.central.(flag :=
        if clean then ExcLock_Clean else ExcLock_Dirty)),
      ExcHandle(ExcPending(m.exc.t, 0, clean, m.exc.b))
    )
  }

  glinear method perform_TakeExcLockCheckRefCount(m: M, m': M)
  {
    && m.exc.ExcPending?
    && m.exc.visited in m.refCounts
    && 0 <= m.exc.visited < NUM_THREADS

    && var expected_rc := (if m.exc.visited == m.exc.t then 1 else 0);

    && m == dot(
      ExcHandle(m.exc),
      RefCount(m.exc.visited, expected_rc)
    )
    && m' == dot(
      ExcHandle(m.exc.(visited := m.exc.visited + 1)),
      RefCount(m.exc.visited, expected_rc)
    )
  }

  glinear method perform_Withdraw_TakeExcLockFinish(m: M, m': M, b: Base.M, b': Base.M)
  {
    && m.exc.ExcPending?
    && m.exc.visited == NUM_THREADS
    && m == ExcHandle(m.exc)
    && m' == ExcHandle(ExcObtained(m.exc.t, m.exc.clean))
    && b == Base.unit()
    && b' == m.exc.b
  }

  glinear method perform_Deposit_DowngradeExcLoc(m: M, m': M, b: Base.M, b': Base.M)
  {
    && m.exc.ExcObtained?
    && m.central.CentralState?
    && 0 <= m.exc.t < NUM_THREADS
    && m == dot(
      CentralHandle(m.central),
      ExcHandle(m.exc)
    )
    && m' == dot(
      CentralHandle(m.central
        .(flag := Available)
        .(stored_value := b)
      ),
      SharedHandle(SharedObtained(m.exc.t, b))
    )
    && b' == Base.unit()
  }

  glinear method perform_Withdraw_Alloc(m: M, m': M, b: Base.M, b': Base.M)
  {
    && m.central.CentralState?
    && m.central.flag == Unmapped
    && m == CentralHandle(m.central)

    && m' == dot(
      CentralHandle(m.central.(flag := Reading_ExcLock)),
      ReadHandle(ReadPending)
    )

    && b == Base.unit()
    && b' == m.central.stored_value
  }

  glinear method perform_ReadingIncCount(m: M, m': M, t: int)
  {
    && t in m.refCounts
    && 0 <= t < NUM_THREADS
    && m == dot(
      ReadHandle(ReadPending),
      RefCount(t, m.refCounts[t])
    )
    && m' == dot(
      ReadHandle(ReadPendingCounted(t)),
      RefCount(t, m.refCounts[t] + 1)
    )
  }

  glinear method perform_ObtainReading(m: M, m': M)
  {
    && m.central.CentralState?
    && m.read.ReadPendingCounted?
    && m == dot(
      CentralHandle(m.central),
      ReadHandle(m.read)
    )
    && m' == dot(
      CentralHandle(m.central.(flag := Reading)),
      ReadHandle(ReadObtained(m.read.t))
    )
  }


  glinear method perform_Deposit_ReadingToShared(m: M, m': M, b: Base.M, b': Base.M)
  {
    && m.central.CentralState?
    && m.read.ReadObtained?
    && m == dot(
      CentralHandle(m.central),
      ReadHandle(m.read)
    )
    && m' == dot(
      CentralHandle(m.central.(flag := Available).(stored_value := b)),
      SharedHandle(SharedObtained(m.read.t, b))
    )
    && b' == Base.unit()
  }

  glinear method perform_SharedIncCount(m: M, m': M, t: int)
  {
    && 0 <= t < NUM_THREADS
    && t in m.refCounts
    && m == RefCount(t, m.refCounts[t])
    && m' == dot(
      RefCount(t, m.refCounts[t] + 1),
      SharedHandle(SharedPending(t))
    )
  }

  glinear method perform_SharedDecCountPending(m: M, m': M, t: int)
  {
    && 0 <= t < NUM_THREADS
    && t in m.refCounts
    && m == dot(
      RefCount(t, m.refCounts[t]),
      SharedHandle(SharedPending(t))
    )
    && (m.refCounts[t] >= 1 ==>
      m' == RefCount(t, m.refCounts[t] - 1)
    )
  }

  glinear method perform_SharedDecCountObtained(m: M, m': M, t: int, b: Base.M)
  {
    && 0 <= t < NUM_THREADS
    && t in m.refCounts
    && m == dot(
      RefCount(t, m.refCounts[t]),
      SharedHandle(SharedObtained(t, b))
    )
    && (m.refCounts[t] >= 1 ==>
      m' == RefCount(t, m.refCounts[t] - 1)
    )
  }

  glinear method perform_SharedCheckExc(m: M, m': M, t: int)
  {
    && 0 <= t < NUM_THREADS
    && m.central.CentralState?
    && (m.central.flag == Available
        || m.central.flag == Writeback
        || m.central.flag == Reading)
    && m == dot(
      CentralHandle(m.central),
      SharedHandle(SharedPending(t))
    )
    && m' == dot(
      CentralHandle(m.central),
      SharedHandle(SharedPending2(t))
    )
  }

  glinear method perform_SharedCheckReading(m: M, m': M, t: int)
  {
    && 0 <= t < NUM_THREADS
    && m.central.CentralState?
    && m.central.flag != Reading
    && m.central.flag != Reading_ExcLock
    && m == dot(
      CentralHandle(m.central),
      SharedHandle(SharedPending2(t))
    )
    && m' == dot(
      CentralHandle(m.central),
      SharedHandle(SharedObtained(t, m.central.stored_value))
    )
  }

  glinear method perform_Deposit_Unmap(m: M, m': M, b: Base.M, b': Base.M)
  {
    && m.exc.ExcObtained?
    && m.exc.t == -1
    && m.central.CentralState?
    && m == dot(
      CentralHandle(m.central),
      ExcHandle(m.exc)
    )
    && m' == CentralHandle(
      m.central.(flag := Unmapped).(stored_value := b)
    )
    && b' == Base.unit()
  }

  glinear method perform_AbandonExcPending(m: M, m': M)
  {
    && m.exc.ExcPending?
    && m.exc.t == -1
    && m.central.CentralState?
    && m == dot(
      CentralHandle(m.central),
      ExcHandle(m.exc)
    )
    && m' == CentralHandle(m.central.(flag := Available))
  }

  glinear method perform_Deposit_AbandonReadPending(m: M, m': M, b: Base.M, b': Base.M)
  {
    && m.read.ReadPending?
    && m.central.CentralState?
    && m == dot(
      CentralHandle(m.central),
      ReadHandle(m.read)
    )
    && m' == CentralHandle(m.central.(flag := Unmapped).(stored_value := b))
    && b' == Base.unit()
  }
}
