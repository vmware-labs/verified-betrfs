// Copyright 2018-2021 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, and University of Washington
// SPDX-License-Identifier: BSD-2-Clause

// Top layer of the write ahead log model
include "../lib/Base/FloatingSeq.s.dfy"

module TxnIfc {
  type Txn(!new,==)
  predicate Inv(t: Txn)
}

module Wal(txntype: TxnIfc) {
  import opened FloatingSeqMod
  type Txn = txntype.Txn

  // by making log track units of transactions, everything in the log is committed
  // this pushes the transaction layer down to the next layer

  datatype Wal = Wal(
    log: FloatingSeq<Txn>      // history of the write-ahead-log, log content in units of transactions
  ) {
    predicate WF()
    {
      && (forall i | log.ActiveRange(i) :: txntype.Inv(log.Get(i)) )
    }
  
    predicate isSubSet(other: Wal)
    requires WF()
    requires other.WF()
    {
      && log.Len() <= other.log.Len()
      && log == other.log.GetPrefix(log.Len())
    }

    predicate CanEndAt(end: nat)
    {
      || log.ActiveRange(end)
      || end == log.Len()
    }

    function Upto(end: nat) : FloatingSeq<Txn>
    requires WF()
    requires CanEndAt(end)
    {
      log.GetSuffix(end)
    }
  }

  predicate Init(wal: Wal)
  {
    && wal.WF()
    && wal == Wal(FloatingSeq(0, []))
  }

  // Q: if a txn spans over multiple pages, this might be too restricting, but maybe
  // the next layer can extrapolate that reading one value == reading the frame
  predicate Read(wal: Wal, wal': Wal, txnId: nat, result: Txn)
  {
    && wal.WF()
    && wal.log.ActiveRange(txnId)
    && wal' == wal
    && wal'.log.Get(txnId) == result
  }

  // write a txn is equivalent to commmitting a txn
  predicate Write(wal: Wal, wal': Wal, txn: Txn)
  {
    && wal.WF()
    && wal'.WF()
    && txntype.Inv(txn)
    && wal'.log == wal.log.Append([txn])
  }

  predicate Truncate(wal: Wal, wal': Wal, newStart: nat)
  {
    && wal.WF()
    && wal'.WF()
    && wal.CanEndAt(newStart)
    && wal'.log == wal.log.GetSuffix(newStart)
  }

  predicate Stutter(wal: Wal, wal': Wal)
  {
    && wal.WF()
    && wal == wal'
  }

  // TODO: uiop.
  datatype Step =
    | ReadStep(txnId: nat, result: Txn)
    | WriteStep(txn: Txn)
    | TruncateStep(new_start: nat)
    | StutterStep

  predicate NextStep(wal: Wal, wal': Wal, step:Step)
  {
    match step {
      case ReadStep(txnId, result) => Read(wal, wal', txnId, result)
      case WriteStep(txn) => Write(wal, wal', txn)
      case TruncateStep(new_start) => Truncate(wal, wal', new_start)
      case StutterStep => Stutter(wal, wal')
    }
  }

  predicate Next(wal: Wal, wal':Wal)
  {
    exists step :: NextStep(wal, wal', step)
  }

  predicate Inv(wal: Wal)
  {
    && wal.WF()
  }

  lemma InitImpliesInv(wal: Wal)
  {
  }

  lemma NextPreservesInv(wal: Wal, wal': Wal)
  {
  }
}

module WalPersistence(txntype: TxnIfc) {
  import opened WalMod = Wal(TxnIfc)

  type Wal = WalMod.Wal

  datatype States = States(
    ephemeral: Wal,
    persistent: Wal
  ) {
    predicate WF()
    {
      && ephemeral.WF()
      && persistent.WF()
    }
  }

  predicate Init(s: States)
  {
    && s.persistent.WF()
    && s.ephemeral == s.persistent
  }

  // at user level, sync can be represented synchronously
  // NOTE: need invariant to track the content difference between ephemeral and persistent
  // predicate Sync(s: States, s': States, upto: nat)
  // {
  //   // s' == s
  //   // TODO: check that persistent log is up to upto
  //   && s.WF()
  //   && s.ephemeral.CanEndAt(upto)
  //   && s'.ephemeral == s.ephemeral
  //   && s'.persistent.start == s.ephemeral.start
  //   && s'.persistent.log == s.ephemeral.Upto(upto)
  // }
  // A: split into req tf rsq
  // B: include TF in sync (), specify subset = upto
  // C: flush/durable isn't in the sync, pretend nothing's done until a TF step happens

  // captures the nondeterminism of partial flushed content
  predicate TransientFlush(s: States, s': States)
  {
    && s.WF()
    && s'.WF()
    && s'.ephemeral == s.ephemeral
    && s'.persistent.isSubSet(s.ephemeral)
    && s'.persistent.log.Len() >= s.persistent.log.Len() // background flush cannot shrink the log
  }

  // sync happens when enough transient flush is completed
  predicate Sync(s: States, s': States, upto: nat)
  {
    && s.WF()
    && s.ephemeral.CanEndAt(upto) // sync request is reflected in in-memory state already
    && s.persistent.CanEndAt(upto)
    && s' == s
  }
  
  predicate Crash(s: States, s': States)
  {
    && s.WF()
    && s'.WF()
    && s'.persistent == s.persistent
    && s'.ephemeral == s'.persistent 
  }

  // app level crashing refines to a stutter step
  predicate Stutter(s: States, s': States)
  {
    && s.WF()
    && s' == s
  }
}
