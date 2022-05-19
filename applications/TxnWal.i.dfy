// Copyright 2018-2021 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, and University of Washington
// SPDX-License-Identifier: BSD-2-Clause
include "../lib/Base/SequencesLite.s.dfy"
include "../lib/Base/FloatingSeq.s.dfy"

module OpIfc {
  type Op(!new,==)

  predicate Inv(op: Op)

  predicate SeqInv(ops: seq<Op>)
  {
    && (forall op | op in ops :: Inv(op))
  }

  function CheckSum(ops: seq<Op>) : (chksum: nat)
  requires SeqInv(ops)

  lemma CheckSumUnique(ops1: seq<Op>, ops2: seq<Op>)
  requires SeqInv(ops1)
  requires SeqInv(ops2)
  ensures CheckSum(ops1) == CheckSum(ops2) <==> ops1 == ops2 
}

module Txn(optype: OpIfc) {
  type Op = optype.Op

  // this is a place where we want to represent transactions as ops
  // and then we can have a paged layer that knows the size of ops

  datatype Txn = 
    | Ongoing(ops: seq<Op>)
    | Committed(ops: seq<Op>, chksum: nat)
  {
    function AppendTxn(t: Txn) : Txn
    // requires t.Ongoing?
    {
      Ongoing(ops + t.ops)
    }

    function ToCommitted() : Txn
    requires optype.SeqInv(ops)
    {
      var chksum := optype.CheckSum(ops);
      Committed(ops, chksum)
    }
  }

//   // Txn(ops: seq<Op>)
//     // | NestedTxns(txns: seq<Txn>) // TODO: add in nested txn to support savepoints

  predicate Inv(t: Txn) {
    && optype.SeqInv(t.ops)
    // TODO: add chksum valid condition?
  }
}

module TxnWal(optype: OpIfc) {
  import TxnMod = Txn(optype)

  import opened SequencesLite
  import opened FloatingSeqMod

  type Txn = TxnMod.Txn

  // endmark is exclusive
  datatype RState = RState(id: nat, endmark: nat) {
    static function min(a: RState, b: RState) : RState
    {
      if a.endmark < b.endmark then a else b
    }

    static function min_reader(rstates: seq<RState>) : RState
    requires |rstates| > 0
    {
      if |rstates| == 1
      then rstates[0]
      else min(min_reader(DropLast(rstates)), Last(rstates))
    }
  }

  datatype Wal = Wal(
    log: FloatingSeq<Txn>,        // history of the write-ahead-log, log content in units of transactions
    readers: seq<RState>          // seq of readers and their states, used for deciding valid truncation
  ) {
    predicate WF()
    {
      && (forall i | log.ActiveRange(i) :: TxnMod.Inv(log.Get(i)))
      && (forall r | r in readers :: r.endmark <= log.Len())
    }

    predicate NewlyTruncated()
    {
      || log.Len() == 0
      || !log.ActiveRange(log.Len()-1)
    }

    predicate HasReader()
    {
      && |readers| > 0
    }

    // predicate IsSubSet()
    // {
//       && true
//       // in a world with ongoing txn, we don't want to allow for ongoing with ongoing
//       // && start == other.start
//       // && |log| <= |other.log|
//       // && log == other.log[..|log|]
    // }

    function Endmark() : nat
    requires WF()
    {
      if NewlyTruncated() || log.Last().Committed?      
      then log.Len()
      else log.Len() - 1
    }

    // TODO: implement
    function RemoveReader(r: RState) : seq<RState>
    requires WF()
    requires r in readers
    {
      readers
    }
  }

  predicate Init(wal: Wal)
  {
    && wal.WF()
    && wal == Wal(FloatingSeq(0, []), [])
  }

  // Q: there needs to be a thread tying the reader in SetReadEnd with reader at Read
  predicate SetReadEnd(wal: Wal, wal': Wal, reader: RState)
  {
    && wal.WF()
    && wal'.WF()
    && reader.endmark == wal.Endmark()
    // new state
    && wal'.log == wal.log
    && wal'.readers == wal.readers + [ reader ]
  }

  // Can only read committed txn that's still in the log 
  predicate Read(wal: Wal, wal': Wal, txnId: nat, reader: RState, result: Txn)
  {
    && wal.WF()
    && wal'.WF()
    // enabling conditions for read
    && reader in wal.readers   // questionable
    && txnId < reader.endmark  // questionable
    && wal.log.ActiveRange(txnId)
    && wal.log.Get(txnId).Committed?
    // state unchanged
    && result == wal.log.Get(txnId)
    && wal'.log == wal.log
    && wal'.readers == wal.RemoveReader(reader)
  }

  predicate BeginTxn(wal: Wal, wal': Wal)
  {
    && wal.WF()
    && wal'.WF()
    && (!wal.NewlyTruncated() ==> wal.log.Last().Committed?)
    // new state
    && wal'.log == wal.log.Append([Txn.Ongoing([])])
    && wal'.readers == wal.readers
  }

  predicate AppendTxn(wal: Wal, wal': Wal, t: Txn)
  {
    && wal.WF()
    && wal'.WF()
    // && t.Ongoing?
    && TxnMod.Inv(t)
    && !wal.NewlyTruncated()
    && wal.log.Last().Ongoing?
    // new state
    && var newtxn := wal.log.Last().AppendTxn(t);
    && wal'.log == wal.log.DropLast().Append([newtxn])
    && wal'.readers == wal.readers
  }

  predicate EndTxn(wal: Wal, wal': Wal, chksum: nat)
  {
    && wal.WF()
    && wal'.WF()
    && !wal.NewlyTruncated()
    && wal.log.Last().Ongoing?
    && var newtxn := wal.log.Last().ToCommitted();
    && newtxn.chksum == chksum
    // new state
    && wal'.log == wal.log.DropLast().Append([newtxn])    
    && wal'.readers == wal.readers
  }

  predicate Truncate(wal: Wal, wal': Wal, newStart: nat)
  {
    && wal.WF()
    && wal'.WF()
    && (wal.log.ActiveRange(newStart) || newStart == wal.log.Len())
    // reader condition guarantees endmark ends at committed entries
    && (wal.HasReader() ==> newStart < RState.min_reader(wal.readers).endmark)
    && (!wal.HasReader() ==> newStart <= wal.Endmark())
    // new state
    && wal'.log == wal.log.GetSuffix(newStart)
    && wal'.readers == wal.readers
  }

  predicate Stutter(wal: Wal, wal': Wal)
  {
    && wal.WF()
    && wal == wal'
  }
}

module TxnWalPersistence(optype: OpIfc) {
  import opened TxnWalMod = TxnWal(OpIfc)

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

  // captures the nondeterminism of partial flushed content
  // predicate TransientFlush(s: States, s': States)
  // {
  //   && s.WF()
  //   && s'.WF()
  //   && s'.ephemeral == s.ephemeral
  //   // && s'.persistent.isSubSet(s.ephemeral)
  // }

  // // sync happens when enough transient flush is completed
  // predicate Sync(s: States, s': States, upto: nat)
  // {
  //   && s.WF()
  //   && s' == s
  //   && s'.ephemeral.CanEndAt(upto) // sync request is reflected in in-memory state already
  //   && s'.persistent.log == s.ephemeral.Upto(upto) // Q: precise or subset? 
  //   // && s'.persistent.CanEndAt(upto)
  //   // && s'.persistent.isSubSet(s'.ephemeral)
  // }
  
  // predicate Crash(s: States, s': States)
  // {
  //   && s.WF()
  //   && s'.WF()
  //   && s'.persistent == s.persistent
  //   && s'.ephemeral == s'.persistent 
  // }

  // // app level crashing refines to a stutter step
  // predicate Stutter(s: States, s': States)
  // {
  //   && s.WF()
  //   && s' == s
  // }
}
