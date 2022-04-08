// Copyright 2018-2021 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, and University of Washington
// SPDX-License-Identifier: BSD-2-Clause

include "../CoordinationLayer/AbstractMap.i.dfy"

module PagedBetree {
  import opened Options
  import opened ValueMessage
  import opened KeyType
  import opened MsgHistoryMod
  import opened LSNMod
  import opened Sequences
  import opened MapLabels

  datatype Buffer = Buffer(filter: set<Key>, mapp: map<Key, Message>)
  {
    function Query(key: Key) : Message
    {
      if key in filter && key in mapp
      then mapp[key]
      else NopDelta()
    }
  }

  // buffers[0] is the newest data
  datatype BufferStack = BufferStack(buffers: seq<Buffer>)
  {
    function QueryUpTo(key: Key, count: nat) : Message
      requires count <= |buffers|
    {
      if count == 0 then NopDelta()
      else CombineDeltas(Query(key, count-1), buffers[count-1].Query(key))
    }

    function Query(key: Key) : Message
    {
      QueryUpTo(key, |buffers|)
    }
  }

  datatype BetreeNode = BetreeNode(
    domain: set<Key>,
    children: imap<Key, Option<BetreeNode>>,
    buffers: BufferStack)
  {
    function Query(key: Key) : 
  }

  datatype StampedBetree = StampedBetree(
    root: Option<BetreeNode>,
    seqEnd: LSN)

  datatype QueryReceiptLine = QueryReceiptLine(
    node: BetreeNode,
    result: Mesage)
  {
  }

  datatype QueryReceipt = QueryReceipt(
    key: Key,
    value: Value,
    root: Option<BetreeNode>,
    lines: seq<QueryReceiptLine>)
  {
    predicate Valid()
    {
      && (if root.None? then |lines| == 0 else Last(lines).node == root.value)
      && value == (if |lines| == 0 then DefaultMessage() else Last(lines).result)
    }
  }

    
  datatype Memtable = Memtable(mapp: map<Key, Message>, seqEnd: LSN)
  {
    function ApplyPut(km: KeyedMessage) : Memtable
    {
      var oldMessage := if km.key in mapp then mapp[km.key] else Update(NopDelta());
      Memtable(mapp[km.key := Merge(km.message, oldMessage)], seqEnd+1)
    }

    function ApplyPuts(puts: MsgHistory) : Memtable
      requires puts.seqStart == seqEnd
    {
      if puts.IsEmpty() then this
      else ApplyPuts(puts.DiscardRecent(puts.seqEnd-1)).ApplyPut(puts.msgs[puts.seqEnd-1])
    }
  }

  function EmptyMemtable(lsn: LSN) : Memtable
  {
    Memtable(map[], lsn)
  }

  datatype Variables = Variables(
    memtable: Memtable,
    stampedBetree: StampedBetree)
  {
  }

  predicate Query(v: Variables, v': Variables, lbl: TransitionLabel)
  {
    true
  }

  predicate Put(v: Variables, v': Variables, lbl: TransitionLabel)
  {
    && lbl.PutLabel?
    && lbl.puts.seqStart == v.memtable.seqEnd
    && v' == v.(memtable := v.memtable.ApplyPuts(lbl.puts))
  }

  predicate QueryEndLsn(v: Variables, v': Variables, lbl: TransitionLabel)
  {
    true
  }

  predicate FreezeAs(v: Variables, v': Variables, lbl: TransitionLabel, stampedBetree: StampedBetree)
  {
    && lbl.FreezeAsLabel?
    && stampedBetree.I() == lbl.stampedMap
    && stampedBetree == v.stampedBetree
    && v' == v
  }

  predicate InternalSplit(v: Variables, v': Variables, lbl: TransitionLabel)
  {
    true
  }

  predicate InternalFlush(v: Variables, v': Variables, lbl: TransitionLabel)
  {
    true
  }

  predicate InternalCompact(v: Variables, v': Variables, lbl: TransitionLabel)
  {
    true
  }

  // public:

  predicate Init(v: Variables, stampedBetree: StampedBetree)
  {
    v == Variables(EmptyMemtable(stampedBetree.seqEnd), stampedBetree)
  }

  datatype Step =
      QueryStep()
    | PutStep()
    | QueryEndLsnStep()
    | FreezeAsStep(stampedBetree: StampedBetree)
    | InternalSplitStep()
    | InternalFlushStep()
    | InternalCompactStep()

  predicate NextStep(v: Variables, v': Variables, lbl: TransitionLabel, step: Step)
  {
    match step {
      case QueryStep() => Query(v, v', lbl)
      case PutStep() => Put(v, v', lbl)
      case QueryEndLsnStep() => QueryEndLsn(v, v', lbl)
      case FreezeAsStep(stampedBetree) => FreezeAs(v, v', lbl, stampedBetree)
      case InternalSplitStep() => InternalSplit(v, v', lbl)
      case InternalFlushStep() => InternalFlush(v, v', lbl)
      case InternalCompactStep() => InternalCompact(v, v', lbl)
    }
  }

  predicate Next(v: Variables, v': Variables, lbl: TransitionLabel) {
    exists step: Step :: NextStep(v, v', lbl, step)
  }
}
