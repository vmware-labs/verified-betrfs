// Copyright 2018-2021 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, and University of Washington
// SPDX-License-Identifier: BSD-2-Clause

include "../CoordinationLayer/AbstractMap.i.dfy"

module ChildMapMod refines TotalMapMod {
  import opened Options
  import opened KeyType

  type NodeType(!new,==)   // placeholder for Betree down where we define it.

  type K = Key
  type V = Option<NodeType>
  predicate TerminalValue(v: V) { true }
  function DefaultV() : V { None }

  type ChildMap = TotalMap
}

module PagedBetree
  refines ChildMapMod // refinement here because that's the only way to supply ChildMapMod.NodeType
{
  import opened StampedMapMod
  import TotalKMMapMod
  import opened ValueMessage
  import opened MsgHistoryMod
  import opened LSNMod
  import opened Sequences

  datatype TransitionLabel =
      QueryLabel(endLsn: LSN, key: Key, value: Value)
    | PutLabel(puts: MsgHistory)
    | QueryEndLsnLabel(endLsn: LSN)
    | FreezeAsLabel(stampedMap: StampedMap)
    | InternalLabel()

  datatype Buffer = Buffer(filter: set<Key>, mapp: map<Key, Message>)
  {
    function Query(key: Key) : Message
    {
      if key in filter && key in mapp
      then mapp[key]
      else Update(NopDelta())
    }
  }

  // buffers[0] is the newest data
  datatype BufferStack = BufferStack(buffers: seq<Buffer>)
  {
    function QueryUpTo(key: Key, count: nat) : Message
      requires count <= |buffers|
    {
      if count == 0 then Update(NopDelta())
      else Merge(QueryUpTo(key, count-1), buffers[count-1].Query(key))
    }

    function Query(key: Key) : Message
    {
      QueryUpTo(key, |buffers|)
    }
  }

  type NodeType = BetreeNode  // Tell ChildMapMod about BetreeNodes

  datatype BetreeNode = BetreeNode(
    domain: set<Key>,
    children: ChildMap,
    sillychildren: imap<Key, Option<BetreeNode>>,
    buffers: BufferStack)
  {
    predicate WF() {
      && true
    }
  }

  datatype QueryReceiptLine = QueryReceiptLine(
    node: BetreeNode,
    result: Message)
  {
    predicate WF()
    {
      result.Define?
    }
  }

  datatype QueryReceipt = QueryReceipt(
    key: Key,
    root: Option<BetreeNode>,
    lines: seq<QueryReceiptLine>)
  {
    function ResultAt(i: nat) : Message
      requires i <= |lines|
    {
      if i<|lines| then lines[i].result else Define(DefaultValue())
    }

    predicate LinkedAt(i: nat)
      requires i < |lines|
    {
      lines[i].result == Merge(lines[i].node.buffers.Query(key), ResultAt(i+1))
    }

    predicate Valid()
    {
      && (if root.None? then |lines| == 0 else 0 < |lines| && lines[0].node == root.value)
      && (forall i:nat | i < |lines| :: lines[i].WF())
      && (forall i:nat | i < |lines| :: LinkedAt(i))
    }

    function Result() : Message
    {
      ResultAt(0)
    }
  }

  // Constructive evidence that a Valid QueryReceipt exists for every key.
  function BuildQueryReceipt(node: Option<BetreeNode>, key: Key) : (out: QueryReceipt)
    ensures out.key == key
    ensures out.Valid()
    decreases node
  {
    if node.None?
    then QueryReceipt(key, node, [])
    else
      assert AnyKey(key);
      //var childReceipt := BuildQueryReceipt(node.value.children[key], key);
      assume key in node.value.sillychildren;
      var childReceipt := BuildQueryReceipt(node.value.sillychildren[key], key);
      var thisMessage := node.value.buffers.Query(key);
      var topLine := QueryReceiptLine(node.value, Merge(thisMessage, childReceipt.Result()));
      var receipt := QueryReceipt(key, node, [topLine] + childReceipt.lines);
      assert receipt.LinkedAt(0);
      assume receipt.Valid();
      receipt
  }

  datatype StampedBetree = StampedBetree(
    root: Option<BetreeNode>,
    seqEnd: LSN)
  {
    function I() : StampedMap
    {
      var mi := imap key | AnyKey(key) :: BuildQueryReceipt(root, key).Result();
      assert TotalKMMapMod.TotalMapIsFull(mi);
      StampedMap(mi, seqEnd)
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
      requires puts.WF()
      requires puts.seqStart == seqEnd
      decreases puts.Len()
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
    && lbl.puts.WF()
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
