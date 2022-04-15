// Copyright 2018-2021 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, and University of Washington
// SPDX-License-Identifier: BSD-2-Clause

include "../CoordinationLayer/AbstractMap.i.dfy"

module PagedBetree
{
  import opened Options
  import opened KeyType
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
    | FreezeAsLabel(stampedBetree: StampedBetree)
    | InternalLabel()

  datatype Buffer = Buffer(filter: iset<Key>, mapp: map<Key, Message>)
  {
    function Query(key: Key) : Message
    {
      if key in filter && key in mapp
      then mapp[key]
      else Update(NopDelta())
    }

    function ApplyFilter(accept: iset<Key>) : Buffer
    {
      Buffer(filter * accept, mapp)
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

    function ApplyFilter(accept: iset<Key>) : BufferStack
    {
      BufferStack(seq(|buffers|, i requires 0<=i<|buffers| => buffers[i].ApplyFilter(accept)))
    }

    function PrependBufferStack(newBuffers: BufferStack) : BufferStack
    {
      BufferStack(newBuffers.buffers + this.buffers)
    }

    predicate Equivalent(other: BufferStack)
    {
      forall k | AnyKey(k) :: Query(k) == other.Query(k)
    }
  }

  // I'd prefer to instantiate TotalMapMod here, but rank_is_less_than doesn't
  // make it through the module refinement, so I can't prove decreases when I
  // recursively walk down the BetreeNode. So I do it manually instead.
  predicate AnyKey(key: Key) { true }
  predicate Total(keys: iset<Key>) {
    forall k | AnyKey(k) :: k in keys
  }
  function AllKeys() : (out: iset<Key>)
    ensures Total(out)
  {
    iset k | AnyKey(k)
  }
  datatype ChildMap = ChildMap(mapp: imap<Key, BetreeNode>) {
    predicate WF() {
      && Total(mapp.Keys)
      && (forall k | AnyKey(k) :: mapp[k].WF())
    }
  }
  
  function EmptyChildMap() : (out: ChildMap)
    ensures out.WF()
  {
    var mapp := imap key | AnyKey(key) :: Nil;
    ChildMap(mapp)
  }
  
  datatype Domain = DomainTODO  // TODO placeholder

  datatype BetreeNode = Nil | BetreeNode(
    domain: Domain,
    children: ChildMap,
    buffers: BufferStack)
  {
    predicate WF() {
      && (BetreeNode? ==> children.WF())
    }

    function PrependBufferStack(bufferStack: BufferStack) : (out: BetreeNode)
      requires WF()
      requires BetreeNode?
      ensures out.WF()
    {
      BetreeNode(DomainTODO, children, buffers.PrependBufferStack(bufferStack))
    }

    function Split(leftKeys: iset<Key>) : (out: BetreeNode)
      requires WF()
      requires BetreeNode?
      ensures out.WF()
    {
      assert children.WF(); // trigger
      var leftMapp := imap key | AnyKey(key) :: if key in leftKeys then children.mapp[key] else Nil;
      var leftNode := BetreeNode(DomainTODO, ChildMap(leftMapp), BufferStack([]));
      assert leftNode.WF();

      var rightMapp := imap key | AnyKey(key) :: if key in leftKeys then Nil else children.mapp[key];
      var rightNode := BetreeNode(DomainTODO, ChildMap(rightMapp), BufferStack([]));
      assert rightNode.WF();

      var mapp := imap key | AnyKey(key) :: if key in leftKeys then leftNode else rightNode;
      BetreeNode(DomainTODO, ChildMap(mapp), buffers)
    }

    function Promote() : BetreeNode
    {
      if Nil? then BetreeNode(DomainTODO, EmptyChildMap(), BufferStack([])) else this
    }

    function Flush(downKeys: iset<Key>) : (out: BetreeNode)
      requires WF()
      requires BetreeNode?
      ensures out.WF()
    {
      var keptBuffers := buffers.ApplyFilter(AllKeys() - downKeys);
      var movedBuffers := buffers.ApplyFilter(downKeys);
      assert children.WF();
      var outChildren := ChildMap(imap key | AnyKey(key)
        :: if key in downKeys
          then children.mapp[key].Promote().PrependBufferStack(movedBuffers)
          else children.mapp[key]);
      assert outChildren.WF();
      var out := BetreeNode(DomainTODO, outChildren, keptBuffers);
      assert out.WF();
      out
    }

    predicate EquivalentBufferCompaction(other: BetreeNode)
    {
      && WF()
      && other.WF()
      && Promote().buffers.Equivalent(other.Promote().buffers)
      // Can only make a local change; entirety of children subtrees are identical.
      && Promote().children == other.Promote().children
    }
  }

  function EmptyRoot() : (out: BetreeNode)
    ensures out.WF()
  {
    BetreeNode(DomainTODO, EmptyChildMap(), BufferStack([])
    )
  }

  datatype QueryReceiptLine = QueryReceiptLine(
    node: BetreeNode,
    result: Message)
  {
    predicate WF()
    {
      && node.BetreeNode?
      && result.Define?
    }
  }

  datatype QueryReceipt = QueryReceipt(
    key: Key,
    root: BetreeNode,
    lines: seq<QueryReceiptLine>)
  {
    function ResultAt(i: nat) : Message
      requires i <= |lines|
    {
      if i<|lines| then lines[i].result else Define(DefaultValue())
    }

    predicate AllLinesWF()
    {
      && (forall i:nat | i < |lines| :: lines[i].WF())
    }

    predicate LinkedAt(i: nat)
      requires AllLinesWF()
      requires i < |lines|
    {
      lines[i].result == Merge(lines[i].node.buffers.Query(key), ResultAt(i+1))
    }

    predicate Valid()
    {
      && (if root.Nil? then |lines| == 0 else 0 < |lines| && lines[0].node == root)
      && AllLinesWF()
      && (forall i:nat | i < |lines| :: LinkedAt(i))
    }

    function Result() : Message
    {
      ResultAt(0)
    }

    predicate ValidFor(root: BetreeNode, key: Key)
    {
      && Valid()
      && this.root == root
      && this.key == key
    }
  }

  // Constructive evidence that a Valid QueryReceipt exists for every key.
  function BuildQueryReceipt(node: BetreeNode, key: Key) : (out: QueryReceipt)
    requires node.WF()
    ensures out.key == key
    ensures out.Valid()
    decreases node
  {
    if node.Nil?
    then QueryReceipt(key, node, [])
    else
      assert node.children.WF();  // trigger
      var childReceipt := BuildQueryReceipt(node.children.mapp[key], key);
      var thisMessage := node.buffers.Query(key);
      var topLine := QueryReceiptLine(node, Merge(thisMessage, childReceipt.Result()));
      var receipt := QueryReceipt(key, node, [topLine] + childReceipt.lines);
      assert receipt.LinkedAt(0);
      assert forall i | 0<i<|receipt.lines| :: childReceipt.LinkedAt(i-1) && receipt.LinkedAt(i); // trigger Valid
      receipt
  }

  datatype StampedBetree = StampedBetree(
    root: BetreeNode,
    seqEnd: LSN)
  {
    predicate WF()
    {
      root.WF()
    }
    
    function I() : StampedMap
      requires WF()
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

    function Query(key: Key) : Message
    {
      if key in mapp then mapp[key] else Update(NopDelta())
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
    predicate WF() {
      && stampedBetree.WF()
    }
  }

  predicate Query(v: Variables, v': Variables, lbl: TransitionLabel, receipt: QueryReceipt)
  {
    && lbl.QueryLabel?
    && lbl.endLsn == v.stampedBetree.seqEnd
    && receipt.ValidFor(v.stampedBetree.root, lbl.key)
    && Define(lbl.value) == Merge(v.memtable.Query(lbl.key), receipt.Result())
  }

  predicate Put(v: Variables, v': Variables, lbl: TransitionLabel)
  {
    && lbl.PutLabel?
    && lbl.puts.WF()
    && lbl.puts.seqStart == v.memtable.seqEnd
    && v' == v.(
        memtable := v.memtable.ApplyPuts(lbl.puts)
      )
  }

  predicate QueryEndLsn(v: Variables, v': Variables, lbl: TransitionLabel)
  {
    && lbl.QueryEndLsnLabel?
    && lbl.endLsn == v.stampedBetree.seqEnd
  }

  predicate FreezeAs(v: Variables, v': Variables, lbl: TransitionLabel, stampedBetree: StampedBetree)
  {
    && lbl.FreezeAsLabel?
    && stampedBetree == v.stampedBetree
    && v' == v
  }

  predicate InternalFlushMemtable(v: Variables, v': Variables, lbl: TransitionLabel)
  {
    && v.WF()
    && var newBuffer := Buffer(AllKeys(), v.memtable.mapp);
    && var rootBase := if v.stampedBetree.root.Nil? then EmptyRoot() else v.stampedBetree.root;
    && v' == v.(
        memtable := EmptyMemtable(v.memtable.seqEnd),
        stampedBetree := StampedBetree(rootBase.PrependBufferStack(BufferStack([newBuffer])), v.memtable.seqEnd)
      )
  }
  
  datatype Path = Path(node: BetreeNode, key: Key, depth: nat)
  {
    function Subpath() : (out: Path)
      requires 0 < depth
      requires node.WF()
      requires node.BetreeNode?
    {
      assert node.children.WF();
      Path(node.children.mapp[key], key, depth-1)
    }

    predicate Valid()
      decreases depth
    {
      && node.WF()
      && node.BetreeNode?
      //&& (0 < depth ==> Path(node.children[key], key, depth-1).Valid())
      && (0 < depth ==> Subpath().Valid())
    }

    function Node() : (out: BetreeNode)
      requires Valid()
      ensures out.WF()
      ensures out.BetreeNode?
      decreases depth
    {
      if 0 == depth
      then node
      else Subpath().Node()
    }

    function Substitute(replacement: BetreeNode) : (out: BetreeNode)
      requires Valid()
      decreases depth
    {
      if 0 == depth
      then replacement
      else Subpath().Substitute(replacement)
    }
  }

  predicate InternalSplit(v: Variables, v': Variables, lbl: TransitionLabel, step: Step)
  {
    && step.InternalSplitStep?
    && step.path.Valid()
    && step.path.node == v.stampedBetree.root
    && v' == v.(
        stampedBetree := v.stampedBetree.(
          root := step.path.Substitute(step.path.Node().Split(step.leftKeys))
        )
      )
  }

  predicate InternalFlush(v: Variables, v': Variables, lbl: TransitionLabel, step: Step)
  {
    && step.InternalFlushStep?
    && step.path.Valid()
    && step.path.node == v.stampedBetree.root
    && v' == v.(
        stampedBetree := v.stampedBetree.(
          root := step.path.Substitute(step.path.Node().Flush(step.downKeys))
        )
      )
  }

  // NB we tell you exactly how to Split and Flush, but leave lots of
  // nondetermistic freedom in the description of Compact.
  predicate InternalCompact(v: Variables, v': Variables, lbl: TransitionLabel, step: Step)
  {
    && step.InternalCompactStep?
    && step.path.Valid()
    && step.path.node == v.stampedBetree.root
    && step.compactedNode.WF()
    && step.path.Node().EquivalentBufferCompaction(step.compactedNode)
    && v' == v.(
        stampedBetree := v.stampedBetree.(
          root := step.path.Substitute(step.compactedNode)
        )
      )
  }

  // public:

  predicate Init(v: Variables, stampedBetree: StampedBetree)
  {
    v == Variables(EmptyMemtable(stampedBetree.seqEnd), stampedBetree)
  }

  datatype Step =
      QueryStep(receipt: QueryReceipt)
    | PutStep()
    | QueryEndLsnStep()
    | FreezeAsStep(stampedBetree: StampedBetree)
    | InternalSplitStep(path: Path, leftKeys: iset<Key>)
    | InternalFlushStep(path: Path, downKeys: iset<Key>)
    | InternalCompactStep(path: Path, compactedNode: BetreeNode)

  predicate NextStep(v: Variables, v': Variables, lbl: TransitionLabel, step: Step)
  {
    match step {
      case QueryStep(receipt) => Query(v, v', lbl, receipt)
      case PutStep() => Put(v, v', lbl)
      case QueryEndLsnStep() => QueryEndLsn(v, v', lbl)
      case FreezeAsStep(stampedBetree) => FreezeAs(v, v', lbl, stampedBetree)
      case InternalSplitStep(_, _) => InternalSplit(v, v', lbl, step)
      case InternalFlushStep(_, _) => InternalFlush(v, v', lbl, step)
      case InternalCompactStep(_, _) => InternalCompact(v, v', lbl, step)
    }
  }

  predicate Next(v: Variables, v': Variables, lbl: TransitionLabel) {
    exists step: Step :: NextStep(v, v', lbl, step)
  }
}
