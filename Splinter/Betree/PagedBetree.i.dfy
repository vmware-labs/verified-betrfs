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
  
  function ConstantChildMap(target: BetreeNode) : (out: ChildMap)
    requires target.WF()
    ensures out.WF()
  {
    var mapp := imap key | AnyKey(key) :: target;
    ChildMap(mapp)
  }
  
  function EmptyChildMap() : (out: ChildMap)
  {
    ConstantChildMap(Nil)
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

    function ApplyFilter(filter: iset<Key>) : (out: BetreeNode)
      requires WF()
      ensures out.WF()
    {
      if Nil? then Nil else
      var out := BetreeNode(DomainTODO, children, buffers.ApplyFilter(filter));
      out
    }

    // TODO(jonh): Split shouldn't also Grow; that's a separate operation.
    function Split(leftKeys: iset<Key>, rightKeys: iset<Key>) : (out: BetreeNode)
      requires WF()
      requires BetreeNode?
      ensures out.WF()
    {
      // We suppose that a lower layer will use this when leftKeys+rightKeys are all
      // identical, so that the first two branches of the if expression each produce
      // a single BetreeNode (with a shared representation below).
      assert children.WF(); // trigger
      var mapp := imap key | AnyKey(key)
        :: if key in leftKeys
            then children.mapp[key].ApplyFilter(leftKeys)
            else if key in rightKeys
            then children.mapp[key].ApplyFilter(rightKeys)
            else children.mapp[key];
      BetreeNode(DomainTODO, ChildMap(mapp), buffers)
    }

    function Promote() : (out: BetreeNode)
      requires WF()
      ensures out.WF()
    {
      if Nil? then EmptyRoot() else this
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
      BetreeNode(DomainTODO, outChildren, keptBuffers)
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
    BetreeNode(DomainTODO, ConstantChildMap(Nil), BufferStack([]))
  }

  datatype QueryReceiptLine = QueryReceiptLine(
    node: BetreeNode,
    result: Message)
  {
    predicate WF()
    {
      && node.WF()
      && result.Define?
    }
  }

  // NB the top line is the line for the root node; hence Result()==ResultAt(0)
  // The bottom line is always Nil
  datatype QueryReceipt = QueryReceipt(
    key: Key,
    root: BetreeNode,
    lines: seq<QueryReceiptLine>)
  {
    predicate Structure()
    {
      && 0 < |lines|
      && lines[0].node == root
      && (forall i:nat | i < |lines| :: lines[i].node.BetreeNode? <==> i < |lines|-1)
      && Last(lines).result == Define(DefaultValue())
    }

    predicate AllLinesWF()
    {
      && (forall i:nat | i < |lines| :: lines[i].WF())
    }

    function ChildAt(i: nat) : BetreeNode
      requires AllLinesWF()
      requires Structure()
      requires i < |lines|-1
    {
      assert lines[i].node.children.WF();  // trigger
      lines[i].node.children.mapp[key]
    }

    predicate ChildLinkedAt(i: nat)
      requires AllLinesWF()
      requires Structure()
      requires i < |lines|-1
    {
      lines[i+1].node == ChildAt(i)
    }

    function ResultAt(i: nat) : Message
      requires i < |lines|
    {
      lines[i].result
    }

    predicate ResultLinkedAt(i: nat)
      requires Structure()
      requires AllLinesWF()
      requires i < |lines| - 1
    {
      && lines[i].result == Merge(lines[i].node.buffers.Query(key), ResultAt(i+1))
    }

    predicate Valid()
    {
      && Structure()
      && AllLinesWF()
      && (forall i:nat | i < |lines| - 1 :: ChildLinkedAt(i))
      && (forall i:nat | i < |lines| - 1 :: ResultLinkedAt(i))
    }

    function Result() : Message
      requires Structure()
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
    then QueryReceipt(key, node, [QueryReceiptLine(Nil, Define(DefaultValue()))])
    else
      assert node.children.WF();  // trigger
      var childReceipt := BuildQueryReceipt(node.children.mapp[key], key);
      var thisMessage := node.buffers.Query(key);
      var topLine := QueryReceiptLine(node, Merge(thisMessage, childReceipt.Result()));
      var receipt := QueryReceipt(key, node, [topLine] + childReceipt.lines);
      assert receipt.ResultLinkedAt(0);
      assert forall i | 0<i<|receipt.lines|-1 :: childReceipt.ResultLinkedAt(i-1) && receipt.ResultLinkedAt(i);  // trigger Valid
      assert forall i | 0<i<|receipt.lines|-1 :: childReceipt.ChildLinkedAt(i-1) && receipt.ChildLinkedAt(i);  // trigger Valid
      receipt
  }

  datatype StampedBetree = StampedBetree(
    root: BetreeNode,
    // betree needs its own lsn so we remember it for freeze time without
    // having to drain the membuffer:
    seqEnd: LSN
    )
  {
    predicate WF()
    {
      root.WF()
    }

    function PrependMemtable(memtable: Memtable) : StampedBetree
      requires WF()
    {
      var newBuffer := Buffer(AllKeys(), memtable.mapp);
      StampedBetree(root.Promote().PrependBufferStack(BufferStack([newBuffer])), memtable.seqEnd)
    }
  }
    
  datatype Memtable = Memtable(mapp: map<Key, Message>, seqEnd: LSN)
  {
    function Get(key: Key) : Message
    {
      if key in mapp then mapp[key] else Update(NopDelta())
    }

    function ApplyPut(km: KeyedMessage) : Memtable
    {
      Memtable(mapp[km.key := Merge(km.message, Get(km.key))], seqEnd+1)
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

    // Drain out the contents (into the StampedBetree), but remember the seqEnd
    function Drain() : Memtable
    {
      EmptyMemtable(seqEnd)
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
    && v' == v
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
    && v' == v
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
        memtable := v.memtable.Drain(),
        stampedBetree := v.stampedBetree.PrependMemtable(v.memtable)
      )
  }
  
  datatype Path = Path(node: BetreeNode, key: Key, keyset: iset<Key>, depth: nat)
  {
    function Subpath() : (out: Path)
      requires 0 < depth
      requires node.WF()
      requires node.BetreeNode?
    {
      assert node.children.WF();  // trigger
      Path(node.children.mapp[key], key, keyset, depth-1)
    }

    predicate KeysetChildrenMatch()
      requires node.WF()
      requires node.BetreeNode?
    {
      assert node.children.WF();
      (forall k2 | k2 in keyset :: node.children.mapp[k2]==node.children.mapp[key])
    }

    predicate Valid()
      decreases depth
    {
      && node.WF()
      && node.BetreeNode?
      && key in keyset
      //&& (0 < depth ==> Path(node.children[key], key, depth-1).Valid())
      // keyset 
      && (0 < depth ==> KeysetChildrenMatch())
      && (0 < depth ==> Subpath().Valid())
    }

    function Target() : (out: BetreeNode)
      requires Valid()
      ensures out.WF()
      ensures out.BetreeNode?
      decreases depth
    {
      if 0 == depth
      then node
      else Subpath().Target()
    }

    // opaque: these imap comprehensions cause some trigger mischief!
    function {:opaque} ReplacedChildren(replacement: BetreeNode) : (out: ChildMap)
      requires Valid()
      requires replacement.WF()
      requires 0 < depth
      ensures out.WF()
      decreases depth, 0
    {
      assert node.children.WF();  // trigger
      var replacedChildren := Subpath().Substitute(replacement);
      ChildMap(imap k | AnyKey(k) :: if k in keyset then replacedChildren else node.children.mapp[k])
    }

    function Substitute(replacement: BetreeNode) : (out: BetreeNode)
      requires Valid()
      requires replacement.WF()
      decreases depth, 1
    {
      if 0 == depth
      then replacement
      else
        BetreeNode(DomainTODO, ReplacedChildren(replacement), node.buffers)
    }
  }

  predicate InternalGrow(v: Variables, v': Variables, lbl: TransitionLabel, step: Step)
  {
    && v.WF()
    && step.InternalGrowStep?
    && v' == v.(
        stampedBetree := v.stampedBetree.(
          root := BetreeNode(DomainTODO, ConstantChildMap(v.stampedBetree.root), BufferStack([]))
        )
      )
  }

  predicate InternalSplit(v: Variables, v': Variables, lbl: TransitionLabel, step: Step)
  {
    && step.InternalSplitStep?
    && step.path.Valid()
    && step.path.node == v.stampedBetree.root
    && v' == v.(
        stampedBetree := v.stampedBetree.(
          root := step.path.Substitute(step.path.Target().Split(step.leftKeys, step.rightKeys))
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
          root := step.path.Substitute(step.path.Target().Flush(step.downKeys))
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
    && step.path.Target().EquivalentBufferCompaction(step.compactedNode)
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
    | InternalGrowStep()
    | InternalSplitStep(path: Path, leftKeys: iset<Key>, rightKeys: iset<Key>)
    | InternalFlushStep(path: Path, downKeys: iset<Key>)
    | InternalCompactStep(path: Path, compactedNode: BetreeNode)

  predicate NextStep(v: Variables, v': Variables, lbl: TransitionLabel, step: Step)
  {
    match step {
      case QueryStep(receipt) => Query(v, v', lbl, receipt)
      case PutStep() => Put(v, v', lbl)
      case QueryEndLsnStep() => QueryEndLsn(v, v', lbl)
      case FreezeAsStep(stampedBetree) => FreezeAs(v, v', lbl, stampedBetree)
      case InternalGrowStep() => InternalGrow(v, v', lbl, step)
      case InternalSplitStep(_, _, _) => InternalSplit(v, v', lbl, step)
      case InternalFlushStep(_, _) => InternalFlush(v, v', lbl, step)
      case InternalCompactStep(_, _) => InternalCompact(v, v', lbl, step)
    }
  }

  predicate Next(v: Variables, v': Variables, lbl: TransitionLabel) {
    exists step: Step :: NextStep(v, v', lbl, step)
  }
}
