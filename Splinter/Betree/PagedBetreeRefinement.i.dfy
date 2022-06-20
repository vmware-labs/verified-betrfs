// Copyright 2018-2021 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, and University of Washington
// SPDX-License-Identifier: BSD-2-Clause

include "PagedBetree.i.dfy"
include "../CoordinationLayer/AbstractMap.i.dfy"

module PagedBetreeRefinement
{
  import opened Options
  import opened KeyType
  import opened StampedMod
  import TotalKMMapMod
  import opened ValueMessage
  import opened MsgHistoryMod
  import opened LSNMod
  import opened Sequences
  import opened PagedBetree
  import opened Buffers
  import opened MemtableMod
  import AbstractMap

  // Constructive evidence that a Valid QueryReceipt exists for every key.
  function BuildQueryReceipt(node: BetreeNode, key: Key) : (receipt: QueryReceipt)
    requires node.WF()
    ensures receipt.key == key
    ensures receipt.Valid()
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
      assert forall i | 0 < i< |receipt.lines|-1 :: childReceipt.ResultLinkedAt(i-1) && receipt.ResultLinkedAt(i);  // trigger Valid
      assert forall i | 0 < i< |receipt.lines|-1 :: receipt.ChildLinkedAt(i) by {  // not sure why this one demands being unrolled
        forall i | 0 < i< |receipt.lines|-1 ensures receipt.ChildLinkedAt(i) { assert childReceipt.ChildLinkedAt(i-1); } // trigger
      }
      receipt
  }

  function INodeAt(betreeNode: BetreeNode, key: Key) : Message
    requires betreeNode.WF()
  {
    BuildQueryReceipt(betreeNode, key).Result()
  }
  
  function {:opaque} INode(betreeNode: BetreeNode) : TotalKMMapMod.TotalKMMap
    requires betreeNode.WF()
  {
    imap key | TotalKMMapMod.AnyKey(key) :: INodeAt(betreeNode, key)
  }

  function IStampedBetree(stampedBetree: StampedBetree) : StampedMap
    requires stampedBetree.value.WF()
  {
    Stamped(INode(stampedBetree.value), stampedBetree.seqEnd)
  }
    
  function ILbl(lbl: TransitionLabel) : AbstractMap.TransitionLabel
  {
    match lbl
      case QueryLabel(endLsn, key, value) => AbstractMap.QueryLabel(endLsn, key, value)
      case PutLabel(puts) => AbstractMap.PutLabel(puts)
      case QueryEndLsnLabel(endLsn) => AbstractMap.QueryEndLsnLabel(endLsn)
      case FreezeAsLabel(stampedBetree) => AbstractMap.FreezeAsLabel(
        if stampedBetree.value.WF() then IStampedBetree(stampedBetree) else StampedMod.Empty())
      case InternalLabel() => AbstractMap.InternalLabel()
  }

  function I(v: Variables) : AbstractMap.Variables
    requires v.WF()
  {
    AbstractMap.Variables(IStampedBetree(v.root.PushMemtable(v.memtable)))
  }

  lemma SingletonBufferStack(buffer: Buffer, key: Key)
    ensures buffer.Query(key) == BufferStack([buffer]).Query(key)
  {
    assert Merge(BufferStack([buffer]).QueryUpTo(key, 0), buffer.Query(key)) == buffer.Query(key); // trigger
  }

  lemma CommonBufferStacks(a: BufferStack, b: BufferStack, len: nat, key: Key)
    requires len <= |a.buffers|
    requires len <= |b.buffers|
    requires forall i | 0 <= i< len :: a.buffers[i] == b.buffers[i]
    ensures a.QueryUpTo(key, len) == b.QueryUpTo(key, len)
  {
    var i:nat := 0;
    while i < len
      invariant i<=len
      invariant a.QueryUpTo(key, i) == b.QueryUpTo(key, i);
    {
      i := i + 1;
    }
  }

  lemma PushBufferStackLemma(top: BufferStack, bottom: BufferStack, key: Key)
    ensures bottom.PushBufferStack(top).Query(key) == Merge(top.Query(key), bottom.Query(key))
    decreases |bottom.buffers|
  {
    if |bottom.buffers| == 0 {
      assert bottom.PushBufferStack(top).buffers == top.buffers;  // trigger
    } else {
      var dropBottom := BufferStack(DropLast(bottom.buffers));
      CommonBufferStacks(dropBottom.PushBufferStack(top), bottom.PushBufferStack(top), |top.buffers|+|bottom.buffers|-1, key);
      PushBufferStackLemma(top, dropBottom, key);
      CommonBufferStacks(dropBottom, bottom, |bottom.buffers|-1, key);
    }
  }

  function {:opaque} MapApply(memtable: Memtable, base: TotalKMMapMod.TotalKMMap) : TotalKMMapMod.TotalKMMap
  {
    imap k | TotalKMMapMod.AnyKey(k) :: Merge(memtable.Get(k), base[k])
  }

  lemma {:timeLimitMultiplier 2} MemtableDistributesOverBetree(memtable: Memtable, root: BetreeNode)
    requires root.WF()
    ensures MapApply(memtable, INode(root)) == INode(root.PushMemtable(memtable).value)
  {
    reveal_MapApply();
    assert MapApply(memtable, INode(root)).Keys == INode(root.PushMemtable(memtable).value).Keys;  // trigger
    forall key | AnyKey(key)
      ensures MapApply(memtable, INode(root))[key] == INode(root.PushMemtable(memtable).value)[key]
    {
      var newBuffer := Buffer(memtable.mapp);
      SingletonBufferStack(newBuffer, key);
      PushBufferStackLemma(BufferStack([newBuffer]), root.Promote().buffers, key);
      reveal_INode(); // this imap's really a doozy
    }
  }

  lemma EquivalentRootVars(v: Variables, v': Variables)
    requires v.WF()
    requires v'.WF()
    requires v.memtable == v'.memtable
    // requires v.stampedBetree.seqEnd == v'.stampedBetree.seqEnd
    requires INode(v.root) == INode(v'.root)
    ensures I(v) == I(v')
  {
    MemtableDistributesOverBetree(v.memtable, v.root);
    MemtableDistributesOverBetree(v.memtable, v'.root);
  }

  lemma INodeExtensionality(a: BetreeNode, b: BetreeNode)
    requires a.WF()
    requires b.WF()
    requires forall key | AnyKey(key) :: INodeAt(a, key) == INodeAt(b, key)
    ensures INode(a) == INode(b)
  {
    reveal_INode();
  }

  lemma SubstitutePreservesWF(path: Path, replacement: BetreeNode)
    requires path.Valid()
    requires replacement.WF()
    requires INode(path.Target()) == INode(replacement) // TODO(jonh): probably unecessary.
    ensures path.Substitute(replacement).WF()
    decreases |path.routing|
  {
    if 0 < |path.routing| {
      SubstitutePreservesWF(path.Subpath(), replacement);
      assert path.Substitute(replacement).children.WF();
      assert path.Substitute(replacement).WF();
    } else {
      assert path.Substitute(replacement).WF();
    }
  }

  function ReceiptDropFirst(receipt: QueryReceipt) : (out: QueryReceipt)
    requires receipt.Valid()
    requires 1 < |receipt.lines|
  {
    assert receipt.root.children.WF();  // trigger
    QueryReceipt(receipt.key, receipt.root.children.mapp[receipt.key], receipt.lines[1..])
  }

  lemma ReceiptDropFirstValid(receipt: QueryReceipt)
    requires receipt.Valid()
    requires 1 < |receipt.lines|
    ensures ReceiptDropFirst(receipt).Valid()
  {
    var out := ReceiptDropFirst(receipt);
    assert receipt.ResultLinkedAt(0); // trigger
    assert receipt.ChildLinkedAt(0);  // trigger
    forall i:nat | i < |out.lines|-1 ensures out.ChildLinkedAt(i) {
      assert receipt.ChildLinkedAt(i+1);  // trigger
    }
    forall i:nat | i < |out.lines|-1 ensures out.ResultLinkedAt(i) {
      assert receipt.ResultLinkedAt(i+1); // trigger
    }
  }

  lemma EqualReceipts(a: QueryReceipt, b: QueryReceipt)
    requires a.Valid()
    requires b.Valid()
    requires a.key == b.key
    requires a.root == b.root
    ensures a == b
    decreases |a.lines|
  {
    if 1 < |a.lines| {
      ReceiptDropFirstValid(a);
      ReceiptDropFirstValid(b);
      EqualReceipts(ReceiptDropFirst(a), ReceiptDropFirst(b));
      assert a.ResultLinkedAt(0);  // trigger
      assert b.ResultLinkedAt(0);  // trigger
    }
  }

  lemma SubstituteReceiptEquivalence(path: Path, replacement: BetreeNode, key: Key)
    requires path.Valid()
    requires replacement.WF()
    requires INodeAt(path.Target(), key) == INodeAt(replacement, key)
    requires INode(path.Target()) == INode(replacement)
    ensures path.Substitute(replacement).WF()
    ensures INodeAt(path.node, key) == INodeAt(path.Substitute(replacement), key)
    decreases |path.routing|
  {
    // Behold the power of the receipt! This is where the magic happens.
    SubstitutePreservesWF(path, replacement);
    if 0 < |path.routing| {
      if key !in path.routing[0] {
        // key diverged from changes made by substitution, so they're easy equal.
        assert INodeAt(path.node, key) == INodeAt(path.Substitute(replacement), key);
      } else {
        var receipt := BuildQueryReceipt(path.node, key);
        ReceiptDropFirstValid(receipt);
        assert ReceiptDropFirst(receipt).root == path.Subpath().node by {
          assert path.Subpath().node == path.node.Child(path.key);
          assert receipt.ChildLinkedAt(0); // trigger
          //assert ReceiptDropFirst(receipt).key == receipt.key;
//          assert receipt.key == key;
//          assert path.key == key;
//          assert receipt.key == path.key;
//          assert ReceiptDropFirst(receipt).root == receipt.lines[0].node.Child(path.key);
        }
        EqualReceipts(BuildQueryReceipt(path.Subpath().node, key), ReceiptDropFirst(receipt));
        assert path.Substitute(replacement).children.mapp[key] == path.Subpath().Substitute(replacement)
          by { path.reveal_ReplacedChildren(); }
        EqualReceipts(BuildQueryReceipt(path.Subpath().Substitute(replacement), key),
          ReceiptDropFirst(BuildQueryReceipt(path.Substitute(replacement), key)));

        SubstituteReceiptEquivalence(path.Subpath(), replacement, key);
      }
    }
  }

  lemma ApplyINodeEquivalence(a: BetreeNode, b: BetreeNode, key: Key)
    requires a.WF()
    requires b.WF()
    requires INode(a) == INode(b)
    ensures INodeAt(a, key) == INodeAt(b, key)
  {
    assert AnyKey(key); // trigger
    reveal_INode();
    assert INodeAt(a, key) == INode(a)[key];  // trigger
    assert INodeAt(b, key) == INode(b)[key];  // trigger
  }

  // TODO(jonh): side quest: we don't need receipts, do we?
  lemma SubstituteEquivalence(path: Path, replacement: BetreeNode)
    requires path.Valid()
    requires replacement.WF()
    requires INode(path.Target()) == INode(replacement)
    ensures path.Substitute(replacement).WF()
    ensures INode(path.node) == INode(path.Substitute(replacement))
  {
    SubstitutePreservesWF(path, replacement);
    forall key | AnyKey(key)
      ensures INodeAt(path.node, key) == INodeAt(path.Substitute(replacement), key)
    {
      ApplyINodeEquivalence(path.Target(), replacement, key);
      SubstituteReceiptEquivalence(path, replacement, key);
    }
    INodeExtensionality(path.node, path.Substitute(replacement));
  }

  lemma InternalGrowNoop(v: Variables, v': Variables, lbl: TransitionLabel, step: Step)
    requires v.WF()
    requires v'.WF()
    requires InternalGrow(v, v', lbl, step)
    ensures I(v') == I(v)
  {
    var orig := v.root;
    var grown := BetreeNode(BufferStack([]), ConstantChildMap(orig));

    forall key | AnyKey(key)
      ensures INodeAt(grown, key) == INodeAt(orig, key)
    {
      calc {
        INodeAt(grown, key);
        BuildQueryReceipt(grown, key).Result();
        BuildQueryReceipt(orig, key).Result();
        INodeAt(orig, key);
      }
    }
    INodeExtensionality(grown, orig);
    EquivalentRootVars(v, v');
  }

  lemma FilteredBufferStack(bufferStack: BufferStack, filter: iset<Key>, key: Key)
    ensures bufferStack.ApplyFilter(filter).Query(key) == if key in filter then bufferStack.Query(key) else Update(NopDelta())
  {
    var i:nat := 0;
    while i < |bufferStack.buffers|
      invariant i <= |bufferStack.buffers|
      invariant bufferStack.ApplyFilter(filter).QueryUpTo(key, i) == if key in filter then bufferStack.QueryUpTo(key, i) else Update(NopDelta())
    {
      i := i + 1;
    }
  }

  lemma ApplyFilterEquivalance(orig: BetreeNode, filter: iset<Key>, key: Key)
    requires orig.WF()
    requires key in filter
    ensures INodeAt(orig.ApplyFilter(filter), key) == INodeAt(orig, key)
  {
    var receipt := BuildQueryReceipt(orig, key);
    if 1 < |receipt.lines| {
      FilteredBufferStack(receipt.lines[0].node.buffers, filter, key);
    }
  }

  lemma InternalSplitNoop(v: Variables, v': Variables, lbl: TransitionLabel, step: Step)
    requires v.WF()
    requires v'.WF()
    requires InternalSplit(v, v', lbl, step)
    ensures I(v') == I(v)
  {
    var target := step.path.Target();
    var top := target.Split(step.leftKeys, step.rightKeys);
    forall key | AnyKey(key)
      ensures INodeAt(target, key) == INodeAt(top, key)
    {
      assert target.children.WF();  // trigger
      var targetChild := target.children.mapp[key];
      if key in step.leftKeys {
        ApplyFilterEquivalance(targetChild, step.leftKeys, key);
      } else if key in step.rightKeys {
        ApplyFilterEquivalance(targetChild, step.rightKeys, key);
      }
    }
    INodeExtensionality(target, top);
    SubstituteEquivalence(step.path, top);
    EquivalentRootVars(v, v');
  }

  lemma PushBetreeNodeLemma(node: BetreeNode, buffers: BufferStack, key: Key)
    requires node.WF()
    ensures INodeAt(node.Promote().PushBufferStack(buffers), key) == Merge(buffers.Query(key), INodeAt(node, key))
  {
    PushBufferStackLemma(buffers, node.Promote().buffers, key);
  }

  lemma InternalFlushNoop(v: Variables, v': Variables, lbl: TransitionLabel, step: Step)
    requires v.WF()
    requires v'.WF()
    requires InternalFlush(v, v', lbl, step)
    ensures I(v') == I(v)
  {
    var target := step.path.Target();
    var top := target.Flush(step.downKeys);
    forall key | AnyKey(key)
      ensures INodeAt(target, key) == INodeAt(top, key)
    {
      if key in step.downKeys {
        FilteredBufferStack(target.buffers, AllKeys() - step.downKeys, key);
        assert target.children.WF();  // trigger
        var movedBuffers := target.buffers.ApplyFilter(step.downKeys);
        PushBetreeNodeLemma(target.children.mapp[key], movedBuffers, key);
        FilteredBufferStack(target.buffers, step.downKeys, key);
      } else {
        FilteredBufferStack(target.buffers, AllKeys() - step.downKeys, key);
      }
    }
    INodeExtensionality(target, top);
    SubstituteEquivalence(step.path, top);
    EquivalentRootVars(v, v');
  }

  lemma InternalCompactNoop(v: Variables, v': Variables, lbl: TransitionLabel, step: Step)
    requires v.WF()
    requires v'.WF()
    requires step.WF()
    requires InternalCompact(v, v', lbl, step)
    ensures I(v') == I(v)
  {
    var compactedNode := CompactedNode(step.path.Target(), step.compactedBuffers);
    INodeExtensionality(compactedNode, step.path.Target());
    SubstituteEquivalence(step.path, compactedNode);
    EquivalentRootVars(v, v');
  }

  //////////////////////////////////////////////////////////////////////////////
  // State machine refinement

  predicate Inv(v: Variables)
  {
    && v.WF()
  }
  
  lemma InvInit(v: Variables, stampedBetree: StampedBetree)
    requires Init(v, stampedBetree)
    ensures Inv(v)
  {
  }

  lemma InvNext(v: Variables, v': Variables, lbl: TransitionLabel)
    requires Inv(v)
    requires Next(v, v', lbl)
    ensures Inv(v')
  {
  }

  lemma InitRefines(v: Variables, stampedBetree: StampedBetree)
    requires Init(v, stampedBetree)
    ensures AbstractMap.Init(I(v), IStampedBetree(stampedBetree))
  {
    MemtableDistributesOverBetree(v.memtable, v.root);
    reveal_MapApply();
    reveal_INode();
    assert INode(stampedBetree.value.PushMemtable(v.memtable).value) == INode(stampedBetree.value); // trigger
  }

  lemma QueryRefines(v: Variables, v': Variables, lbl: TransitionLabel, step: Step)
    requires Inv(v)
    requires step.QueryStep?
    requires Query(v, v', lbl, step.receipt)
    ensures AbstractMap.Next(I(v), I(v'), ILbl(lbl));
  {
    assert TotalKMMapMod.AnyKey(lbl.key); // trigger
    EqualReceipts(step.receipt, BuildQueryReceipt(v.root, lbl.key));
    MemtableDistributesOverBetree(v.memtable, v.root);
    reveal_MapApply();
    reveal_INode(); 
  }

  lemma ApplySinglePutIsMapPlusHistory(v: Variables, v': Variables, puts: MsgHistory)
    requires v.WF()
    requires v'.WF()
    requires puts.WF()
    requires puts.seqStart == v.memtable.seqEnd
    requires puts.Len() == 1
    requires v' == v.(memtable := v.memtable.ApplyPuts(puts))
    ensures I(v').stampedMap == MapPlusHistory(I(v).stampedMap, puts)
  {
    var KeyedMessage(key,message) := puts.msgs[puts.seqStart];
    assert TotalKMMapMod.AnyKey(key);  // trigger

    assert INode(v'.root.PushMemtable(v'.memtable).value).Keys == AllKeys() by { reveal_INode(); }
    assert I(v).stampedMap.value[key := Merge(message, I(v).stampedMap.value[key])].Keys == AllKeys() by { reveal_INode(); }
    forall k | AnyKey(k)
      ensures INode(v'.root.PushMemtable(v'.memtable).value)[k]
        == I(v).stampedMap.value[key := Merge(message, I(v).stampedMap.value[key])][k]
    {
      var node := v.root;
      var buffer := Buffer(v.memtable.mapp);
      var buffers := BufferStack([buffer]);
      var buffer' := Buffer(v'.memtable.mapp);
      var buffers' := BufferStack([buffer']);

      if k!=key {
        assert buffer'.Query(k) == buffer.Query(k);  // trigger
        assert buffers'.Query(k) == buffers'.QueryUpTo(k, 1);  // trigger: unroll
        assert buffers.Query(k) == buffers.QueryUpTo(k, 1);  // trigger: unroll
      } else {
        // propagate the message
        assert Merge(message, v.memtable.Get(key)) == buffers'.QueryUpTo(k, 1);  // trigger: unroll QueryUpTo
        assert v.memtable.Get(k) == buffers.QueryUpTo(k, 1);  // trigger: unroll QueryUpTo
      }
      PushBetreeNodeLemma(node, buffers', k);
      PushBetreeNodeLemma(node, buffers, k);
      reveal_INode();
    }
    assert I(v').stampedMap.value == puts.ApplyToStampedMap(I(v).stampedMap).value;  // trigger.  (should we have a "mention" operator just for triggering an expression?)
  }

  lemma CompositeSinglePut(puts1: MsgHistory, puts2: MsgHistory, stampedMap: StampedMap)
    requires puts1.WF()
    requires puts2.WF()
    requires puts2.Len() == 1 // could easily generalize, but I don't need it.
    requires puts1.seqStart == stampedMap.seqEnd
    requires puts2.seqStart == puts1.seqEnd
    ensures puts1.Concat(puts2).ApplyToStampedMap(stampedMap) == puts2.ApplyToStampedMap(puts1.ApplyToStampedMap(stampedMap))
  {
    assert puts1 == puts1.Concat(puts2).DiscardRecent(puts2.seqEnd - 1);  // seq math trigger
  }

  lemma ApplyPutsIsMapPlusHistory(v: Variables, v': Variables, puts: MsgHistory)
    requires v.WF()
    requires v'.WF()
    requires puts.WF()
    requires puts.seqStart == v.memtable.seqEnd
    requires v' == v.(memtable := v.memtable.ApplyPuts(puts))
    ensures I(v').stampedMap == MapPlusHistory(I(v).stampedMap, puts)
    decreases puts.Len()
  {
    if 0 < puts.Len() {
      var shortPuts := puts.DiscardRecent(puts.seqEnd-1);
      var lastPut := puts.DiscardOld(puts.seqEnd-1);
      var vmid := v.(memtable := v.memtable.ApplyPuts(shortPuts));
      ApplyPutsIsMapPlusHistory(v, vmid, shortPuts);  // recurse
      ApplySinglePutIsMapPlusHistory(vmid, v', lastPut);  // take care of last put
      CompositeSinglePut(shortPuts, lastPut, I(v).stampedMap);  // push Concat through ApplyToStampedMap (MapPlusHistory)
    }
  }

  lemma PutRefines(v: Variables, v': Variables, lbl: TransitionLabel, step: Step)
    requires Inv(v)
    requires step.PutStep?
    requires Put(v, v', lbl)
    ensures AbstractMap.Put(I(v), I(v'), ILbl(lbl));
  {
    MemtableDistributesOverBetree(v.memtable, v.root);
    reveal_MapApply();
    reveal_INode(); 
    ApplyPutsIsMapPlusHistory(v, v', lbl.puts);
  }

  lemma NextRefines(v: Variables, v': Variables, lbl: TransitionLabel)
    requires Inv(v)
    requires Next(v, v', lbl)
    ensures v'.WF()
    ensures AbstractMap.Next(I(v), I(v'), ILbl(lbl))
  {
    var step: Step :| NextStep(v, v', lbl, step);
    match step {
      case QueryStep(receipt) => { QueryRefines(v, v', lbl, step); }
      case PutStep() => { PutRefines(v, v', lbl, step); }
      case QueryEndLsnStep() => {
        assert AbstractMap.Next(I(v), I(v'), ILbl(lbl));
      }
      case FreezeAsStep() => {
        assert AbstractMap.Next(I(v), I(v'), ILbl(lbl));
      }
      case InternalGrowStep() => {
        InternalGrowNoop(v, v', lbl, step);
      }
      case InternalSplitStep(_, _, _) => {
        InternalSplitNoop(v, v', lbl, step);
      }
      case InternalFlushStep(_, _) => {
        InternalFlushNoop(v, v', lbl, step);
      }
      case InternalCompactStep(_, _) => {
        InternalCompactNoop(v, v', lbl, step);
      }
    }
  }
}
