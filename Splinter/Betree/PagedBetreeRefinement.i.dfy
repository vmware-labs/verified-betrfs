// Copyright 2018-2021 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, and University of Washington
// SPDX-License-Identifier: BSD-2-Clause

include "PagedBetree.i.dfy"
include "../CoordinationLayer/AbstractMap.i.dfy"

module PagedBetreeRefinement
{
  import opened Options
  import opened KeyType
  import opened StampedMapMod
  import TotalKMMapMod
  import opened ValueMessage
  import opened MsgHistoryMod
  import opened LSNMod
  import opened Sequences
  import opened PagedBetree
  import AbstractMap

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
    requires stampedBetree.WF()
  {
    StampedMap(INode(stampedBetree.root), stampedBetree.seqEnd)
  }
    
  function ILbl(lbl: TransitionLabel) : AbstractMap.TransitionLabel
  {
    match lbl
      case QueryLabel(endLsn, key, value) => AbstractMap.QueryLabel(endLsn, key, value)
      case PutLabel(puts) => AbstractMap.PutLabel(puts)
      case QueryEndLsnLabel(endLsn) => AbstractMap.QueryEndLsnLabel(endLsn)
      case FreezeAsLabel(stampedBetree) => AbstractMap.FreezeAsLabel(
        if stampedBetree.WF() then IStampedBetree(stampedBetree) else StampedMapMod.Empty())
      case InternalLabel() => AbstractMap.InternalLabel()
  }

  function I(v: Variables) : AbstractMap.Variables
    requires v.WF()
  {
    AbstractMap.Variables(IStampedBetree(v.stampedBetree.PrependMemtable(v.memtable)))
  }

  function {:opaque} MapApply(memtable: Memtable, base: TotalKMMapMod.TotalKMMap) : TotalKMMapMod.TotalKMMap
  {
    imap k | TotalKMMapMod.AnyKey(k) :: Merge(memtable.Get(k), base[k])
  }

  lemma SingletonBufferStack(buffer: Buffer, key: Key)
    ensures buffer.Query(key) == BufferStack([buffer]).Query(key)
  {
    assert Merge(BufferStack([buffer]).QueryUpTo(key, 0), buffer.Query(key)) == buffer.Query(key); // trigger
  }

  lemma CommonBufferStacks(a: BufferStack, b: BufferStack, len: nat, key: Key)
    requires len <= |a.buffers|
    requires len <= |b.buffers|
    requires forall i | 0<=i<len :: a.buffers[i] == b.buffers[i]
    ensures a.QueryUpTo(key, len) == b.QueryUpTo(key, len)
  {
    var i:nat := 0;
    while i<len
      invariant i<=len
      invariant a.QueryUpTo(key, i) == b.QueryUpTo(key, i);
    {
      i := i + 1;
    }
  }

  lemma PrependBufferStackLemma(front: BufferStack, back: BufferStack, key: Key)
    ensures back.PrependBufferStack(front).Query(key) == Merge(front.Query(key), back.Query(key))
    decreases |back.buffers|
  {
    if |back.buffers| == 0 {
      assert back.PrependBufferStack(front).buffers == front.buffers;  // trigger
    } else {
      var dropBack := BufferStack(DropLast(back.buffers));
      CommonBufferStacks(dropBack.PrependBufferStack(front), back.PrependBufferStack(front), |front.buffers|+|back.buffers|-1, key);
      PrependBufferStackLemma(front, dropBack, key);
      CommonBufferStacks(dropBack, back, |back.buffers|-1, key);
    }
  }

  lemma {:timeLimitMultiplier 2} MemtableDistributesOverBetree(memtable: Memtable, base: StampedBetree)
    requires base.WF()
    ensures MapApply(memtable, INode(base.root)) == INode(base.PrependMemtable(memtable).root)
  {
    reveal_MapApply();
    assert MapApply(memtable, INode(base.root)).Keys == INode(base.PrependMemtable(memtable).root).Keys;  // trigger
    forall key | AnyKey(key)
      ensures MapApply(memtable, INode(base.root))[key] == INode(base.PrependMemtable(memtable).root)[key]
    {
      var newBuffer := Buffer(AllKeys(), memtable.mapp);
      SingletonBufferStack(newBuffer, key);
      PrependBufferStackLemma(BufferStack([newBuffer]), base.root.Promote().buffers, key);
      reveal_INode(); // this imap's really a doozy
    }
  }

  lemma EquivalentRootVars(v: Variables, v': Variables)
    requires v.WF()
    requires v'.WF()
    requires v.memtable == v'.memtable
    requires v.stampedBetree.seqEnd == v'.stampedBetree.seqEnd
    requires INode(v.stampedBetree.root) == INode(v'.stampedBetree.root)
    ensures I(v) == I(v')
  {
    MemtableDistributesOverBetree(v.memtable, v.stampedBetree);
    MemtableDistributesOverBetree(v.memtable, v'.stampedBetree);
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
    requires INode(path.Target()) == INode(replacement)
    ensures path.Substitute(replacement).WF()
    decreases path.depth
  {
    if 0 < path.depth {
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
    decreases path.depth
  {
    // Behold the power of the receipt! This is where the magic happens.
    SubstitutePreservesWF(path, replacement);
    if 0 < path.depth {
      if key !in path.keyset {
        // key diverged from changes made by substitution, so they're easy equal.
        assert INodeAt(path.node, key) == INodeAt(path.Substitute(replacement), key);
      } else {
        EqualReceipts(BuildQueryReceipt(path.Subpath().node, key),
          ReceiptDropFirst(BuildQueryReceipt(path.node, key)));
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
    var orig := v.stampedBetree.root;
    var grown := BetreeNode(DomainTODO, ConstantChildMap(orig), BufferStack([]));

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

  // TODO fold together with prev
  lemma FilteredOutBufferStack(bufferStack: BufferStack, filter: iset<Key>, key: Key)
    requires key !in filter
    ensures bufferStack.ApplyFilter(filter).Query(key) == Update(NopDelta())
  {
    var i:nat := 0;
    while i < |bufferStack.buffers|
      invariant i <= |bufferStack.buffers|
      invariant bufferStack.ApplyFilter(filter).QueryUpTo(key, i) == Update(NopDelta())
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

  lemma PrependBetreeNodeLemma(node: BetreeNode, buffers: BufferStack, key: Key)
    requires node.WF()
    ensures INodeAt(node.Promote().PrependBufferStack(buffers), key) == Merge(buffers.Query(key), INodeAt(node, key))
  {
    PrependBufferStackLemma(buffers, node.Promote().buffers, key);
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
        FilteredOutBufferStack(target.buffers, AllKeys() - step.downKeys, key);
        assert target.children.WF();  // trigger
        var movedBuffers := target.buffers.ApplyFilter(step.downKeys);
        PrependBetreeNodeLemma(target.children.mapp[key], movedBuffers, key);
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
    requires InternalCompact(v, v', lbl, step)
    ensures I(v') == I(v)
  {
    INodeExtensionality(step.compactedNode, step.path.Target());
    SubstituteEquivalence(step.path, step.compactedNode);
    EquivalentRootVars(v, v');
  }

//  // TODO delete
//  lemma NoopSteps(v: Variables, v': Variables, lbl: TransitionLabel, step: Step)
//    requires v.WF()
//    requires v'.WF()
//    requires NextStep(v, v', lbl, step)
//    requires !step.PutStep?
//    ensures I(v') == I(v)
//  {
//    match step {
//      case QueryStep(receipt) => {
//        assert Query(v, v', lbl, receipt);
//        assert v' == v;
//        assert I(v') == I(v);
//      }
//      case PutStep() => {
//        assert false;
//      }
//      case QueryEndLsnStep() => {
//        assert I(v') == I(v);
//      }
//      case FreezeAsStep() => {
//        assert I(v') == I(v);
//      }
//      case InternalGrowStep() => {
//        InternalGrowNoop(v, v', lbl, step);
//      }
//      case InternalSplitStep(_, _, _) => {
//        InternalSplitNoop(v, v', lbl, step);
//      }
//      case InternalFlushStep(_, _) => {
//        InternalFlushNoop(v, v', lbl, step);
//      }
//      case InternalCompactStep(_, _) => {
//        InternalCompactNoop(v, v', lbl, step);
//      }
//    }
//  }

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
    MemtableDistributesOverBetree(v.memtable, v.stampedBetree);
    reveal_MapApply();
    reveal_INode();
  }

  lemma QueryRefines(v: Variables, v': Variables, lbl: TransitionLabel, step: Step)
    requires Inv(v)
    requires step.QueryStep?
    requires Query(v, v', lbl, step.receipt)
    ensures AbstractMap.Next(I(v), I(v'), ILbl(lbl));
  {
    assert TotalKMMapMod.AnyKey(lbl.key); // trigger
    EqualReceipts(step.receipt, BuildQueryReceipt(v.stampedBetree.root, lbl.key));
    MemtableDistributesOverBetree(v.memtable, v.stampedBetree);
    reveal_MapApply();
    reveal_INode(); 
  }

  lemma ApplyPutIsMapPlusHistory(v: Variables, v': Variables, puts: MsgHistory)
    requires v.WF()
    requires v'.WF()
    requires puts.WF()
    requires puts.seqStart == v.memtable.seqEnd
    requires puts.Len() == 1
    requires v' == v.(memtable := v.memtable.ApplyPuts(puts))
    ensures I(v').stampedMap == MapPlusHistory(I(v).stampedMap, puts)
  {
  // TODO tidy this monstrosity
    var keyedMsg := puts.msgs[puts.seqStart];
    var KeyedMessage(key,message) := keyedMsg;
    assert TotalKMMapMod.AnyKey(key);
    assert v'.memtable == v.memtable.ApplyPut(keyedMsg);
    var memUpdated := Merge(message, v.memtable.Get(key));
    calc {
      v.memtable.ApplyPut(keyedMsg);
      Memtable(v.memtable.mapp[key := memUpdated], v.memtable.seqEnd+1);
    }
    calc {
      v'.stampedBetree.PrependMemtable(v'.memtable).seqEnd;
      I(v).stampedMap.seqEnd + 1;
    }
    assert INode(v'.stampedBetree.PrependMemtable(v'.memtable).root).Keys == AllKeys() by { reveal_INode(); }
    assert I(v).stampedMap.mi[key := Merge(message, I(v).stampedMap.mi[key])].Keys == AllKeys() by { reveal_INode(); }
    forall k | AnyKey(k)
      ensures INode(v'.stampedBetree.PrependMemtable(v'.memtable).root)[k]
        == I(v).stampedMap.mi[key := Merge(message, I(v).stampedMap.mi[key])][k]
    {
      var node := v.stampedBetree.root;
      var buffer := Buffer(AllKeys(), v.memtable.mapp);
      var buffers := BufferStack([buffer]);
      var buffer' := Buffer(AllKeys(), v'.memtable.mapp);
      var buffers' := BufferStack([buffer']);
      if k!=key {
        calc {
          buffer'.Query(k);
          buffer.Query(k);
        }
        calc {
          buffers'.Query(k);
          buffers'.QueryUpTo(k, 1);
          Merge(buffers'.QueryUpTo(k, 0), buffers'.buffers[0].Query(k));
          Merge(Update(NopDelta()), buffer'.Query(k));
          Merge(Update(NopDelta()), buffer.Query(k));
          buffers.QueryUpTo(k, 1);
          buffers.Query(k);
        }
        calc {
          INode(v'.stampedBetree.PrependMemtable(v'.memtable).root)[k];
            { reveal_INode(); }
          INodeAt(v'.stampedBetree.PrependMemtable(v'.memtable).root, k);
            { PrependBetreeNodeLemma(node, buffers', k); }
          Merge(buffers'.Query(k), INodeAt(node, k));
          Merge(buffers.Query(k), INodeAt(node, k));
            { PrependBetreeNodeLemma(node, buffers, k); }
          INodeAt(v.stampedBetree.PrependMemtable(v.memtable).root, k);
            { reveal_INode(); }
          INode(v.stampedBetree.PrependMemtable(v.memtable).root)[k];
        }
      } else {
        // propagate the message
        calc {
          buffer'.Query(k);
          memUpdated;
        }
        calc {
          buffers'.Query(k);
          buffers'.QueryUpTo(k, 1);
          Merge(buffers'.QueryUpTo(k, 0), buffers'.buffers[0].Query(k));
          Merge(Update(NopDelta()), buffer'.Query(k));
          Merge(Update(NopDelta()), memUpdated);
          memUpdated;
        }
        calc {
          v.memtable.Get(k);
          buffer.Query(k);
          Merge(Update(NopDelta()), buffer.Query(k));
          buffers.QueryUpTo(k, 1);
          buffers.Query(k);
        }

        calc {
          INode(v'.stampedBetree.PrependMemtable(v'.memtable).root)[k];
            { reveal_INode(); }
          INodeAt(v'.stampedBetree.PrependMemtable(v'.memtable).root, k);
            { PrependBetreeNodeLemma(node, buffers', k); }
          Merge(buffers'.Query(k), INodeAt(node, k));
          Merge(memUpdated, INodeAt(node, k));
          Merge(Merge(message, v.memtable.Get(k)), INodeAt(node, k));
          Merge(message, Merge(v.memtable.Get(k), INodeAt(node, k)));
          Merge(message, Merge(buffers.Query(k), INodeAt(node, k)));
            { PrependBetreeNodeLemma(node, buffers, k); }
          Merge(message, INodeAt(v.stampedBetree.PrependMemtable(v.memtable).root, k));
            { reveal_INode(); }
          Merge(message, INode(v.stampedBetree.PrependMemtable(v.memtable).root)[k]);
          I(v).stampedMap.mi[key := Merge(message, I(v).stampedMap.mi[key])][k];
        }
      }
    }
    calc {
      INode(v'.stampedBetree.PrependMemtable(v'.memtable).root);
      I(v).stampedMap.mi[key := Merge(message, I(v).stampedMap.mi[key])];
    }
    calc {
      I(v').stampedMap;
      IStampedBetree(v'.stampedBetree.PrependMemtable(v'.memtable));
      StampedMap(INode(v'.stampedBetree.PrependMemtable(v'.memtable).root), v'.stampedBetree.PrependMemtable(v'.memtable).seqEnd);


      StampedMap(I(v).stampedMap.mi[key := Merge(message, I(v).stampedMap.mi[key])], I(v).stampedMap.seqEnd + 1);
      puts.ApplyToStampedMap(I(v).stampedMap);
      MapPlusHistory(I(v).stampedMap, puts);
    }
  }

  lemma CompositePuts(puts1: MsgHistory, puts2: MsgHistory, stampedMap: StampedMap)
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
    if puts.Len() == 0 {
      assert I(v').stampedMap == MapPlusHistory(I(v).stampedMap, puts);
    } else {
      var shortPuts := puts.DiscardRecent(puts.seqEnd-1);
      var lastPut := puts.DiscardOld(puts.seqEnd-1);
      assert puts == shortPuts.Concat(lastPut);
      var vmid := v.(memtable := v.memtable.ApplyPuts(shortPuts));
      ApplyPutsIsMapPlusHistory(v, vmid, shortPuts);
      assert I(vmid).stampedMap == MapPlusHistory(I(v).stampedMap, shortPuts);
      //ApplyPutsIsMapPlusHistory(vmid, v', lastPut);
      ApplyPutIsMapPlusHistory(vmid, v', lastPut);
      assert I(v').stampedMap == MapPlusHistory(I(vmid).stampedMap, lastPut);
      CompositePuts(shortPuts, lastPut, I(v).stampedMap);
      assert I(v').stampedMap == MapPlusHistory(I(v).stampedMap, puts);
    }
  }

  lemma PutRefines(v: Variables, v': Variables, lbl: TransitionLabel, step: Step)
    requires Inv(v)
    requires step.PutStep?
    requires Put(v, v', lbl)
    ensures AbstractMap.Put(I(v), I(v'), ILbl(lbl));
  {
    //assert TotalKMMapMod.AnyKey(lbl.key); // trigger
    //EqualReceipts(step.receipt, BuildQueryReceipt(v.stampedBetree.root, lbl.key));
    MemtableDistributesOverBetree(v.memtable, v.stampedBetree);
    reveal_MapApply();
    reveal_INode(); 
    ApplyPutsIsMapPlusHistory(v, v', lbl.puts);
//    calc {
//      I(v').stampedMap;
//      IStampedBetree(v'.stampedBetree.PrependMemtable(v'.memtable));
//        memtable := v.memtable.ApplyPuts(lbl.puts)
//
//      lbl.puts.ApplyToStampedMap(I(v).stampedMap);
//      MapPlusHistory(I(v).stampedMap, lbl.puts);
//    }
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
