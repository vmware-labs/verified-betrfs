// Copyright 2018-2021 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, and University of Washington
// SPDX-License-Identifier: BSD-2-Clause

include "PagedBetree.i.dfy"

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
    
  function I(v: Variables) : StampedMap
    requires v.WF()
  {
    IStampedBetree(v.stampedBetree.PrependMemtable(v.memtable))
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
        // TODO tidy
        var r := BuildQueryReceipt(path.node, key);
        var r' := BuildQueryReceipt(path.Substitute(replacement), key);

        assert r.Result() == Merge(r.lines[0].node.buffers.Query(key), r.ResultAt(1));
        assert r'.Result() == Merge(r'.lines[0].node.buffers.Query(key), r'.ResultAt(1));

        var sr := BuildQueryReceipt(path.Subpath().node, key);
        var er := ReceiptDropFirst(r);
        EqualReceipts(er, sr);
        
        var sr' := BuildQueryReceipt(path.Subpath().Substitute(replacement), key);
        var er' := ReceiptDropFirst(r');
        assert er'.root == r'.root.children.mapp[r'.key] == r'.root.children.mapp[key];  // trigger
        calc {
          er'.root;
          r'.root.children.mapp[key];
          path.Substitute(replacement).children.mapp[key];
            { path.reveal_ReplacedChildren(); }
          path.Subpath().Substitute(replacement);
          sr'.root;
        }
        assert path.node.children.WF();  // trigger
        assert er'.root == sr'.root;
        EqualReceipts(er', sr');

        SubstituteReceiptEquivalence(path.Subpath(), replacement, key);
        assert r.ResultAt(1) == r'.ResultAt(1);

        assert r.Result() == r'.Result();  // Exciting conclusion
        assert INodeAt(path.node, key) == INodeAt(path.Substitute(replacement), key);
      }
    } else {
      assert INodeAt(path.node, key) == INodeAt(path.Substitute(replacement), key);
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

  lemma NoopSteps(v: Variables, v': Variables, lbl: TransitionLabel, step: Step)
    requires v.WF()
    requires v'.WF()
    requires NextStep(v, v', lbl, step)
    requires !step.PutStep?
    ensures I(v') == I(v)
  {
    match step {
      case QueryStep(receipt) => {
        assert Query(v, v', lbl, receipt);
        assert v' == v;
        assert I(v') == I(v);
      }
      case PutStep() => {
        assert false;
      }
      case QueryEndLsnStep() => {
        assert I(v') == I(v);
      }
      case FreezeAsStep(stampedBetree) => {
        assert I(v') == I(v);
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
        assume I(v') == I(v);
      }
    }
  }
}
