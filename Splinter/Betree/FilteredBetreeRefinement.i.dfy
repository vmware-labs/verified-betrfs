// Copyright 2018-2021 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, and University of Washington
// SPDX-License-Identifier: BSD-2-Clause

// include "PivotBetree.i.dfy"
include "FilteredBetree.i.dfy"
include "PivotBetreeRefinement.i.dfy"

module FilteredBetreeRefinement
{
  import opened Options
  import opened KeyType
  import opened StampedMod
  import TotalKMMapMod
  import opened ValueMessage
  import opened MsgHistoryMod
  import opened LSNMod
  import opened Sequences
  import opened Buffers
  import opened MemtableMod
  import opened Upperbounded_Lexicographic_Byte_Order_Impl
  import opened Upperbounded_Lexicographic_Byte_Order_Impl.Ord
  import opened BoundedPivotsLib
  import opened DomainMod
  import opened FilteredBetree
  import PivotBetree
  import PivotBetreeRefinement

  function ActiveBufferKeysForChild(node: BetreeNode, childIdx: nat, bufferIdx: nat) : iset<Key>
    requires node.WF()
    requires node.BetreeNode?
    requires childIdx < |node.children|
    requires bufferIdx < node.buffers.Length()
  {
    if node.activeBufferRanges[childIdx] <= bufferIdx 
    then node.DomainRoutedToChild(childIdx).KeySet()
    else iset{}
  }

  function ActiveBufferKeys(node: BetreeNode, bufferIdx: nat) : iset<Key>
    requires node.WF()
    requires node.BetreeNode?
    requires bufferIdx < node.buffers.Length()
  {
    iset k, i | 0 <= i < |node.children| && k in ActiveBufferKeysForChild(node, i, bufferIdx) :: k
  }

  function IBuffer(node: BetreeNode, bufferIdx: nat) : Buffer
    requires node.WF()
    requires node.BetreeNode?
    requires bufferIdx < node.buffers.Length()
  {
    node.buffers.buffers[bufferIdx].ApplyFilter(ActiveBufferKeys(node, bufferIdx))
  }

  function IBufferStack(node: BetreeNode) : BufferStack
    requires node.WF()
    requires node.BetreeNode?
  {
    BufferStack(seq (node.buffers.Length(), i requires 0 <= i < node.buffers.Length() => IBuffer(node, i)))
  }

  function IChildren(node: BetreeNode) : (out: seq<PivotBetree.BetreeNode>)
    requires node.WF()
    requires node.BetreeNode?
    decreases node, 0
  {
    assert WFChildren(node.children); // trigger
    seq (|node.children|, i requires 0 <= i < |node.children| => INode(node.children[i]))
  }

  function INode(node: BetreeNode) : (out: PivotBetree.BetreeNode)
    requires node.WF()
    ensures out.WF()
    ensures node.Nil? <==> out.Nil?
    decreases node, 1
  {
    var out := 
      if node.Nil?
      then PivotBetree.Nil
      else PivotBetree.BetreeNode(IBufferStack(node), node.pivotTable, IChildren(node));

    assert out.WF() by {
      forall i:nat |
        && out.ValidChildIndex(i)
        && out.children[i].BetreeNode?
        && out.children[i].LocalStructure()
        ensures out.children[i].MyDomain() == out.DomainRoutedToChild(i) {
          assert WFChildren(node.children); // trigger
          assert out.children[i] == IChildren(node)[i]; // trigger
          // assert out.DomainRoutedToChild(i) == node.DomainRoutedToChild(i);  // trigger
       }
    }
    out
  }

  function IStampedBetree(stampedBetree: StampedBetree) : PivotBetree.StampedBetree
    requires stampedBetree.value.WF()
  {
    Stamped(INode(stampedBetree.value), stampedBetree.seqEnd)
  }

  function ILbl(lbl: TransitionLabel) : PivotBetree.TransitionLabel
  {
    match lbl
      case QueryLabel(endLsn, key, value) => PivotBetree.QueryLabel(endLsn, key, value)
      case PutLabel(puts) => PivotBetree.PutLabel(puts)
      case QueryEndLsnLabel(endLsn) => PivotBetree.QueryEndLsnLabel(endLsn)
      case FreezeAsLabel(stampedBetree) => PivotBetree.FreezeAsLabel(
        if stampedBetree.value.WF()
        then IStampedBetree(stampedBetree)
        else PivotBetree.EmptyImage())
      case InternalLabel() => PivotBetree.InternalLabel()
  }

  function I(v: Variables) : PivotBetree.Variables
    requires v.WF()
  {
    PivotBetree.Variables(v.memtable, INode(v.root))
  }

  predicate Inv(v: Variables)
  {
    && v.WF()
    && (v.root.BetreeNode? ==> v.root.MyDomain() == TotalDomain())
  }

  // lemma InvNext(v: Variables, v': Variables, lbl: TransitionLabel)
  //   requires Inv(v)
  //   requires Next(v, v', lbl)
  //   ensures Inv(v')
  // {
  //   if v'.root.BetreeNode? {
  //     var step :| NextStep(v, v', lbl, step);
  //     if step.InternalSplitStep? {
  //       SubstitutePreservesWF(step.path, step.path.Target().SplitParent(step.request));
  //     } else if step.InternalFlushStep? {
  //       SubstitutePreservesWF(step.path, step.path.Target().Flush(step.childIdx));
  //     } else if step.InternalCompactStep? {
  //       var compactedNode := CompactedNode(step.path.Target(), step.compactedBuffers);
  //       SubstitutePreservesWF(step.path, compactedNode);
  //     }
  //   }
  //   assert v'.root.WF();  // trigger
  // }

  function IPath(path: Path) : (out: PivotBetree.Path)
    requires path.Valid()
  {
    PivotBetree.Path(INode(path.node), path.key, path.depth)
  }

  lemma SubpathCommutesWithIPath(path: Path) 
    requires path.Valid()
    requires 0 < path.depth
    ensures IPath(path.Subpath()) == IPath(path).Subpath()
  {
    calc {  // trigger
        IPath(Path(path.node.Child(path.key), path.key, path.depth-1));
        PivotBetree.Path(INode(path.node), path.key, path.depth).Subpath();
      }
  }

  lemma IPathValid(path: Path) 
    requires path.Valid()
    ensures IPath(path).Valid()
    decreases path.depth
  {
    if 0 < path.depth {
      SubpathCommutesWithIPath(path);
      IPathValid(path.Subpath());
      assert IPath(path).node == INode(path.node); // trigger
    }
  }

  function IReceiptLine(line: QueryReceiptLine) : PivotBetree.QueryReceiptLine
    requires line.WF()
  {
    PivotBetree.QueryReceiptLine(INode(line.node), line.result)
  }

  function IReceipt(receipt: QueryReceipt) : PivotBetree.QueryReceipt
    requires receipt.Valid()
  {
    PivotBetree.QueryReceipt(receipt.key, INode(receipt.root),
      seq(|receipt.lines|, i requires 0<=i<|receipt.lines| => IReceiptLine(receipt.lines[i])))
  }

  lemma IReceiptValid(receipt: QueryReceipt) 
    requires receipt.Valid()
    ensures IReceipt(receipt).Valid()
  {
    var ireceipt := IReceipt(receipt);
    var key := receipt.key;

    forall i:nat | i < |ireceipt.lines|-1 
      ensures ireceipt.lines[i].node.KeyInDomain(key)
      ensures ireceipt.ChildLinkedAt(i)
    {
      assert receipt.lines[i].node.KeyInDomain(key);  // trigger
      assert receipt.ChildLinkedAt(i);  // trigger
      ChildKeyCommutesWithI(receipt.lines[i].node, key);
    }
  
    forall i:nat | i < |ireceipt.lines| - 1 
    ensures ireceipt.ResultLinkedAt(i)
    {
      assert receipt.ResultLinkedAt(i);  // trigger
      var node := receipt.lines[i].node;
      var key := ireceipt.key;
      QueryCommutesWithIBufferStack(node, key, node.ActiveBuffersForKey(key), node.buffers.Length());
    }
  }

  lemma ChildKeyCommutesWithI(node: BetreeNode, key: Key)
    requires node.WF()
    requires node.KeyInDomain(key)
    ensures node.Child(key).WF()
    ensures INode(node.Child(key)) == INode(node).Child(key)
  {
  }

  lemma ActiveBuffersForKeyConsistent(node: BetreeNode, key: Key, start: nat)
    requires node.WF()
    requires node.KeyInDomain(key)
    requires start == node.ActiveBuffersForKey(key)
    ensures forall i:nat | i < start :: key !in ActiveBufferKeys(node, i)
    ensures forall i:nat | start <= i < node.buffers.Length() :: key in ActiveBufferKeys(node, i)
  {
    forall i:nat | start <= i < node.buffers.Length()
      ensures key in ActiveBufferKeys(node, i)
    {
      var childIdx := Route(node.pivotTable, key);
      assert key in ActiveBufferKeysForChild(node, childIdx, i); // trigger
    }
  }

  lemma QueryCommutesWithIBufferStack(node: BetreeNode, key: Key, start: nat, count: nat)
    requires IBufferStack.requires(node)
    requires node.KeyInDomain(key)
    requires count <= node.buffers.Length()
    requires start == node.ActiveBuffersForKey(key)
    ensures count <= start ==> (IBufferStack(node).QueryUpTo(key, count) == Update(NopDelta()))
    ensures start < count ==> (IBufferStack(node).QueryUpTo(key, count) == 
      node.buffers.Slice(start, node.buffers.Length()).QueryUpTo(key, count-start))
  {
    ActiveBuffersForKeyConsistent(node, key, start);
    if start < count || 0 < count {
      QueryCommutesWithIBufferStack(node, key, start, count-1);
    }
  }

  function IStepDefn(step: Step) : (out: PivotBetree.Step)
    requires step.WF()
  {
    match step {
      case QueryStep(receipt) => PivotBetree.QueryStep(IReceipt(receipt))
      case PutStep() => PivotBetree.PutStep()
      case QueryEndLsnStep() => PivotBetree.QueryEndLsnStep()
      case FreezeAsStep() => PivotBetree.FreezeAsStep()
      case InternalGrowStep() => PivotBetree.InternalGrowStep()
      case  InternalSplitStep(path, request) => PivotBetree.InternalSplitStep(IPath(path), request)
      case InternalFlushStep(path, childIdx, _) => PivotBetree.InternalFlushStep(IPath(path), childIdx)
      case InternalFlushMemtableStep() => PivotBetree.InternalFlushMemtableStep()
      case InternalCompactStep(path, compactStart, compactEnd, compactedBuffer) => (
        var buffers := IBufferStack(path.Target()).buffers;
        var compactedBuffers := BufferStack(buffers[..compactStart] + [compactedBuffer] + buffers[compactEnd..]);
        PivotBetree.InternalCompactStep(IPath(path), compactedBuffers)
      )
      case InternalNoOpStep() => PivotBetree.InternalNoOpStep()
    }
  }

  lemma IStepWF(step: Step)
    requires IStepDefn.requires(step)
    ensures IStepDefn(step).WF()
  {
    var istep := IStepDefn(step);
    match step {
      case QueryStep(receipt) => { IReceiptValid(receipt); }
      case InternalSplitStep(path, request) => { assume false; }//TargetCommutesWithI(path); }
      case InternalFlushStep(path, childIdx, _) => { assume false; }//TargetCommutesWithI(path); }
      case InternalCompactStep(path, compactStart, compactEnd, compactedBuffer) => { assume false; }//InternalCompactStepWF(step); }
      case _ => { assert istep.WF(); }
    }
  }

  function IStep(step: Step) : (out: PivotBetree.Step)
    requires step.WF()
    ensures out.WF()
  {
    IStepWF(step);
    IStepDefn(step)
  }

  lemma InitRefines(v: Variables, stampedBetree: StampedBetree)
    requires Init(v, stampedBetree)
    ensures PivotBetree.Init(I(v), IStampedBetree(stampedBetree))
  {
  }

//   lemma AllKeysInTotalDomain(key: Key)
//     ensures key in TotalDomain().KeySet()
//     ensures TotalDomain().Contains(key)
//   {
//     SmallestElementLte(Element(key));
//   }

//   lemma InternalGrowStepRefines(v: Variables, v': Variables, lbl: TransitionLabel, step: Step)
//     requires Inv(v)
//     requires NextStep(v, v', lbl, step)
//     requires step.InternalGrowStep?
//     ensures v'.WF()
//     ensures PagedBetree.NextStep(I(v), I(v'), ILbl(lbl), IStep(step))
//   {
//     INodeWF(v.root);
//     INodeWF(v'.root);
//     assert I(v').root.children.mapp.Keys == AllKeys();  // trigger
//     forall key:Key | AnyKey(key)
//       ensures I(v').root.Child(key)
//           == PagedBetree.ConstantChildMap(I(v).root).mapp[key] {
//       AllKeysInTotalDomain(key);
//       ChildCommutesWithI(v'.root, key);
//     }
//   }

//   lemma SubstitutePreservesWF(path: Path, target': BetreeNode)
//     requires path.Valid()
//     requires path.ValidReplacement(target')
//     ensures path.Substitute(target').WF()
//   {}

//   // Substitution followed by interpretation is the same as interpretation
//   // followed by paged-level substitution.
//   lemma SubstitutionRefines(path: Path, target': BetreeNode)
//     requires path.Valid()
//     requires path.ValidReplacement(target')
//     ensures path.Substitute(target').WF()
//     ensures IPath(path).Valid()
//     ensures INode(target').WF();
//     ensures INode(path.Substitute(target')) == IPath(path).Substitute(INode(target'));
//     decreases path.depth;
//   {
//     IPathValid(path);
//     SubstitutePreservesWF(path, target');
//     IPathValid(path);
//     INodeWF(target');
//     if path.depth==0 {
//       assert INode(path.Substitute(target')) == IPath(path).Substitute(INode(target'));
//     } else {
//       SubstitutionRefines(path.Subpath(), target');
//       forall key ensures
//         IChildren(path.Substitute(target')).mapp[key]
//         == IPath(path).ReplacedChildren(INode(target')).mapp[key] 
//       {
//         if key in path.node.KeySet() {
//           if Route(path.node.pivotTable, path.key) == Route(path.node.pivotTable, key) {
//             var replacedChild := IPath(path).Subpath().Substitute(INode(target'));
//             assert replacedChild == IPath(path).ReplacedChildren(INode(target')).mapp[key] by {
//               IPath(path).reveal_ReplacedChildren();  // protected in by clause to avoid timeout
//             }
//             SubpathCommutesWithIPath(path);
//           } else {
//             assert IPath(path).node.Child(key) == IPath(path).ReplacedChildren(INode(target')).mapp[key] by {
//               IPath(path).reveal_ReplacedChildren();  // protected in by clause to avoid timeout
//             }
//             ChildCommutesWithI(path.node, key);
//           }
//         } else {
//           assert PagedBetree.Nil == INode(path.node).Child(key);  // trigger
//           assert IPath(path).node.Child(key) == IPath(path).ReplacedChildren(INode(target')).mapp[key] by {
//             IPath(path).reveal_ReplacedChildren();  // protected in by clause to avoid timeout
//           }
//         }
//       }
//       assert INode(path.Substitute(target')) == IPath(path).Substitute(INode(target'));  // trigger
//     }
//   }

//   lemma TargetCommutesWithI(path: Path) 
//     requires path.Valid()
//     ensures IPath(path).Valid()  // prereq
//     ensures IPath(path).Target() == INode(path.Target())
//     decreases path.depth
//   {
//     IPathValid(path);
//     if 0 < path.depth {
//       TargetCommutesWithI(path.Subpath());
//       SubpathCommutesWithIPath(path);
//       assert IPath(path).Target() == INode(path.Target());
//     }
//   }

//   lemma SplitCommutesWithILeft(step: Step, key: Key)
//     requires step.InternalSplitStep?
//     requires step.WF()
//     requires key in SplitLeftKeys(step)
//     requires key in step.path.Target().KeySet()
//     ensures
//       var leftKeys := SplitLeftKeys(step);
//       var t := step.path.Target();
//       INode(t).Split(leftKeys, SplitChildKeys(step) - leftKeys).Child(key) == IChildren(t.SplitParent(step.request)).mapp[key];
//   {
//     var t := step.path.Target();
//     var childDom := t.DomainRoutedToChild(step.request.childIdx);
//     var leftDom := Domain(childDom.start, Element(step.SplitKey()));
//     var leftKeys := SplitLeftKeys(step);
//     var rightKeys := SplitChildKeys(step) - SplitLeftKeys(step);

//     assert leftDom.KeySet() == leftKeys by {
//       Keyspace.reveal_IsStrictlySorted();
//       Keyspace.lteTransitiveForall();
//     }
//     if step.request.SplitLeaf? {
//       assert INode(t.Child(key)).FilterBuffersAndChildren(leftDom.KeySet()).children == INode(t.Child(key).SplitLeaf(step.request.splitKey).0).children;  // trigger seq extensionality
//     } else {
//       assert INode(t.Child(key)).FilterBuffersAndChildren(leftDom.KeySet()).children == INode(t.Child(key).SplitIndex(step.request.childPivotIdx).0).children;  // trigger seq extensionality
//     }
//   }

//   lemma SplitCommutesWithIRight(step: Step, key: Key)
//     requires step.InternalSplitStep?
//     requires step.WF()
//     requires key in SplitChildKeys(step) - SplitLeftKeys(step)
//     requires key in step.path.Target().KeySet()
//     ensures
//       var leftKeys := SplitLeftKeys(step);
//       var t := step.path.Target();
//       INode(t).Split(leftKeys, SplitChildKeys(step) - leftKeys).Child(key) == IChildren(t.SplitParent(step.request)).mapp[key];
//   {
//     var t := step.path.Target();
//     var childDom := t.DomainRoutedToChild(step.request.childIdx);
//     var rightDom := Domain(Element(step.SplitKey()), childDom.end);
//     var leftKeys := SplitLeftKeys(step);
//     var rightKeys := SplitChildKeys(step) - leftKeys;

//     assert rightDom.KeySet() == rightKeys by {
//       Keyspace.reveal_IsStrictlySorted();
//       Keyspace.lteTransitiveForall();
//     }
//     if step.request.SplitLeaf? {
//       assert INode(t.Child(key)).FilterBuffersAndChildren(rightDom.KeySet()).children == INode(t.Child(key).SplitLeaf(step.request.splitKey).1).children;  // trigger seq extensionality
//     } else {
//       assert INode(t.Child(key)).FilterBuffersAndChildren(rightDom.KeySet()).children == INode(t.Child(key).SplitIndex(step.request.childPivotIdx).1).children;  // trigger seq extensionality
//     }
//   }

//   lemma SplitCommutesWithI(step: Step) 
//     requires step.InternalSplitStep?
//     requires step.WF()
//     ensures INode(step.path.Target()).Split(SplitLeftKeys(step), SplitChildKeys(step) - SplitLeftKeys(step)) == INode(step.path.Target().SplitParent(step.request))
//   {
//     var leftKeys := SplitLeftKeys(step);
//     var rightKeys := SplitChildKeys(step) - SplitLeftKeys(step);
//     var t := step.path.Target();

//     forall key | AnyKey(key)
//     ensures INode(t).Split(leftKeys, rightKeys).Child(key)
//       == IChildren(t.SplitParent(step.request)).mapp[key] 
//     {
//       if key in t.KeySet() {
//         if key in leftKeys {
//           SplitCommutesWithILeft(step, key);
//         } else if key in rightKeys {
//           SplitCommutesWithIRight(step, key);
//         }
//       }
//     }
//     assert PagedBetree.BetreeNode(t.buffers, IChildren(t)).Split(leftKeys, rightKeys).children.mapp.Keys
//         == IChildren(t.SplitParent(step.request)).mapp.Keys;  // triggers extensionality
//   }

//   lemma InternalSplitStepRefines(v: Variables, v': Variables, lbl: TransitionLabel, step: Step)
//     requires Inv(v)
//     requires NextStep(v, v', lbl, step)
//     requires step.InternalSplitStep?
//     ensures v'.WF()
//     ensures PagedBetree.NextStep(I(v), I(v'), ILbl(lbl), IStep(step))
//   {
//     INodeWF(v.root);
//     INodeWF(step.path.Target());
//     InvNext(v, v', lbl); //assert v'.WF();
//     INodeWF(v'.root);
//     IPathValid(step.path); //assert IPath(step.path).Valid();
//     TargetCommutesWithI(step.path);
//     SplitCommutesWithI(step);
//     SubstitutionRefines(step.path, step.path.Target().SplitParent(step.request));
//   }

//   lemma PromoteCommutesWithI(node: BetreeNode, domain: Domain)  
//     requires node.WF()
//     requires domain.WF()
//     requires domain.Domain?
//     ensures INode(node.Promote(domain)) == INode(node).Promote()
//   {
//     assert INode(node.Promote(domain)) == INode(node).Promote();  // trigger
//   }

//   lemma PushBufferCommutesWithI(node: BetreeNode, buffers: BufferStack) 
//     requires node.WF()
//     requires node.BetreeNode?
//     ensures INode(node.PushBufferStack(buffers)) == INode(node).PushBufferStack(buffers)
//   {
//     assert INode(node.PushBufferStack(buffers)).buffers == INode(node).PushBufferStack(buffers).buffers;  // trigger
//   }

//   // todo: this is duplicated in Journal/LinkedJournalRefinement
//   lemma CommuteTransitivity<L,H>(I: L->H, f: L->L, F: H->H, g: L->L, G: H->H)
//     requires forall x :: I(f(x))==F(I(x))
//     requires forall x :: I(g(x))==G(I(x))
//     ensures forall x :: I(g(f(x)))==G(F(I(x)))
//   {
//     // See Tony's phone cam picture of the proof that we wrote on the whiteboard
//     // but which dafny doesn't need; eyeroll
//   }
  
//   // TODO(tony): a much easier proof would be to condition on the nullity of node to factor out Promote()
//   lemma PromoteComposedWithPushCommutes(node: BetreeNode, promoteDomain: Domain, buffers: BufferStack)  
//     requires node.WF()
//     requires promoteDomain.WF()
//     requires promoteDomain.Domain?
//     ensures INode(node.Promote(promoteDomain).PushBufferStack(buffers)) 
//         == INode(node).Promote().PushBufferStack(buffers);
//   {
//     EmptyDomain.reveal_SaneKeys();
//     var dummy := EmptyRoot(promoteDomain);  // using promoteDomain as placeholder. It doesn't matter what domain is used
//     var idummy := PagedBetree.EmptyRoot();
//     var i := (n: BetreeNode) => if n.WF() && n.BetreeNode? then INode(n) else idummy;
//     var f := (n: BetreeNode) => if n.WF() then n.Promote(promoteDomain) else dummy;
//     var g := (n: BetreeNode) => if n.WF() && n.BetreeNode? then n.PushBufferStack(buffers) else dummy.PushBufferStack(buffers);  // this is a clever trick to use dummy.PushBufferStack(buffers), so that the commutativity aligns
//     var F := (pn: PagedBetree.BetreeNode) => if pn.WF() then pn.Promote() else idummy;
//     var G := (pn: PagedBetree.BetreeNode) => if pn.WF() && pn.BetreeNode? then pn.PushBufferStack(buffers) else idummy;

//     forall n ensures i(f(n)) == F(i(n))
//     {
//       if n.WF() {
//         PromoteCommutesWithI(n, promoteDomain);
//       } else {
//         PushBufferCommutesWithI(EmptyRoot(promoteDomain), buffers); 
//         assert IChildren(EmptyRoot(promoteDomain)) == PagedBetree.ConstantChildMap(PagedBetree.Nil);  // trigger
//       }
//     }
//     assert INode(f(node)) == F(INode(node));  // trigger
//     forall n ensures i(g(n)) == G(i(n))
//     {
//       if n.WF() && n.BetreeNode? {
//         calc {
//           INode(n.PushBufferStack(buffers));
//           { PushBufferCommutesWithI(n, buffers); }
//           INode(n).PushBufferStack(buffers);
//         }
//       } else {
//         PushBufferCommutesWithI(EmptyRoot(promoteDomain), buffers);
//         assert IChildren(EmptyRoot(promoteDomain)) == PagedBetree.ConstantChildMap(PagedBetree.Nil);
//       }
//     }
//     CommuteTransitivity(i, f, F, g, G);
//   }

//   lemma FlushCommutesWithI(step: Step) 
//     requires step.InternalFlushStep?
//     requires step.WF()
//     ensures INode(step.path.Target()).Flush(IStep(step).downKeys) == INode(step.path.Target().Flush(step.childIdx))
//   {
//     var t := step.path.Target();
//     var istep := IStep(step);
//     forall k | AnyKey(k) 
//     ensures INode(t.Flush(step.childIdx)).Child(k) == INode(t).Flush(istep.downKeys).Child(k)
//     {
//       if k in istep.downKeys {
//         assert t.KeyInDomain(k) by {
//           Keyspace.reveal_IsSorted();
//           Keyspace.lteTransitiveForall();
//         }
//         ChildCommutesWithI(t.Flush(step.childIdx), k);
//         var newBuffers := t.buffers.ApplyFilter(t.DomainRoutedToChild(step.childIdx).KeySet());
//         PromoteComposedWithPushCommutes(t.children[step.childIdx], t.DomainRoutedToChild(step.childIdx), newBuffers);
//       }
//     }
//     assert INode(step.path.Target()).Flush(IStep(step).downKeys) == INode(step.path.Target().Flush(step.childIdx));  // trigger
//   }

//   lemma InternalFlushStepRefines(v: Variables, v': Variables, lbl: TransitionLabel, step: Step)
//     requires Inv(v)
//     requires NextStep(v, v', lbl, step)
//     requires step.InternalFlushStep?
//     ensures v'.WF()
//     ensures PagedBetree.NextStep(I(v), I(v'), ILbl(lbl), IStep(step))
//   {
//     INodeWF(v.root);
//     INodeWF(step.path.Target());
//     InvNext(v, v', lbl); //assert v'.WF();
//     INodeWF(v'.root);
//     IPathValid(step.path); //assert IPath(step.path).Valid();
//     TargetCommutesWithI(step.path);
//     FlushCommutesWithI(step);
//     SubstitutionRefines(step.path, step.path.Target().Flush(step.childIdx));
//   }

//   predicate EquivalentBufferCompaction(node: BetreeNode, other: BetreeNode)
//   {
//     && node.WF()
//     && other.WF()
//     && node.BetreeNode?
//     && other.BetreeNode?
//     && node.buffers.Equivalent(other.buffers)
//     && node.pivotTable == other.pivotTable
//     && node.children == other.children
//   }

//   lemma BufferCompactionRefines(node: BetreeNode, other: BetreeNode)
//     requires EquivalentBufferCompaction(node, other)
//     ensures PagedBetreeRefinement.EquivalentBufferCompaction(INode(node), INode(other))
//   {}

//   lemma InternalCompactStepRefines(v: Variables, v': Variables, lbl: TransitionLabel, step: Step)
//     requires Inv(v)
//     requires NextStep(v, v', lbl, step)
//     requires step.InternalCompactStep?
//     ensures v'.WF()
//     ensures PagedBetree.NextStep(I(v), I(v'), ILbl(lbl), IStep(step))
//   {
//     INodeWF(v.root);
//     INodeWF(step.path.Target());
//     InvNext(v, v', lbl); //assert v'.WF();
//     INodeWF(v'.root);
//     IPathValid(step.path); //assert IPath(step.path).Valid();
//     var compactedNode := CompactedNode(step.path.Target(), step.compactedBuffers);
//     SubstitutionRefines(step.path, compactedNode);
//     BufferCompactionRefines(step.path.Target(), compactedNode);
//     TargetCommutesWithI(step.path);
//   }

  // lemma FreezeAsRefines(v: Variables, v': Variables, lbl: TransitionLabel, step: Step)
  //   requires Inv(v)
  //   requires NextStep(v, v', lbl, step)
  //   requires step.FreezeAsStep?
  //   ensures v'.WF()
  //   ensures PivotBetree.NextStep(I(v), I(v'), ILbl(lbl), IStep(step))
  // {
  //   assert INode(PushMemtable(v.root, v.memtable).value) == PivotBetree.PushMemtable(INode(v.root), v.memtable).value;
  // }

  // lemma InternalFlushMemtableStepRefines(v: Variables, v': Variables, lbl: TransitionLabel, step: Step)
  //   requires Inv(v)
  //   requires NextStep(v, v', lbl, step)
  //   requires step.InternalFlushMemtableStep?
  //   ensures v'.WF()
  //   ensures PivotBetree.NextStep(I(v), I(v'), ILbl(lbl), IStep(step))
  // {
  //   assert INode(PushMemtable(v.root, v.memtable).value) == PivotBetree.PushMemtable(INode(v.root), v.memtable).value;
  // }

  // lemma NextRefines(v: Variables, v': Variables, lbl: TransitionLabel)
  //   requires Inv(v)
  //   requires Next(v, v', lbl)
  //   ensures v'.WF()
  //   ensures PivotBetree.Next(I(v), I(v'), ILbl(lbl))
  // {
  //   InvNext(v, v', lbl);
  //   var step: Step :| NextStep(v, v', lbl, step);
  //   match step {
  //     case QueryStep(receipt) => {
  //       ValidReceiptRefines(step.receipt);
  //       assert PivotBetree.NextStep(I(v), I(v'), ILbl(lbl), IStep(step)); // trigger
  //     }
  //     case PutStep() => {
  //       assert PivotBetree.NextStep(I(v), I(v'), ILbl(lbl), IStep(step));
  //     }
  //     case QueryEndLsnStep() => {
  //       assert PivotBetree.NextStep(I(v), I(v'), ILbl(lbl), IStep(step));
  //     }
  //     case FreezeAsStep() => {
  //       INodeWF(v.root);
  //       FreezeAsRefines(v, v', lbl, step);
  //       assert PivotBetree.NextStep(I(v), I(v'), ILbl(lbl), IStep(step)); 
  //     }
  //     case InternalGrowStep() => {
  //       InternalGrowStepRefines(v, v', lbl, step);
  //     }
  //     case InternalSplitStep(_, _) => {
  //       InternalSplitStepRefines(v, v', lbl, step);
  //       assert PivotBetree.NextStep(I(v), I(v'), ILbl(lbl), IStep(step));
  //     }
  //     case InternalFlushStep(_, _) => {
  //       InternalFlushStepRefines(v, v', lbl, step);
  //       assert PivotBetree.NextStep(I(v), I(v'), ILbl(lbl), IStep(step));
  //     }
  //     case InternalFlushMemtableStep() => {
  //       InternalFlushMemtableStepRefines(v, v', lbl, step);
  //       assert PivotBetree.NextStep(I(v), I(v'), ILbl(lbl), IStep(step));
  //     }
  //     case InternalCompactStep(_, _) => {
  //       InternalCompactStepRefines(v, v', lbl, step);
  //       assert PivotBetree.NextStep(I(v), I(v'), ILbl(lbl), IStep(step));
  //     }
  //     case InternalNoOpStep() => 
  //        assert PivotBetree.NextStep(I(v), I(v'), ILbl(lbl), IStep(step));
  //   }
  // }
}
