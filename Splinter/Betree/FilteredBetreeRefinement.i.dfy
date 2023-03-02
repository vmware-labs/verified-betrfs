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
  import opened BufferMod
  import opened BufferSeqMod
  import opened MemtableMod
  import opened Upperbounded_Lexicographic_Byte_Order_Impl
  import opened Upperbounded_Lexicographic_Byte_Order_Impl.Ord
  import opened BoundedPivotsLib
  import opened DomainMod
  import opened FilteredBetree
  import PivotBetree
  import PivotBetreeRefinement

  function IBuffer(node: BetreeNode, bufferIdx: nat) : Buffer
    requires node.WF()
    requires node.BetreeNode?
    requires bufferIdx < node.buffers.Length()
  {
    node.buffers.buffers[bufferIdx].ApplyFilter(node.ActiveBufferKeys(bufferIdx))
  }

  function IBufferSeq(node: BetreeNode) : BufferSeq
    requires node.WF()
    requires node.BetreeNode?
  {
    BufferSeq(seq (node.buffers.Length(), i requires 0 <= i < node.buffers.Length() => IBuffer(node, i)))
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
      else PivotBetree.BetreeNode(IBufferSeq(node), node.pivotTable, IChildren(node));

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

  lemma InvNext(v: Variables, v': Variables, lbl: TransitionLabel)
    requires Inv(v)
    requires Next(v, v', lbl)
    ensures Inv(v')
  {
    if v'.root.BetreeNode? {
      var step :| NextStep(v, v', lbl, step);
      match step {
        case InternalSplitStep(path, request) => { 
          SubstitutePreservesWF(path, path.Target().SplitParent(request)); }
        case InternalFlushStep(path, childIdx, bufferGCCount) => { 
          SubstitutePreservesWF(path, path.Target().Flush(childIdx, bufferGCCount)); }
        case InternalCompactStep(path, compactStart, compactEnd, compactedBuffer) => { 
          SubstitutePreservesWF(path, CompactedNode(path.Target(), compactStart, compactEnd, compactedBuffer)); }
        case _ => { assert v'.root.WF(); }
      }
    }
  }

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

  lemma TargetCommutesWithI(path: Path)
    requires path.Valid()
    ensures IPath(path).Valid()
    ensures IPath(path).Target() == INode(path.Target())
    decreases path.depth
  {
    IPathValid(path);
    if 0 < path.depth {
      SubpathCommutesWithIPath(path);
      TargetCommutesWithI(path.Subpath());
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

      assume false;
      // QueryCommutesWithIBufferSeq(node, key, node.buffers.Length());
    }
  }

  lemma ChildKeyCommutesWithI(node: BetreeNode, key: Key)
    requires node.WF()
    requires node.KeyInDomain(key)
    ensures node.Child(key).WF()
    ensures INode(node.Child(key)) == INode(node).Child(key)
  {
  }

  lemma ActiveBuffersForKeyConsistent(node: BetreeNode, key: Key)
    requires node.WF()
    requires node.KeyInDomain(key)
    ensures forall i:nat | i < node.ActiveBuffersForKey(key) :: key in node.ActiveBufferKeys(i)
    ensures forall i:nat | node.ActiveBuffersForKey(key) <= i < node.buffers.Length() :: key !in node.ActiveBufferKeys(i)
  {
    forall i:nat | i < node.ActiveBuffersForKey(key)
      ensures key in node.ActiveBufferKeys(i)
    {
      var childIdx := Route(node.pivotTable, key);
      assert key in node.ActiveBufferKeysForChild(childIdx, i); // trigger
    }
  }

  // lemma QueryCommutesWithIBufferSeq(node: BetreeNode, key: Key, start: nat)
  //   requires IBufferSeq.requires(node)
  //   requires node.KeyInDomain(key)
  //   requires start <= node.buffers.Length()
  //   ensures var end := node.ActiveBuffersForKey(key);
  //     && (count > end ==> IBufferSeq(node).QueryUpTo(key, count) == Merge(node.buffers.QueryUpTo(key, end), Update(NopDelta())))
  //     && (count <= end ==> IBufferSeq(node).QueryUpTo(key, count) == node.buffers.QueryUpTo(key, count))
  // {
  //   // ActiveBuffersForKeyConsistent(node, key);
  //   // if 0 < count {
  //   //   QueryCommutesWithIBufferSeq(node, key, count-1);
  //   // }
  // }

  // lemma QueryFromEquivalent(a: BufferSeq, b: BufferSeq, key: Key, start: nat)
  //   requires count <= |a.buffers|
  //   requires count <= |b.buffers|
  //   requires forall i:nat | i < count :: a.buffers[i].Query(key) == b.buffers[i].Query(key)
  //   ensures a.QueryUpTo(key, count) == b.QueryUpTo(key, count)
  // {
  //   if count > 0 {
  //     QueryUpToEquivalent(a, b, key, count-1);
  //   }
  // }

  // lemma BufferSeqQueryAdditive(left: BufferSeq, right: BufferSeq, key: Key, count: nat)
  //   requires count <= |left.buffers| + |right.buffers|
  //   ensures 
  //     && var out := BufferSeq(left.buffers + right.buffers);
  //     && (count <= |left.buffers| ==> out.QueryUpTo(key, count) == left.QueryUpTo(key, count))
  //     && (|left.buffers| < count ==> out.QueryUpTo(key, count) == Merge(left.Query(key), right.QueryUpTo(key, count-|left.buffers|)))
  // {
  //   var out := BufferSeq(left.buffers + right.buffers);
  //   if count <= |left.buffers| {
  //     QueryUpToEquivalent(out, left, key, count);
  //   } else {
  //     BufferSeqQueryAdditive(left, right, key, count-1);
  //   }
  // }

  // lemma CompactedQueryEquivalence(a: BufferSeq, start: nat, end: nat, compacted: Buffer, key: Key, count: nat) 
  //   requires start < end <= a.Length()
  //   requires count <= a.Length()
  //   requires a.Slice(start, end).Equivalent(BufferSeq([compacted]))
  //   ensures var out := BufferSeq(a.buffers[..start] + [compacted] + a.buffers[end..]);
  //     && (count >= end ==> a.QueryUpTo(key, count) == out.QueryUpTo(key, count-end+start+1))
  //     && (count <= start ==> a.QueryUpTo(key, count) == out.QueryUpTo(key, count))
  // {
  //   if count == 0 { return; }

  //   if count > end {
  //     CompactedQueryEquivalence(a, start, end, compacted, key, count-1);
  //   } else if count > start {
  //     if (count == end) {
  //       assert a.Slice(start, end).Equivalent(BufferSeq([compacted]));
  //       assert a.Slice(start, end).Query(key) == BufferSeq([compacted]).Query(key); // trigger
  //       CompactedQueryEquivalence(a, start, end, compacted, key, start);
        
  //       var out := BufferSeq(a.buffers[..start] + [compacted] + a.buffers[end..]);
  //       BufferSeqQueryAdditive(BufferSeq(a.buffers[..start]), a.Slice(start, end), key, end);
  //       BufferSeqQueryAdditive(BufferSeq(a.buffers[..start]), BufferSeq([compacted]), key, start+1);

  //       assert a.buffers[..start] + a.buffers[start..end] == a.buffers[..end];
  //       assert BufferSeq(a.buffers[..end]).Query(key) == BufferSeq(out.buffers[..start+1]).Query(key); // trigger

  //       QueryUpToEquivalent(BufferSeq(a.buffers[..end]), a, key, count);
  //       QueryUpToEquivalent(BufferSeq(out.buffers[..start+1]), out, key, start+1);
  //     }
  //   } else {
  //     CompactedQueryEquivalence(a, start, end, compacted, key, count-1);
  //   }
  // }

  // lemma CompactedBufferEquivalent(node: BetreeNode, start: nat, end: nat, compacted: Buffer)
  //   requires node.ActiveBufferSlice.requires(start, end)
  //   requires node.ActiveBufferSlice(start, end).Equivalent(BufferSeq([compacted]))
  //   ensures INode(node).buffers.Slice(start, end).Equivalent(BufferSeq([compacted]))
  // {
  //   assert node.ActiveBufferSlice(start, end) == INode(node).buffers.Slice(start, end); // trigger
  // }

  function IStepDefn(step: Step) : (out: PivotBetree.Step)
    requires step.WF()
  {
    match step {
      case QueryStep(receipt) => PivotBetree.QueryStep(IReceipt(receipt))
      case PutStep() => PivotBetree.PutStep()
      case QueryEndLsnStep() => PivotBetree.QueryEndLsnStep()
      case FreezeAsStep() => PivotBetree.FreezeAsStep()
      case InternalGrowStep() => PivotBetree.InternalGrowStep()
      case InternalSplitStep(path, request) => PivotBetree.InternalSplitStep(IPath(path), request)
      case InternalFlushStep(path, childIdx, _) => PivotBetree.InternalFlushStep(IPath(path), childIdx)
      case InternalFlushMemtableStep() => PivotBetree.InternalFlushMemtableStep()
      case InternalCompactStep(path, compactStart, compactEnd, compactedBuffer) => (
        var buffers := IBufferSeq(path.Target()).buffers;
        var compactedBuffers := BufferSeq(buffers[..compactStart] + [compactedBuffer] + buffers[compactEnd..]);
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
      case InternalSplitStep(path, request) => {
        TargetCommutesWithI(path);
        var child := path.Target().children[request.childIdx];
        var ichild := istep.path.Target().children[request.childIdx];

        assert INode(child) == ichild;
        assert ichild.children == IChildren(child);
      }
      case InternalFlushStep(path, childIdx, _) => { TargetCommutesWithI(path); }
      case InternalCompactStep(path, compactStart, compactEnd, compactedBuffer) => { 
        TargetCommutesWithI(path);

        var ibuffers := IBufferSeq(path.Target()); // og buffers
        var icompactedBuffers := BufferSeq(ibuffers.buffers[..compactStart] + [compactedBuffer] + ibuffers.buffers[compactEnd..]); // compacted buffers

        assume false;
        // CompactedBufferEquivalent(path.Target(), compactStart, compactEnd, compactedBuffer);
        // assert ibuffers.Slice(compactStart, compactEnd).Equivalent(BufferSeq([compactedBuffer]));

        // forall k | AnyKey(k)
        //   ensures ibuffers.Query(k) == icompactedBuffers.Query(k) 
        // {
        //   CompactedQueryEquivalence(ibuffers, compactStart, compactEnd, compactedBuffer, k, ibuffers.Length());
        // }
      }
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

  lemma AllKeysInTotalDomain(key: Key)
    ensures key in TotalDomain().KeySet()
    ensures TotalDomain().Contains(key)
  {
    SmallestElementLte(Element(key));
  }

  lemma InternalGrowStepRefines(v: Variables, v': Variables, lbl: TransitionLabel, step: Step)
    requires Inv(v)
    requires NextStep(v, v', lbl, step)
    requires step.InternalGrowStep?
    ensures v'.WF()
    ensures PivotBetree.NextStep(I(v), I(v'), ILbl(lbl), IStep(step))
  {
    assert I(v').root == INode(v'.root); // trigger
  }

  lemma SubstitutePreservesWF(path: Path, target': BetreeNode)
    requires path.Valid()
    requires path.ValidReplacement(target')
    ensures path.Substitute(target').WF()
  {}

  // Substitution followed by interpretation is the same as interpretation
  // followed by paged-level substitution.
  lemma SubstitutionRefines(path: Path, target': BetreeNode)
    requires path.Valid()
    requires path.ValidReplacement(target')
    ensures path.Substitute(target').WF()
    ensures IPath(path).Valid()
    ensures INode(target').WF();
    ensures INode(path.Substitute(target')) == IPath(path).Substitute(INode(target'));
    decreases path.depth;
  {
    assume false;
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
  }

  lemma SplitLeafCommutesWithI(node: BetreeNode, key: Key)
    requires node.SplitLeaf.requires(key)
    ensures INode(node.SplitLeaf(key).0) == INode(node).SplitLeaf(key).0
    ensures INode(node.SplitLeaf(key).1) == INode(node).SplitLeaf(key).1
  {
    var (left, right) := node.SplitLeaf(key);
    var (ileft, iright) := INode(node).SplitLeaf(key);

    forall i | 0 <= i < ileft.buffers.Length()
      ensures IBuffer(left, i) == ileft.buffers.buffers[i]
    {
      assert left.ActiveBufferKeys(i) == left.ActiveBufferKeysForChild(0, i); // trigger
      assert node.ActiveBufferKeys(i) == node.ActiveBufferKeysForChild(0, i); // trigger

      forall k | k in left.ActiveBufferKeys(i)
        ensures k in node.ActiveBufferKeys(i) {
        assert node.MyDomain().Contains(k) by {
          Keyspace.lteTransitiveForall();
        }
      }
      assert IBuffer(left, i) == ileft.buffers.buffers[i];
    }

    forall i | 0 <= i < iright.buffers.Length()
      ensures IBuffer(right, i) == iright.buffers.buffers[i]
    {
      assert right.ActiveBufferKeys(i) == right.ActiveBufferKeysForChild(0, i); // trigger
      assert node.ActiveBufferKeys(i) == node.ActiveBufferKeysForChild(0, i); // trigger

      forall k | k in right.ActiveBufferKeys(i)
        ensures k in node.ActiveBufferKeys(i) {
        assert node.MyDomain().Contains(k) by {
          Keyspace.lteTransitiveForall();
        }
      }
      assert IBuffer(right, i) == iright.buffers.buffers[i];
    }
  }

  lemma SplitIndexCommutesWithILeft(node: BetreeNode, pivotIdx: nat)
    requires node.SplitIndex.requires(pivotIdx)
    ensures INode(node.SplitIndex(pivotIdx).0) == INode(node).SplitIndex(pivotIdx).0
  {
     var (left, _) := node.SplitIndex(pivotIdx);
    var (ileft, _) := INode(node).SplitIndex(pivotIdx);

    var splitElt := INode(node).pivotTable[pivotIdx];
    var leftFilter := Domain(INode(node).MyDomain().start, splitElt);

    forall i | 0 <= i < ileft.buffers.Length()
      ensures IBuffer(left, i) == ileft.buffers.buffers[i]
    {
      forall k 
        ensures k in IBuffer(left, i).mapp <==> k in ileft.buffers.buffers[i].mapp 
      {
        if k in IBuffer(left, i).mapp && k !in ileft.buffers.buffers[i].mapp {
          var childIdx :| 0 <= childIdx < |left.children| && k in left.ActiveBufferKeysForChild(childIdx, i);

          assert childIdx < pivotIdx;
          assert k in node.ActiveBufferKeysForChild(childIdx, i); // trigger
          assert node.DomainRoutedToChild(childIdx).Contains(k);

          assert Keyspace.lte(node.pivotTable[childIdx], Element(k));
          assert Keyspace.lt(Element(k), node.pivotTable[childIdx+1]);
          assert leftFilter.Contains(k) by {  Keyspace.reveal_IsStrictlySorted(); Keyspace.lteTransitiveForall(); }
          assert false;
        }

        if k !in IBuffer(left, i).mapp && k in ileft.buffers.buffers[i].mapp {
          assert leftFilter.Contains(k);
          assert k in INode(node).buffers.buffers[i].mapp;
          assert k in node.buffers.buffers[i].mapp;
          assert k in node.ActiveBufferKeys(i);

          var childIdx :| 0 <= childIdx < |node.children| && k in node.ActiveBufferKeysForChild(childIdx, i);

          if childIdx < |ileft.children| {
            assert k in left.ActiveBufferKeysForChild(childIdx, i);
            assert false;
          } else {
            Keyspace.reveal_IsStrictlySorted();
            Keyspace.lteTransitiveForall();
            assert false;
          }
        }
      }
    }
  }

  lemma SplitIndexCommutesWithIRight(node: BetreeNode, pivotIdx: nat)
    requires node.SplitIndex.requires(pivotIdx)
    ensures INode(node.SplitIndex(pivotIdx).1) == INode(node).SplitIndex(pivotIdx).1
  {
    var (_, right) := node.SplitIndex(pivotIdx);
    var (_, iright) := INode(node).SplitIndex(pivotIdx);

    var splitElt := INode(node).pivotTable[pivotIdx];
    var rightFilter := Domain(splitElt, INode(node).MyDomain().end);

    forall i | 0 <= i < iright.buffers.Length()
      ensures IBufferSeq(right).buffers[i] == iright.buffers.buffers[i]
    {
      forall k 
        ensures k in IBuffer(right, i).mapp <==> k in iright.buffers.buffers[i].mapp 
      {
        if k in IBuffer(right, i).mapp && k !in iright.buffers.buffers[i].mapp {
          var childIdx :| 0 <= childIdx < |right.children| && k in right.ActiveBufferKeysForChild(childIdx, i);
          var nodeIdx := childIdx+pivotIdx;

          assert k in node.ActiveBufferKeysForChild(nodeIdx, i); // trigger
          assert node.DomainRoutedToChild(nodeIdx).Contains(k);

          assert Keyspace.lte(node.pivotTable[nodeIdx], Element(k));
          assert Keyspace.lt(Element(k), node.pivotTable[nodeIdx+1]);

          assert rightFilter.Contains(k) by { Keyspace.reveal_IsStrictlySorted(); Keyspace.lteTransitiveForall();}
          assert false;
        }

        if k !in IBuffer(right, i).mapp && k in iright.buffers.buffers[i].mapp {
          assert rightFilter.Contains(k);
          assert k in INode(node).buffers.buffers[i].mapp;
          assert k in node.buffers.buffers[i].mapp;
          assert k in node.ActiveBufferKeys(i);

          var childIdx :| 0 <= childIdx < |node.children| && k in node.ActiveBufferKeysForChild(childIdx, i);

          if childIdx >= pivotIdx {
            assert k in right.ActiveBufferKeysForChild(childIdx-pivotIdx, i);
            assert false;
          } else {
            Keyspace.reveal_IsStrictlySorted();
            Keyspace.lteTransitiveForall();
            assert false;
          }
        }
      }
    }
  }

  lemma SplitCommutesWithI(step: Step) 
    requires step.InternalSplitStep?
    requires step.WF()
    requires INode(step.path.Target()).CanSplitParent(step.request)
    ensures INode(step.path.Target().SplitParent(step.request)) == INode(step.path.Target()).SplitParent(step.request);
  {
    IPathValid(step.path);
    TargetCommutesWithI(step.path);

    var node := step.path.Target();
    var inode := INode(step.path.Target());
    assert node.pivotTable == inode.pivotTable;

    var parent := node.SplitParent(step.request);
    var iparent := inode.SplitParent(step.request);

    var childIdx := step.request.childIdx;
    assert WFChildren(node.children); // trigger
    assert PivotBetree.WFChildren(inode.children); // trigger
    assert INode(node.children[childIdx]) == inode.children[childIdx];
    assert parent.pivotTable == iparent.pivotTable;

    forall i | 0 <= i < |parent.children| 
      ensures INode(parent.children[i]) == iparent.children[i]
    {
      if i < childIdx {
      } else if i <= childIdx + 1 {
        if step.request.SplitLeaf? {
          SplitLeafCommutesWithI(node.children[childIdx], step.request.splitKey);
        } else {
          SplitIndexCommutesWithILeft(node.children[childIdx], step.request.childPivotIdx);
          SplitIndexCommutesWithIRight(node.children[childIdx], step.request.childPivotIdx);
        }
      } else {
        assert parent.children[i] == node.children[i-1];
      }
    }

    forall i | 0 <= i < parent.buffers.Length()
      ensures IBuffer(parent, i) == iparent.buffers.buffers[i]
    {
      assert parent.buffers.buffers[i] == node.buffers.buffers[i];
      assert IBuffer(node, i) == iparent.buffers.buffers[i];

      // TODO(jialin): prove
      assume IBuffer(parent, i) == IBuffer(node, i);
    }
  }

  lemma InternalSplitStepRefines(v: Variables, v': Variables, lbl: TransitionLabel, step: Step)
    requires Inv(v)
    requires NextStep(v, v', lbl, step)
    requires step.InternalSplitStep?
    ensures v'.WF()
    ensures PivotBetree.NextStep(I(v), I(v'), ILbl(lbl), IStep(step))
  {
    InvNext(v, v', lbl); //assert v'.WF();
    IPathValid(step.path); //assert IPath(step.path).Valid();
    TargetCommutesWithI(step.path);

    assert IStep(step).WF(); // trigger
    SplitCommutesWithI(step);
    SubstitutionRefines(step.path, step.path.Target().SplitParent(step.request)); 
    assert PivotBetree.InternalSplit(I(v), I(v'), ILbl(lbl), IStep(step));
  }

  lemma PromoteCommutesWithI(node: BetreeNode, domain: Domain)  
    requires node.WF()
    requires domain.WF()
    requires domain.Domain?
    ensures INode(node.Promote(domain)) == INode(node).Promote(domain)
  {
    assert INode(node.Promote(domain)) == INode(node).Promote(domain);  // trigger
  }

  lemma ActiveBufferKeysAfterExtendBufferSeq(node: BetreeNode, buffers: BufferSeq, bufferIdx: nat)
    requires node.WF()
    requires node.BetreeNode?
    requires bufferIdx < node.buffers.Length()
    ensures node.ExtendBufferSeq(buffers).ActiveBufferKeys(bufferIdx) == node.ActiveBufferKeys(bufferIdx)
  {
    forall i | 0 <= i < |node.children| 
      ensures node.ExtendBufferSeq(buffers).ActiveBufferKeysForChild(i, bufferIdx)
        == node.ActiveBufferKeysForChild(i, bufferIdx)
    {}
  }

  lemma ExtendBufferCommutesWithI(node: BetreeNode, buffers: BufferSeq) 
    requires node.WF()
    requires node.BetreeNode?
    requires buffers.ApplyFilter(node.KeySet()) == buffers // buffers must be within node's domain
    ensures INode(node.ExtendBufferSeq(buffers)) == INode(node).ExtendBufferSeq(buffers)
  {
    var node_a := INode(node.ExtendBufferSeq(buffers));
    var node_b := INode(node).ExtendBufferSeq(buffers);

    assert IChildren(node.ExtendBufferSeq(buffers)) == IChildren(node); // trigger
    assert node_a.children == node_b.children;
    assert node_a.buffers.Length() == node_b.buffers.Length();

    forall i | 0 <= i < node_a.buffers.Length() 
      ensures node_a.buffers.buffers[i] == node_b.buffers.buffers[i] 
    {
      if i < node.buffers.Length() {
        ActiveBufferKeysAfterExtendBufferSeq(node, buffers, i);
      } else {
        var idx := i-node.buffers.Length();
        forall k | k in buffers.buffers[idx].mapp 
          ensures k in IBuffer(node.ExtendBufferSeq(buffers), i).mapp
        {
          var childIdx := Route(node.pivotTable, k);
          assert k in node.ExtendBufferSeq(buffers).ActiveBufferKeysForChild(childIdx, i);
        }
      }
    }
  }

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
//   lemma PromoteComposedWithPushCommutes(node: BetreeNode, promoteDomain: Domain, buffers: BufferSeq)  
//     requires node.WF()
//     requires promoteDomain.WF()
//     requires promoteDomain.Domain?
//     ensures INode(node.Promote(promoteDomain).ExtendBufferSeq(buffers)) 
//         == INode(node).Promote().ExtendBufferSeq(buffers);
//   {
//     EmptyDomain.reveal_SaneKeys();
//     var dummy := EmptyRoot(promoteDomain);  // using promoteDomain as placeholder. It doesn't matter what domain is used
//     var idummy := PagedBetree.EmptyRoot();
//     var i := (n: BetreeNode) => if n.WF() && n.BetreeNode? then INode(n) else idummy;
//     var f := (n: BetreeNode) => if n.WF() then n.Promote(promoteDomain) else dummy;
//     var g := (n: BetreeNode) => if n.WF() && n.BetreeNode? then n.ExtendBufferSeq(buffers) else dummy.ExtendBufferSeq(buffers);  // this is a clever trick to use dummy.ExtendBufferSeq(buffers), so that the commutativity aligns
//     var F := (pn: PagedBetree.BetreeNode) => if pn.WF() then pn.Promote() else idummy;
//     var G := (pn: PagedBetree.BetreeNode) => if pn.WF() && pn.BetreeNode? then pn.ExtendBufferSeq(buffers) else idummy;

//     forall n ensures i(f(n)) == F(i(n))
//     {
//       if n.WF() {
//         PromoteCommutesWithI(n, promoteDomain);
//       } else {
//         ExtendBufferCommutesWithI(EmptyRoot(promoteDomain), buffers); 
//         assert IChildren(EmptyRoot(promoteDomain)) == PagedBetree.ConstantChildMap(PagedBetree.Nil);  // trigger
//       }
//     }
//     assert INode(f(node)) == F(INode(node));  // trigger
//     forall n ensures i(g(n)) == G(i(n))
//     {
//       if n.WF() && n.BetreeNode? {
//         calc {
//           INode(n.ExtendBufferSeq(buffers));
//           { ExtendBufferCommutesWithI(n, buffers); }
//           INode(n).ExtendBufferSeq(buffers);
//         }
//       } else {
//         ExtendBufferCommutesWithI(EmptyRoot(promoteDomain), buffers);
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

  lemma InternalFlushStepRefines(v: Variables, v': Variables, lbl: TransitionLabel, step: Step)
    requires Inv(v)
    requires NextStep(v, v', lbl, step)
    requires step.InternalFlushStep?
    ensures v'.WF()
    ensures PivotBetree.NextStep(I(v), I(v'), ILbl(lbl), IStep(step))
  {
    assume false;
    // INodeWF(v.root);
    // INodeWF(step.path.Target());
    // InvNext(v, v', lbl); //assert v'.WF();
    // INodeWF(v'.root);
    // IPathValid(step.path); //assert IPath(step.path).Valid();
    // TargetCommutesWithI(step.path);
    // FlushCommutesWithI(step);
    // SubstitutionRefines(step.path, step.path.Target().Flush(step.childIdx));
  }

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

  lemma InternalCompactStepRefines(v: Variables, v': Variables, lbl: TransitionLabel, step: Step)
    requires Inv(v)
    requires NextStep(v, v', lbl, step)
    requires step.InternalCompactStep?
    ensures v'.WF()
    ensures PivotBetree.NextStep(I(v), I(v'), ILbl(lbl), IStep(step))
  {
    assume false;
//     INodeWF(v.root);
//     INodeWF(step.path.Target());
//     InvNext(v, v', lbl); //assert v'.WF();
//     INodeWF(v'.root);
//     IPathValid(step.path); //assert IPath(step.path).Valid();
//     var compactedNode := CompactedNode(step.path.Target(), step.compactedBuffers);
//     SubstitutionRefines(step.path, compactedNode);
//     BufferCompactionRefines(step.path.Target(), compactedNode);
//     TargetCommutesWithI(step.path);
  }

  lemma InternalFlushMemtableStepRefines(v: Variables, v': Variables, lbl: TransitionLabel, step: Step)
    requires Inv(v)
    requires NextStep(v, v', lbl, step)
    requires step.InternalFlushMemtableStep?
    ensures v'.WF()
    ensures PivotBetree.NextStep(I(v), I(v'), ILbl(lbl), IStep(step))
  {
    var node := v.root.Promote(TotalDomain());
    assert node.MyDomain() == TotalDomain();

    var buffers := BufferSeq([v.memtable.buffer]);
    forall i | 0 <= i < buffers.Length() 
      ensures buffers.ApplyFilter(node.KeySet()).buffers[i] == buffers.buffers[i]
    {
      assert buffers.ApplyFilter(node.KeySet()).buffers[i] == buffers.buffers[i].ApplyFilter(node.KeySet());
      if exists k :: k in buffers.buffers[i].mapp && k !in node.KeySet() {
        var k :| k in buffers.buffers[i].mapp && k !in node.KeySet();
        AllKeysInTotalDomain(k);
        assert false;
      }
    } 
    ExtendBufferCommutesWithI(node, buffers);
  }

  lemma NextRefines(v: Variables, v': Variables, lbl: TransitionLabel)
    requires Inv(v)
    requires Next(v, v', lbl)
    ensures v'.WF()
    ensures PivotBetree.Next(I(v), I(v'), ILbl(lbl))
  {
    InvNext(v, v', lbl);
    var step: Step :| NextStep(v, v', lbl, step);
    match step {
      case QueryStep(receipt) => {
        assert PivotBetree.NextStep(I(v), I(v'), ILbl(lbl), IStep(step));
      }
      case PutStep() => {
        assert PivotBetree.NextStep(I(v), I(v'), ILbl(lbl), IStep(step));
      }
      case QueryEndLsnStep() => {
        assert PivotBetree.NextStep(I(v), I(v'), ILbl(lbl), IStep(step));
      }
      case FreezeAsStep() => {
        assert PivotBetree.NextStep(I(v), I(v'), ILbl(lbl), IStep(step)); 
      }
      case InternalGrowStep() => {
        InternalGrowStepRefines(v, v', lbl, step);
        assert PivotBetree.NextStep(I(v), I(v'), ILbl(lbl), IStep(step));
      }
      case InternalSplitStep(_, _) => {
        InternalSplitStepRefines(v, v', lbl, step);
        assert PivotBetree.NextStep(I(v), I(v'), ILbl(lbl), IStep(step));
      }
      case InternalFlushStep(_, _, _) => {
        InternalFlushStepRefines(v, v', lbl, step);
        assert PivotBetree.NextStep(I(v), I(v'), ILbl(lbl), IStep(step));
      }
      case InternalFlushMemtableStep() => {
        InternalFlushMemtableStepRefines(v, v', lbl, step);
        assert PivotBetree.NextStep(I(v), I(v'), ILbl(lbl), IStep(step));
      }
      case InternalCompactStep(_, _, _, _) => {
        InternalCompactStepRefines(v, v', lbl, step);
        assert PivotBetree.NextStep(I(v), I(v'), ILbl(lbl), IStep(step));
      }
      case InternalNoOpStep() => 
         assert PivotBetree.NextStep(I(v), I(v'), ILbl(lbl), IStep(step));
    }
  }
}
