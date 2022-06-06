// Copyright 2018-2021 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, and University of Washington
// SPDX-License-Identifier: BSD-2-Clause

include "PivotBetree.i.dfy"

module PivotBetreeRefinement
{
  import opened Options
  import opened KeyType
  import opened StampedMapMod
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
  import opened PivotBetree
  import PagedBetree

  function IChildren(node: BetreeNode) : PagedBetree.ChildMap
    requires node.WF()
    requires node.BetreeNode?
    decreases node, 0
  {
    PagedBetree.ChildMap(imap key | AnyKey(key) ::
      assert WFChildren(node.children); // trigger
      if key in node.KeySet() then INode(node.Child(key)) else PagedBetree.Nil)
  }

  function INode(node: BetreeNode) : (out: PagedBetree.BetreeNode)
    requires node.WF()
    ensures out.WF()
    decreases node, 1
  {
    if node.Nil?
    then PagedBetree.Nil
    else PagedBetree.BetreeNode(node.buffers, IChildren(node))
  }

  function IStampedBetree(stampedBetree: StampedBetree) : PagedBetree.StampedBetree
    requires stampedBetree.WF()
  {
    PagedBetree.StampedBetree(INode(stampedBetree.root), stampedBetree.seqEnd)
  }

  function ILbl(lbl: TransitionLabel) : PagedBetree.TransitionLabel
  {
    match lbl
      case QueryLabel(endLsn, key, value) => PagedBetree.QueryLabel(endLsn, key, value)
      case PutLabel(puts) => PagedBetree.PutLabel(puts)
      case QueryEndLsnLabel(endLsn) => PagedBetree.QueryEndLsnLabel(endLsn)
      case FreezeAsLabel(stampedBetree) =>PagedBetree.FreezeAsLabel(
        if stampedBetree.WF()
        then IStampedBetree(stampedBetree)
        else PagedBetree.EmptyStampedBetree())
      case InternalLabel() => PagedBetree.InternalLabel()
  }

  function I(v: Variables) : PagedBetree.Variables
    requires v.WF()
  {
    PagedBetree.Variables(v.memtable, INode(v.root))
  }

  predicate Inv(v: Variables)
  {
    && v.WF()
  }

  lemma INodeWF(node: BetreeNode)
    requires node.WF()
    ensures INode(node).WF()
  {
    if node.BetreeNode? {
      forall k | AnyKey(k) ensures INode(node).children.mapp[k].WF() {
        if k in node.KeySet() {
          INodeWF(node.Child(k));
        }
      }
    }
  }

  lemma InvNext(v: Variables, v': Variables, lbl: TransitionLabel)
    requires Inv(v)
    requires Next(v, v', lbl)
    ensures Inv(v')
  {
    assume false;
  }

  function Routing(path: Path) : (out: seq<iset<Key>>) 
    requires path.Valid()
    decreases path.depth
  {
    if path.depth == 0 
      then [] 
      else 
        var keys := PivotTableBucketKeySet(path.node.pivotTable, Route(path.node.pivotTable, path.key));
        [keys] + Routing(path.Subpath())
  }

  function IPath(path: Path) : (out: PagedBetree.Path)
    requires path.Valid()
  {
    PagedBetree.Path(INode(path.node), path.key, Routing(path))
  }

  lemma SubpathCommutesWithIPath(path: Path) 
    requires path.Valid()
    requires 0 < path.depth
    ensures IPath(path.Subpath()) == IPath(path).Subpath()
  {
    calc {  // trigger
        IPath(Path(path.node.Child(path.key), path.key, path.depth-1));
        PagedBetree.Path(INode(path.node), path.key, Routing(path)).Subpath();
      }
  }

  lemma IPathValid(path: Path) 
    requires path.Valid()
    ensures IPath(path).Valid()
    decreases path.depth
  {
    if 0 < path.depth {
      IPathValid(path.Subpath());
      SubpathCommutesWithIPath(path);
    }
  }

  lemma ValidPathRefines(path: Path)
    requires path.Valid()
    ensures IPath(path).Valid()
  {
    assume false;
  }

  lemma PathTargetRefines(path: Path)
    requires path.Valid()
    ensures IPath(path).Valid()
    ensures INode(path.Target()) == IPath(path).Target()
  {
    assume false;
  }

  function IReceiptLine(line: QueryReceiptLine) : PagedBetree.QueryReceiptLine
    requires line.WF()
  {
    PagedBetree.QueryReceiptLine(INode(line.node), line.result)
  }

  function IReceipt(receipt: QueryReceipt) : PagedBetree.QueryReceipt
    requires receipt.Valid()
  {
    PagedBetree.QueryReceipt(receipt.key, INode(receipt.root),
      seq(|receipt.lines|, i requires 0<=i<|receipt.lines| => IReceiptLine(receipt.lines[i])))
  }

  function SplitChildKeys(step: Step) : iset<Key>
    requires step.WF()
    requires step.InternalSplitStep?
    requires step.path.Valid()
  {
    step.path.Target().ChildDomain(step.childIdx).KeySet()
  }

  // Hide iset quantifier mentioning lt, which is a trigger party
  function {:opaque} SplitLeftKeys(step: Step) : iset<Key>
    requires step.WF()
    requires step.InternalSplitStep?
  {
    iset key | key in SplitChildKeys(step) && lt(Element(key), Element(step.splitKey))
  }

  function IStep(step: Step) : (out: PagedBetree.Step)
    requires step.WF()
    ensures out.WF()
  {
    match step {
      case QueryStep(receipt) => PagedBetree.QueryStep(IReceipt(receipt))
      case PutStep() => PagedBetree.PutStep()
      case QueryEndLsnStep() => PagedBetree.QueryEndLsnStep()
      case FreezeAsStep() => PagedBetree.FreezeAsStep()
      case InternalGrowStep() => PagedBetree.InternalGrowStep()
      case InternalSplitStep(path, childIdx, splitKey) =>
          var rightKeys := SplitChildKeys(step) - SplitLeftKeys(step);
          PagedBetree.InternalSplitStep(IPath(path), SplitLeftKeys(step), rightKeys)
      case InternalFlushStep(path, childIdx) =>
        PagedBetree.InternalFlushStep(IPath(path), path.Target().ChildDomain(childIdx).KeySet())
      case InternalCompactStep(path, compactedNode) =>
        PagedBetree.InternalCompactStep(IPath(path), INode(compactedNode))
    }
  }

  lemma InitRefines(v: Variables, stampedBetree: StampedBetree)
    requires Init(v, stampedBetree)
    ensures PagedBetree.Init(I(v), IStampedBetree(stampedBetree))
  {
    INodeWF(stampedBetree.root);
  }

  lemma ChildCommutesWithI(node: BetreeNode, key: Key)
    requires node.WF()
    requires node.BetreeNode?
    requires node.KeyInDomain(key)
    ensures node.Child(key).WF()  // trigger for precondition below
    ensures INode(node).Child(key) == INode(node.Child(key))
  {
    
  }

  lemma ValidReceiptRefines(receipt: QueryReceipt)
    requires receipt.Valid()
    ensures IReceipt(receipt).Valid()
  {
    var ir := IReceipt(receipt);
    forall i:nat | i < |ir.lines| ensures ir.lines[i].WF() {
      INodeWF(receipt.lines[i].node);
    }
    forall i:nat | i < |ir.lines| - 1 ensures ir.ChildLinkedAt(i) {
      assert receipt.ChildLinkedAt(i);  // trigger
      ChildCommutesWithI(receipt.lines[i].node, receipt.key);
    }
    forall i:nat | i < |ir.lines| - 1 ensures ir.ResultLinkedAt(i) {
      assert receipt.ResultLinkedAt(i);  // trigger
    }
  }

  lemma AllKeysInTotalDomain(key: Key)
    ensures key in TotalDomain().KeySet()
    ensures TotalDomain().Contains(key)
  {
    SmallestElementLte(Element(key));
    assert TotalDomain().Contains(key) by {
      reveal_TotalDomain();
      TotalDomain().reveal_Contains();
    }
  }

  lemma InternalGrowStepRefines(v: Variables, v': Variables, lbl: TransitionLabel, step: Step)
    requires Inv(v)
    requires NextStep(v, v', lbl, step)
    requires step.InternalGrowStep?
    ensures v'.WF()
    ensures PagedBetree.NextStep(I(v), I(v'), ILbl(lbl), IStep(step))
  {
    INodeWF(v.root);
    INodeWF(v'.root);

    assert I(v').root.children.mapp.Keys == AllKeys();  // trigger
    forall key:Key | AnyKey(key)
      ensures I(v').root.Child(key)
          == PagedBetree.ConstantChildMap(I(v).root).mapp[key] {
      AllKeysInTotalDomain(key);
      assert v'.root.KeyInDomain(key) by {
        v'.root.reveal_KeyInDomain();
        reveal_TotalDomain();
        TotalDomain().reveal_Contains();
      }
      ChildCommutesWithI(v'.root, key);
    }
  }

  lemma SubstitutePreservesWF(path: Path, target': BetreeNode)
    requires path.Valid()
    requires target'.WF()
    ensures path.Substitute(target').WF()
  {
  }

  // Substitution followed by interpretation is the same as interpretation
  // followed by paged-level substitution.
  lemma SubstitutionRefines(path: Path, target': BetreeNode)
    requires path.Valid()
    requires target'.WF()
    ensures path.Substitute(target').WF()
    ensures IPath(path).Valid()
    ensures INode(target').WF();
    ensures INode(path.Substitute(target')) == IPath(path).Substitute(INode(target'));
    decreases path.depth;
  {
    SubstitutePreservesWF(path, target');
    ValidPathRefines(path);
    INodeWF(target');
    if path.depth==0 {
      assert INode(path.Substitute(target')) == IPath(path).Substitute(INode(target'));
    } else {
      SubstitutionRefines(path.Subpath(), target');
      assert INode(path.Subpath().Substitute(target')) == IPath(path.Subpath()).Substitute(INode(target'));

      forall key ensures
        IChildren(path.Substitute(target')).mapp[key]
        == IPath(path).ReplacedChildren(INode(target')).mapp[key] 
      {
        if key in path.node.KeySet() {

          // assert BoundedKey(path.node.pivotTable, key) by {
          //   path.node.reveal_KeyInDomain();
          //   assert K
          // }
          var pivotMatches := Route(path.node.pivotTable, key) == Route(path.node.pivotTable, path.key);
          var pagedMatches := key in IPath(path).routing[0];


          assert pivotMatches == pagedMatches;
          assert IChildren(path.Substitute(target')).mapp[key] == IPath(path).ReplacedChildren(INode(target')).mapp[key];
        } else {
          calc {
            IChildren(path.Substitute(target')).mapp[key];

            PagedBetree.Nil;

            IPath(path).ReplacedChildren(INode(target')).mapp[key];
          }
          assert IChildren(path.Substitute(target')).mapp[key] == IPath(path).ReplacedChildren(INode(target')).mapp[key];
        }
      }

      assert INode(path.Substitute(target')) == IPath(path).Substitute(INode(target'));  // trigger
    }
  }

  lemma SplitEquivalence(v: Variables, v': Variables, lbl: TransitionLabel, step: Step, istep: PagedBetree.Step)
    requires step.WF()
    requires step.InternalSplitStep?
    requires step.path.Valid()
    requires NextStep(v, v', lbl, step)
    requires istep == IStep(step)
    ensures INode(step.path.Target().Split(step.childIdx, step.splitKey))
      == istep.path.Target().Split(istep.leftKeys, istep.rightKeys);
  {
    assume false; // still have work to do
  }

  lemma {:timeLimitMultiplier 4} InternalSplitStepRefines(v: Variables, v': Variables, lbl: TransitionLabel, step: Step)
    requires Inv(v)
    requires NextStep(v, v', lbl, step)
    requires step.InternalSplitStep?
    ensures v'.WF()
    ensures PagedBetree.NextStep(I(v), I(v'), ILbl(lbl), IStep(step))
  {
    INodeWF(v.root);
    INodeWF(step.path.Target());
    InvNext(v, v', lbl); //assert v'.WF();
    var iv := I(v);
    var node := v.root;
    var inode := INode(node);
    var iv' := I(v');
    var node' := v'.root;
    var inode' := INode(node');
    var istep := IStep(step);
    INodeWF(v'.root);
    ValidPathRefines(step.path); //assert IPath(step.path).Valid();
    var target' := step.path.Target().Split(step.childIdx, step.splitKey);
    //var itarget' := istep.path.Target().Split(istep.leftKeys, istep.rightKeys);
    var ipath := IPath(step.path);
    var itarget' := INode(target');
    /*
    //SplitEquivalence(step.path.Target(), step.childIdx, step.splitKey);
    SplitEquivalence(step);
    //var itarget' := istep.path.Target().Split(istep.leftKeys, istep.rightKeys);

    PathTargetRefines(step.path);
//    calc {
//      itarget';
//      istep.path.Target().Split(istep.leftKeys, istep.rightKeys);
//        { reveal_SplitLeftKeys(); }
//      INode(target');
//    }

    assert iv.root == INode(v.root);
    assert iv.root == istep.path.node;
    assert istep.path.Target() == INode(step.path.Target());
    assert iv'.root == INode(v'.root);

    SubstitutionRefines(step.path, target');
    assert inode' == istep.path.Substitute(istep.path.Target().Split(istep.leftKeys, istep.rightKeys));
    */
    calc {
      node';
      step.path.Substitute(target');
    }
    calc {
      itarget';
      istep.path.Target().Split(istep.leftKeys, istep.rightKeys);
    }
    assert IPath(step.path) == ipath;
    calc {
      iv'.root;
      INode(node');
      INode(step.path.Substitute(target'));
      {
        SubstitutionRefines(step.path, target');
      }
      IPath(step.path).Substitute(INode(target'));
      IPath(step.path).Substitute(INode(target'));
      ipath.Substitute(itarget');
      istep.path.Substitute(itarget');
      istep.path.Substitute(istep.path.Target().Split(istep.leftKeys, istep.rightKeys));
    }
    assert iv'.root == istep.path.Substitute(istep.path.Target().Split(istep.leftKeys, istep.rightKeys));
    assert PagedBetree.InternalSplit(I(v), I(v'), ILbl(lbl), IStep(step));
  }

  lemma NextRefines(v: Variables, v': Variables, lbl: TransitionLabel)
    requires Inv(v)
    requires Next(v, v', lbl)
    ensures v'.WF()
    ensures PagedBetree.Next(I(v), I(v'), ILbl(lbl))
  {
    InvNext(v, v', lbl);
    var step: Step :| NextStep(v, v', lbl, step);
    match step {
      case QueryStep(receipt) => {
        ValidReceiptRefines(step.receipt);
        assert PagedBetree.NextStep(I(v), I(v'), ILbl(lbl), IStep(step)); // trigger
      }
      case PutStep() => {
        assert PagedBetree.NextStep(I(v), I(v'), ILbl(lbl), IStep(step));
      }
      case QueryEndLsnStep() => {
        assert PagedBetree.NextStep(I(v), I(v'), ILbl(lbl), IStep(step));
      }
      case FreezeAsStep() => {
        INodeWF(v.root);
        assert PagedBetree.NextStep(I(v), I(v'), ILbl(lbl), IStep(step)); // trigger
      }
      case InternalGrowStep() => {
        InternalGrowStepRefines(v, v', lbl, step);
      }
      case InternalSplitStep(_, _, _) => {
        assume PagedBetree.NextStep(I(v), I(v'), ILbl(lbl), IStep(step));
      }
      case InternalFlushStep(_, _) => {
        assume PagedBetree.NextStep(I(v), I(v'), ILbl(lbl), IStep(step));
      }
      case InternalCompactStep(_, _) => {
        assume PagedBetree.NextStep(I(v), I(v'), ILbl(lbl), IStep(step));
      }
    }
  }
}
