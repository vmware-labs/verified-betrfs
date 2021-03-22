// Copyright 2018-2021 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, and University of Washington
// SPDX-License-Identifier: BSD-2-Clause

include "../Betree/BlockInterface.i.dfy"  
include "../lib/Base/sequences.i.dfy"
include "../lib/Base/Maps.i.dfy"
include "../MapSpec/MapSpec.s.dfy"
include "../Betree/Graph.i.dfy"
include "../lib/Base/Option.s.dfy"
include "../lib/Base/Message.i.dfy"
include "../Betree/BetreeSpec.i.dfy"
include "../Betree/Betree.i.dfy"
include "../Betree/BetreeInv.i.dfy"
include "../PivotBetree/PivotBetreeSpec.i.dfy"
include "../MapSpec/UIStateMachine.s.dfy"
include "PivotBetreeSpecRefinement.i.dfy"
include "PivotBetreeBlockInterface.i.dfy"

//
// Like Betree, PivetBetree lowers the "lifted" op-sequences of PivotBetreeSpec
// down to concrete state machine steps that advance the PivotBetreeBlockInterface
// as required by BetreeSpec. The only difference is that the interface has a more
// concrete (pivot-y) type.
//

module PivotBetree refines UIStateMachine {
  import opened PivotBetreeSpec`Internal

  import BI = PivotBetreeBlockInterface
  import MS = MapSpec
  import opened Maps
  import opened Options
  import opened BucketsLib
  import opened BoundedPivotsLib

  import opened G = PivotBetreeGraph

  datatype Variables = Variables(bcv: BI.Variables)

  function EmptyNode() : Node
  {
    Node(InitPivotTable(), None, [BucketsLib.EmptyBucket()])
  }

  predicate Init(s: Variables) {
    && BI.Init(s.bcv)
    && s.bcv.view[G.Root()] == EmptyNode()
  }

  predicate GC(s: Variables, s': Variables, uiop: UIOp, refs: iset<Reference>) {
    && uiop.NoOp? 
    && BI.GC(s.bcv, s'.bcv, refs)
  }

  predicate Betree(s: Variables, s': Variables, uiop: UIOp, betreeStep: BetreeStep)
  {
    && ValidBetreeStep(betreeStep)
    && BI.Reads(s.bcv, BetreeStepReads(betreeStep))
    && BI.OpTransaction(s.bcv, s'.bcv, BetreeStepOps(betreeStep))
    && BetreeStepUI(betreeStep, uiop)
  }
 
  datatype Step =
    | BetreeStep(step: BetreeStep)
    | GCStep(refs: iset<Reference>)
    | StutterStep

  predicate NextStep(s: Variables, s': Variables, uiop: UIOp, step: Step) {
    match step {
      case BetreeStep(betreeStep) => Betree(s, s', uiop, betreeStep)
      case GCStep(refs) => GC(s, s', uiop, refs)
      case StutterStep => s == s' && uiop.NoOp?
    }
  }

  predicate Next(s: Variables, s': Variables, uiop: UIOp) {
    exists step: Step :: NextStep(s, s', uiop, step)
  }

  //////////////////////////////////////////////
  ////// Invariants and refinement

  //
  // "Boilerplate" for the refinement/invariant proof for PivotBetree.
  // Reasons about refinement between generic Ops.
  // Relies on logic about specific ops from PivotBetreeSpecRefinement.
  //
  // This is "boilerplate" in that the difficult logic is about the Node and Op refinement
  // in PivotBetreeSpecRefinement; this file just "lowers" that logic from ops down to
  // concrete state machine steps.
  //

  import B = Betree
  import BG = BetreeGraph
  import PG = PivotBetreeGraph
  import BBI = BetreeBlockInterface
  import SpecRef = PivotBetreeSpecRefinement
  import BInv = BetreeInv
  import opened Sequences
  import opened BucketWeights

  predicate ViewHasInvNodes(view: imap<Reference, Node>)
  {
    forall ref | ref in view :: InvNode(view[ref])
  }

  function IView(view: imap<Reference, Node>) : imap<Reference, BG.Node>
  requires ViewHasInvNodes(view)
  {
    imap ref | ref in view :: SpecRef.INode(view[ref])
  }
  
  function I(s: Variables) : B.Variables
  requires ViewHasInvNodes(s.bcv.view)
  {
    B.Variables(BBI.Variables(IView(s.bcv.view)))
  }

  predicate Inv(s: Variables)
  {
    && ViewHasInvNodes(s.bcv.view)
    && BInv.Inv(I(s))
  }

  lemma OpRefines(s: Variables, s': Variables, op: PG.Op)
  requires InvNode(op.node)
  requires ViewHasInvNodes(s.bcv.view)
  requires BI.OpStep(s.bcv, s'.bcv, op)
  ensures ViewHasInvNodes(s'.bcv.view)
  ensures BBI.OpStep(I(s).bcv, I(s').bcv, SpecRef.IOp(op))
  {
    //BBI.OpStepPreservesInv(I(s).bcv, I(s').bcv, SpecRef.IOp(op));
  }

  lemma IOpsAdditive(ops1: seq<PG.Op>, ops2: seq<PG.Op>)
  requires forall i | 0 <= i < |ops1| :: InvNode(ops1[i].node)
  requires forall i | 0 <= i < |ops2| :: InvNode(ops2[i].node)
  ensures SpecRef.IOps(ops1 + ops2) == SpecRef.IOps(ops1) + SpecRef.IOps(ops2)
  {
    if (|ops2| == 0) {
      assert ops2 == [];
      assert SpecRef.IOps(ops2) == [];
      assert ops1 + ops2 == ops1;
      assert SpecRef.IOps(ops1 + ops2) == SpecRef.IOps(ops1) + SpecRef.IOps(ops2);
    } else {
      IOpsAdditive(ops1, ops2[..|ops2|-1]);
      assert (ops1 + ops2)[..|ops1 + ops2|-1] == ops1 + ops2[..|ops2|-1];
      assert SpecRef.IOps(ops1 + ops2)
          == SpecRef.IOps((ops1 + ops2)[..|ops1 + ops2|-1]) + [SpecRef.IOp((ops1 + ops2)[|ops1 + ops2| - 1])]
          == SpecRef.IOps(ops1 + ops2[..|ops2|-1]) + [SpecRef.IOp((ops1 + ops2)[|ops1 + ops2| - 1])]
          == SpecRef.IOps(ops1) + SpecRef.IOps(ops2[..|ops2|-1]) + [SpecRef.IOp((ops1 + ops2)[|ops1 + ops2| - 1])]
          == SpecRef.IOps(ops1) + SpecRef.IOps(ops2[..|ops2|-1]) + [SpecRef.IOp(ops2[|ops2| - 1])]
          == SpecRef.IOps(ops1) + SpecRef.IOps(ops2);
    }
  }

  lemma TransactionRefines(s: Variables, s': Variables, ops: seq<PG.Op>)
  requires forall i | 0 <= i < |ops| :: InvNode(ops[i].node)
  requires ViewHasInvNodes(s.bcv.view)
  requires BI.Transaction(s.bcv, s'.bcv, ops)
  ensures ViewHasInvNodes(s'.bcv.view)
  ensures BBI.Transaction(I(s).bcv, I(s').bcv, SpecRef.IOps(ops))
  decreases |ops|
  {
    if (|ops| == 0) {
    } else if (|ops| == 1) {
      OpRefines(s, s', ops[0]);
    } else {
      var ops1, mid, ops2 := BI.SplitTransaction(s.bcv, s'.bcv, ops);
      var smid := Variables(mid);

      forall i | 0 <= i < |ops1| ensures InvNode(ops1[i].node)
      {
        assert ops1[i].node == ops[i].node;
      }
      forall i | 0 <= i < |ops2| ensures InvNode(ops2[i].node)
      {
        assert ops2[i].node == ops[i + |ops1|].node;
      }

      TransactionRefines(s, smid, ops1);
      TransactionRefines(smid, s', ops2);
      BBI.JoinTransactions(I(s).bcv, I(smid).bcv, I(s').bcv, SpecRef.IOps(ops1), SpecRef.IOps(ops2));
      IOpsAdditive(ops1, ops2);
      //assert SpecRef.IOps(ops) == SpecRef.IOps(ops1) + SpecRef.IOps(ops2); // TODO
    }
  }

  lemma ReadsRefines(s: Variables, ops: seq<PG.ReadOp>)
  requires forall i | 0 <= i < |ops| :: InvNode(ops[i].node)
  requires forall i | 0 <= i < |ops| :: WFNode(ops[i].node)
  requires ViewHasInvNodes(s.bcv.view)
  requires BI.Reads(s.bcv, ops)
  ensures BBI.Reads(I(s).bcv, SpecRef.IReadOps(ops))
  decreases |ops|
  {
    if (|ops| == 0) {
    } else {
      ReadsRefines(s, DropLast(ops));
      forall op' | op' in SpecRef.IReadOps(ops)
      ensures BBI.ReadStep(I(s).bcv, op')
      {
        var i :| 0 <= i < |SpecRef.IReadOps(ops)| && SpecRef.IReadOps(ops)[i] == op';
        if (i == |ops| - 1) {
          var op := ops[i];
          //assert op' == SpecRef.IReadOp(op);
          assert BI.ReadStep(s.bcv, op);
          /*
          assert op.ref in s.bcv.view;
          assert op'.ref == op.ref;
          assert op'.ref in s.bcv.view;
          assert op'.ref in I(s).bcv.view;
          assert I(s).bcv.view[op'.ref]
              == SpecRef.INode(s.bcv.view[op.ref])
              == op'.node;
          assert BBI.ReadStep(I(s).bcv, op');
          */
        } else {
          //assert BBI.ReadStep(I(s).bcv, SpecRef.IReadOps(ops)[i]);
        }
      }
    }
  }

  /*lemma ReadOpsBucketsWellMarshalledOfValidStep(s: Variables, betreeStep: BetreeStep)
  requires ValidBetreeStep(betreeStep)
  requires BI.Reads(s.bcv, BetreeStepReads(betreeStep))
  ensures SpecRef.ReadOpsBucketsWellMarshalled(BetreeStepReads(betreeStep))
  {
    var readOps := BetreeStepReads(betreeStep);
    forall i, j |
      0 <= i < |readOps| &&
      0 <= j < |readOps[i].node.buckets|
    ensures BucketWellMarshalled(readOps[i].node.buckets[j])
    {
      assert BI.ReadStep(s.bcv, readOps[i]);
      assert readOps[i].node == s.bcv.view[readOps[i].ref];
    }
  }*/

  lemma BetreeStepRefines(s: Variables, s': Variables, uiop: UIOp, betreeStep: BetreeStep)
  requires Inv(s)
  requires NextStep(s, s', uiop, BetreeStep(betreeStep))
  ensures Inv(s')
  //ensures B.NextStep(I(s), I(s'), uiop, B.BetreeStep(SpecRef.IStep(betreeStep)))
  ensures B.Next(I(s), I(s'), uiop)
  {
    if (betreeStep.BetreeRepivot?) {
      SpecRef.RepivotPreservesNode(betreeStep.repivot);

      assert B.NextStep(I(s), I(s'), uiop, B.StutterStep);
      BInv.NextPreservesInv(I(s), I(s'), uiop);
    } else {
      forall i | 0 <= i < |BetreeStepReads(betreeStep)|
      ensures InvNode(BetreeStepReads(betreeStep)[i].node)
      {
        assert BI.ReadStep(s.bcv, BetreeStepReads(betreeStep)[i]);
        assert s.bcv.view[BetreeStepReads(betreeStep)[i].ref]
            == BetreeStepReads(betreeStep)[i].node;
      }

      SpecRef.RefinesValidBetreeStep(betreeStep);
      SpecRef.RefinesReadOps(betreeStep);
      SpecRef.RefinesOps(betreeStep);
      TransactionRefines(s, s', BetreeStepOps(betreeStep));
      ReadsRefines(s, BetreeStepReads(betreeStep));

      /*
      match betreeStep {
        case BetreeQuery(q) => {
          assert B.Betree(I(s), I(s'), uiop, SpecRef.IStep(betreeStep));
          assert B.NextStep(I(s), I(s'), uiop, B.BetreeStep(SpecRef.IStep(betreeStep)));
        }
        case BetreeInsert(ins) => 
        assert B.NextStep(I(s), I(s'), uiop, B.BetreeStep(SpecRef.IStep(betreeStep)));
        case BetreeFlush(flush) => 
        assert B.NextStep(I(s), I(s'), uiop, B.BetreeStep(SpecRef.IStep(betreeStep)));
        case BetreeGrow(growth) => 
        assert B.NextStep(I(s), I(s'), uiop, B.BetreeStep(SpecRef.IStep(betreeStep)));
        case BetreeSplit(fusion) => 
        assert B.NextStep(I(s), I(s'), uiop, B.BetreeStep(SpecRef.IStep(betreeStep)));
        case BetreeMerge(fusion) => 
        assert B.NextStep(I(s), I(s'), uiop, B.BetreeStep(SpecRef.IStep(betreeStep)));
      }
      */
      assert B.NextStep(I(s), I(s'), uiop, B.BetreeStep(SpecRef.IStep(betreeStep)));
      BInv.NextPreservesInv(I(s), I(s'), uiop);
    }
  }

  lemma GCStepRefines(s: Variables, s': Variables, uiop: UIOp, refs: iset<Reference>)
  requires Inv(s)
  requires NextStep(s, s', uiop, GCStep(refs))
  ensures Inv(s')
  ensures B.NextStep(I(s), I(s'), uiop, B.GCStep(refs))
  {
    assert B.NextStep(I(s), I(s'), uiop, B.GCStep(refs));
    BInv.NextPreservesInv(I(s), I(s'), uiop);
  }

  lemma StutterStepRefines(s: Variables, s': Variables, uiop: UIOp)
  requires Inv(s)
  requires NextStep(s, s', uiop, StutterStep)
  ensures Inv(s')
  ensures B.NextStep(I(s), I(s'), uiop, B.StutterStep)
  {
  }

  lemma PivotBetreeRefinesBetreeNextStep(s: Variables, s': Variables, uiop: UIOp, step: Step)
    requires Inv(s)
    requires NextStep(s, s', uiop, step)
    ensures Inv(s')
    ensures B.Next(I(s), I(s'), uiop)
  {
    match step {
      case BetreeStep(betreeStep) => BetreeStepRefines(s, s', uiop, betreeStep);
      case GCStep(refs) => GCStepRefines(s, s', uiop, refs);
      case StutterStep => StutterStepRefines(s, s', uiop);
    }
  }

  lemma InitImpliesInv(s: Variables)
  // declared in UIStateMachine
  {
    RefinesInit(s);
  }

  lemma NextPreservesInv(s: Variables, s': Variables, uiop: UIOp)
  // declared in UIStateMachine
  {
    var step :| NextStep(s, s', uiop, step);
    PivotBetreeRefinesBetreeNextStep(s, s', uiop, step);
  }

  lemma RefinesInit(s: Variables)
    requires Init(s)
    ensures Inv(s)
    ensures B.Init(I(s))
  {
    reveal_WeightBucketList();
    //reveal_WeightBucket();

    assert SpecRef.INode(EmptyNode()) == B.EmptyNode();
    BInv.InitImpliesInv(I(s));
  }

  lemma RefinesNext(s: Variables, s': Variables, uiop: UIOp)
    requires Inv(s)
    requires Next(s, s', uiop)
    ensures Inv(s')
    ensures B.Next(I(s), I(s'), uiop)
  {
    var step :| NextStep(s, s', uiop, step);
    PivotBetreeRefinesBetreeNextStep(s, s', uiop, step);
  }

}
