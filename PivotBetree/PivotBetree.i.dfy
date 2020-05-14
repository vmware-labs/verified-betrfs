include "../Betree/BlockInterface.i.dfy"  
include "../lib/Base/sequences.i.dfy"
include "../lib/Base/Maps.s.dfy"
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

  import opened G = PivotBetreeGraph

  datatype Constants = Constants(bck: BI.Constants)
  datatype Variables = Variables(bcv: BI.Variables)

  function EmptyNode() : Node
  {
    Node([], None, [BucketsLib.B(map[])])
  }

  predicate Init(k: Constants, s: Variables) {
    && BI.Init(k.bck, s.bcv)
    && s.bcv.view[G.Root()] == EmptyNode()
  }

  predicate GC(k: Constants, s: Variables, s': Variables, uiop: UIOp, refs: iset<Reference>) {
    && uiop.NoOp? 
    && BI.GC(k.bck, s.bcv, s'.bcv, refs)
  }

  predicate Betree(k: Constants, s: Variables, s': Variables, uiop: UIOp, betreeStep: BetreeStep)
  {
    && ValidBetreeStep(betreeStep)
    && BI.Reads(k.bck, s.bcv, BetreeStepReads(betreeStep))
    && BI.OpTransaction(k.bck, s.bcv, s'.bcv, BetreeStepOps(betreeStep))
    && BetreeStepUI(betreeStep, uiop)
  }
 
  datatype Step =
    | BetreeStep(step: BetreeStep)
    | GCStep(refs: iset<Reference>)
    | StutterStep

  predicate NextStep(k: Constants, s: Variables, s': Variables, uiop: UIOp, step: Step) {
    match step {
      case BetreeStep(betreeStep) => Betree(k, s, s', uiop, betreeStep)
      case GCStep(refs) => GC(k, s, s', uiop, refs)
      case StutterStep => s == s' && uiop.NoOp?
    }
  }

  predicate Next(k: Constants, s: Variables, s': Variables, uiop: UIOp) {
    exists step: Step :: NextStep(k, s, s', uiop, step)
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

  function Ik(k: Constants) : B.Constants
  {
    B.Constants(BBI.Constants())
  }

  predicate ViewHasInvNodes(view: imap<Reference, Node>)
  {
    forall ref | ref in view :: InvNode(view[ref])
  }

  function IView(view: imap<Reference, Node>) : imap<Reference, BG.Node>
  requires ViewHasInvNodes(view)
  {
    imap ref | ref in view :: SpecRef.INode(view[ref])
  }
  
  function I(k: Constants, s: Variables) : B.Variables
  requires ViewHasInvNodes(s.bcv.view)
  {
    B.Variables(BBI.Variables(IView(s.bcv.view)))
  }

  predicate Inv(k: Constants, s: Variables)
  {
    && ViewHasInvNodes(s.bcv.view)
    && BInv.Inv(Ik(k), I(k, s))
  }

  lemma OpRefines(k: Constants, s: Variables, s': Variables, op: PG.Op)
  requires InvNode(op.node)
  requires ViewHasInvNodes(s.bcv.view)
  requires BI.OpStep(k.bck, s.bcv, s'.bcv, op)
  ensures ViewHasInvNodes(s'.bcv.view)
  ensures BBI.OpStep(Ik(k).bck, I(k, s).bcv, I(k, s').bcv, SpecRef.IOp(op))
  {
    //BBI.OpStepPreservesInv(Ik(k).bck, I(k, s).bcv, I(k, s').bcv, SpecRef.IOp(op));
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

  lemma TransactionRefines(k: Constants, s: Variables, s': Variables, ops: seq<PG.Op>)
  requires forall i | 0 <= i < |ops| :: InvNode(ops[i].node)
  requires ViewHasInvNodes(s.bcv.view)
  requires BI.Transaction(k.bck, s.bcv, s'.bcv, ops)
  ensures ViewHasInvNodes(s'.bcv.view)
  ensures BBI.Transaction(Ik(k).bck, I(k, s).bcv, I(k, s').bcv, SpecRef.IOps(ops))
  decreases |ops|
  {
    if (|ops| == 0) {
    } else if (|ops| == 1) {
      OpRefines(k, s, s', ops[0]);
    } else {
      var ops1, mid, ops2 := BI.SplitTransaction(k.bck, s.bcv, s'.bcv, ops);
      var smid := Variables(mid);

      forall i | 0 <= i < |ops1| ensures InvNode(ops1[i].node)
      {
        assert ops1[i].node == ops[i].node;
      }
      forall i | 0 <= i < |ops2| ensures InvNode(ops2[i].node)
      {
        assert ops2[i].node == ops[i + |ops1|].node;
      }

      TransactionRefines(k, s, smid, ops1);
      TransactionRefines(k, smid, s', ops2);
      BBI.JoinTransactions(Ik(k).bck, I(k, s).bcv, I(k, smid).bcv, I(k, s').bcv, SpecRef.IOps(ops1), SpecRef.IOps(ops2));
      IOpsAdditive(ops1, ops2);
      //assert SpecRef.IOps(ops) == SpecRef.IOps(ops1) + SpecRef.IOps(ops2); // TODO
    }
  }

  lemma ReadsRefines(k: Constants, s: Variables, ops: seq<PG.ReadOp>)
  requires forall i | 0 <= i < |ops| :: InvNode(ops[i].node)
  requires forall i | 0 <= i < |ops| :: WFNode(ops[i].node)
  requires ViewHasInvNodes(s.bcv.view)
  requires BI.Reads(k.bck, s.bcv, ops)
  ensures BBI.Reads(Ik(k).bck, I(k, s).bcv, SpecRef.IReadOps(ops))
  decreases |ops|
  {
    if (|ops| == 0) {
    } else {
      ReadsRefines(k, s, DropLast(ops));
      forall op' | op' in SpecRef.IReadOps(ops)
      ensures BBI.ReadStep(Ik(k).bck, I(k, s).bcv, op')
      {
        var i :| 0 <= i < |SpecRef.IReadOps(ops)| && SpecRef.IReadOps(ops)[i] == op';
        if (i == |ops| - 1) {
          var op := ops[i];
          //assert op' == SpecRef.IReadOp(op);
          assert BI.ReadStep(k.bck, s.bcv, op);
          /*
          assert op.ref in s.bcv.view;
          assert op'.ref == op.ref;
          assert op'.ref in s.bcv.view;
          assert op'.ref in I(k, s).bcv.view;
          assert I(k, s).bcv.view[op'.ref]
              == SpecRef.INode(s.bcv.view[op.ref])
              == op'.node;
          assert BBI.ReadStep(Ik(k).bck, I(k, s).bcv, op');
          */
        } else {
          //assert BBI.ReadStep(Ik(k).bck, I(k, s).bcv, SpecRef.IReadOps(ops)[i]);
        }
      }
    }
  }

  /*lemma ReadOpsBucketsWellMarshalledOfValidStep(k: Constants, s: Variables, betreeStep: BetreeStep)
  requires ValidBetreeStep(betreeStep)
  requires BI.Reads(k.bck, s.bcv, BetreeStepReads(betreeStep))
  ensures SpecRef.ReadOpsBucketsWellMarshalled(BetreeStepReads(betreeStep))
  {
    var readOps := BetreeStepReads(betreeStep);
    forall i, j |
      0 <= i < |readOps| &&
      0 <= j < |readOps[i].node.buckets|
    ensures BucketWellMarshalled(readOps[i].node.buckets[j])
    {
      assert BI.ReadStep(k.bck, s.bcv, readOps[i]);
      assert readOps[i].node == s.bcv.view[readOps[i].ref];
    }
  }*/

  lemma BetreeStepRefines(k: Constants, s: Variables, s': Variables, uiop: UIOp, betreeStep: BetreeStep)
  requires Inv(k, s)
  requires NextStep(k, s, s', uiop, BetreeStep(betreeStep))
  ensures Inv(k, s')
  //ensures B.NextStep(Ik(k), I(k,s), I(k,s'), uiop, B.BetreeStep(SpecRef.IStep(betreeStep)))
  ensures B.Next(Ik(k), I(k,s), I(k,s'), uiop)
  {
    if (betreeStep.BetreeRepivot?) {
      SpecRef.RepivotPreservesNode(betreeStep.repivot);

      assert B.NextStep(Ik(k), I(k,s), I(k,s'), uiop, B.StutterStep);
      BInv.NextPreservesInv(Ik(k), I(k, s), I(k, s'), uiop);
    } else {
      forall i | 0 <= i < |BetreeStepReads(betreeStep)|
      ensures InvNode(BetreeStepReads(betreeStep)[i].node)
      {
        assert BI.ReadStep(k.bck, s.bcv, BetreeStepReads(betreeStep)[i]);
        assert s.bcv.view[BetreeStepReads(betreeStep)[i].ref]
            == BetreeStepReads(betreeStep)[i].node;
      }

      SpecRef.RefinesValidBetreeStep(betreeStep);
      SpecRef.RefinesReadOps(betreeStep);
      SpecRef.RefinesOps(betreeStep);
      TransactionRefines(k, s, s', BetreeStepOps(betreeStep));
      ReadsRefines(k, s, BetreeStepReads(betreeStep));

      /*
      match betreeStep {
        case BetreeQuery(q) => {
          assert B.Betree(Ik(k), I(k,s), I(k,s'), uiop, SpecRef.IStep(betreeStep));
          assert B.NextStep(Ik(k), I(k,s), I(k,s'), uiop, B.BetreeStep(SpecRef.IStep(betreeStep)));
        }
        case BetreeInsert(ins) => 
        assert B.NextStep(Ik(k), I(k,s), I(k,s'), uiop, B.BetreeStep(SpecRef.IStep(betreeStep)));
        case BetreeFlush(flush) => 
        assert B.NextStep(Ik(k), I(k,s), I(k,s'), uiop, B.BetreeStep(SpecRef.IStep(betreeStep)));
        case BetreeGrow(growth) => 
        assert B.NextStep(Ik(k), I(k,s), I(k,s'), uiop, B.BetreeStep(SpecRef.IStep(betreeStep)));
        case BetreeSplit(fusion) => 
        assert B.NextStep(Ik(k), I(k,s), I(k,s'), uiop, B.BetreeStep(SpecRef.IStep(betreeStep)));
        case BetreeMerge(fusion) => 
        assert B.NextStep(Ik(k), I(k,s), I(k,s'), uiop, B.BetreeStep(SpecRef.IStep(betreeStep)));
      }
      */
      assert B.NextStep(Ik(k), I(k,s), I(k,s'), uiop, B.BetreeStep(SpecRef.IStep(betreeStep)));
      BInv.NextPreservesInv(Ik(k), I(k, s), I(k, s'), uiop);
    }
  }

  lemma GCStepRefines(k: Constants, s: Variables, s': Variables, uiop: UIOp, refs: iset<Reference>)
  requires Inv(k, s)
  requires NextStep(k, s, s', uiop, GCStep(refs))
  ensures Inv(k, s')
  ensures B.NextStep(Ik(k), I(k,s), I(k,s'), uiop, B.GCStep(refs))
  {
    assert B.NextStep(Ik(k), I(k,s), I(k,s'), uiop, B.GCStep(refs));
    BInv.NextPreservesInv(Ik(k), I(k, s), I(k, s'), uiop);
  }

  lemma StutterStepRefines(k: Constants, s: Variables, s': Variables, uiop: UIOp)
  requires Inv(k, s)
  requires NextStep(k, s, s', uiop, StutterStep)
  ensures Inv(k, s')
  ensures B.NextStep(Ik(k), I(k,s), I(k,s'), uiop, B.StutterStep)
  {
  }

  lemma PivotBetreeRefinesBetreeNextStep(k: Constants, s: Variables, s': Variables, uiop: UIOp, step: Step)
    requires Inv(k, s)
    requires NextStep(k, s, s', uiop, step)
    ensures Inv(k, s')
    ensures B.Next(Ik(k), I(k, s), I(k, s'), uiop)
  {
    match step {
      case BetreeStep(betreeStep) => BetreeStepRefines(k, s, s', uiop, betreeStep);
      case GCStep(refs) => GCStepRefines(k, s, s', uiop, refs);
      case StutterStep => StutterStepRefines(k, s, s', uiop);
    }
  }

  lemma InitImpliesInv(k: Constants, s: Variables)
  // declared in UIStateMachine
  {
    RefinesInit(k, s);
  }

  lemma NextPreservesInv(k: Constants, s: Variables, s': Variables, uiop: UIOp)
  // declared in UIStateMachine
  {
    var step :| NextStep(k, s, s', uiop, step);
    PivotBetreeRefinesBetreeNextStep(k, s, s', uiop, step);
  }

  lemma RefinesInit(k: Constants, s: Variables)
    requires Init(k, s)
    ensures Inv(k, s)
    ensures B.Init(Ik(k), I(k, s))
  {
    reveal_WeightBucketList();
    //reveal_WeightBucket();
    assert SpecRef.INode(EmptyNode()) == B.EmptyNode();
    BInv.InitImpliesInv(Ik(k), I(k, s));
  }

  lemma RefinesNext(k: Constants, s: Variables, s': Variables, uiop: UIOp)
    requires Inv(k, s)
    requires Next(k, s, s', uiop)
    ensures Inv(k, s')
    ensures B.Next(Ik(k), I(k, s), I(k, s'), uiop)
  {
    var step :| NextStep(k, s, s', uiop, step);
    PivotBetreeRefinesBetreeNextStep(k, s, s', uiop, step);
  }

}
