include "PivotBetree_Refines_Map.i.dfy"
include "ThreeStateVersionedPivotBetree.i.dfy"
include "../MapSpec/ThreeStateVersionedMap.s.dfy"

//
// Lifts the refinement:
//
//   PivotBetree -> Map
//
// oo
//
//   ThreeStateVersioned PivotBetree -> ThreeStateVersioned Map
//
// via the ThreeStateVersioned functor
//

module ThreeStateVersionedPivotBetree_Refines_ThreeStateVersionedMap {
  import A = ThreeStateVersionedPivotBetree
  import B = ThreeStateVersionedMap
  import Ref = PivotBetree_Refines_Map
  import UI
 
  function Ik(k: A.Constants) : B.Constants {
    B.Constants(Ref.Ik(k.k))
  }
  
  function I(k: A.Constants, s: A.Variables) : B.Variables
    requires A.Inv(k, s)
  {
    B.Variables(
      Ref.I(k.k, s.s1),
      Ref.I(k.k, s.s2),
      Ref.I(k.k, s.s3),
      s.outstandingSyncReqs)
  }

  lemma RefinesInit(k: A.Constants, s: A.Variables)
    requires A.Init(k, s)
    ensures A.Inv(k, s)
    ensures B.Init(Ik(k), I(k, s))
  {
    Ref.PivotBetreeRefinesMapInit(k.k, s.s1);
    Ref.PivotBetreeRefinesMapInit(k.k, s.s2);
    Ref.PivotBetreeRefinesMapInit(k.k, s.s3);
  }

  lemma RefinesNextStep(k: A.Constants, s: A.Variables, s': A.Variables, uiop: UI.Op, step: A.Step)
    requires A.Inv(k, s)
    requires A.NextStep(k, s, s', uiop, step)
    ensures A.Inv(k, s')
    ensures B.Next(Ik(k), I(k, s), I(k, s'), uiop)
  {
    match step {
      case CrashStep => {
        assert B.NextStep(Ik(k), I(k, s), I(k, s'), uiop, B.CrashStep);
      }
      case Move1to2Step => {
        assert B.NextStep(Ik(k), I(k, s), I(k, s'), uiop, B.Move1to2Step);
      }
      case Move2to3Step => {
        assert B.NextStep(Ik(k), I(k, s), I(k, s'), uiop, B.Move2to3Step);
      }
      case Move3Step => {
        Ref.PivotBetreeRefinesMapNext(k.k, s.s3, s'.s3, uiop);
        assert B.NextStep(Ik(k), I(k, s), I(k, s'), uiop, B.Move3Step);
      }
      case PushSyncStep(id) => {
        assert B.NextStep(Ik(k), I(k, s), I(k, s'), uiop, B.PushSyncStep(id));
      }
      case PopSyncStep(id) => {
        assert B.NextStep(Ik(k), I(k, s), I(k, s'), uiop, B.PopSyncStep(id));
      }
    }
  }

  lemma RefinesNext(k: A.Constants, s: A.Variables, s': A.Variables, uiop: UI.Op)
    requires A.Inv(k, s)
    requires A.Next(k, s, s', uiop)
    ensures A.Inv(k, s')
    ensures B.Next(Ik(k), I(k, s), I(k, s'), uiop)
  {
    var step :| A.NextStep(k, s, s', uiop, step);
    RefinesNextStep(k, s, s', uiop, step);
  }
}
