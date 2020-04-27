include "PivotBetree_Refines_Map.i.dfy"
include "StatesViewPivotBetree.i.dfy"
include "../Versions/StatesViewMap.i.dfy"

//
// Lifts the refinement:
//
//   PivotBetree -> Map
//
// to
//
//   StatesView PivotBetree -> StatesView Map
//
// via the StatesView functor
//

module StatesViewPivotBetree_Refines_StatesViewMap {
  import A = StatesViewPivotBetree
  import B = StatesViewMap
  import Ref = PivotBetree_Refines_Map
  import UI
  import opened ViewOp
  import opened Options
 
  function Ik(k: A.Constants) : B.Constants {
    B.Constants(Ref.Ik(k.k))
  }

  function IDisk(k: A.SM.Constants, disk: imap<Loc, A.SM.Variables>) : imap<Loc, B.SM.Variables>
  {
    imap loc | loc in disk && A.SM.Inv(k, disk[loc])
      :: Ref.I(k, disk[loc])
  }

  function IOptState(k: A.SM.Constants, state: Option<A.SM.Variables>) : Option<B.SM.Variables>
  requires state.Some? ==> A.SM.Inv(k, state.value)
  {
    if state.Some? then Some(Ref.I(k, state.value)) else None
  }
  
  function I(k: A.Constants, s: A.Variables) : B.Variables
    requires A.Inv(k, s)
  {
    B.Variables(
      IDisk(k.k, s.disk),
      s.persistentLoc,
      s.frozenLoc,
      IOptState(k.k, s.frozenState),
      IOptState(k.k, s.ephemeralState))
  }

  lemma RefinesInit(k: A.Constants, s: A.Variables, loc: Loc)
    requires A.Init(k, s, loc)
    ensures A.Inv(k, s)
    ensures B.Init(Ik(k), I(k, s), loc)
  {
    A.SM.InitImpliesInv(k.k, s.disk[loc]);
    Ref.RefinesInit(k.k, s.disk[loc]);
  }

  lemma RefinesNextStep(k: A.Constants, s: A.Variables, s': A.Variables, vop: VOp, step: A.Step)
    requires A.Inv(k, s)
    requires A.NextStep(k, s, s', vop, step)
    ensures A.Inv(k, s')
    ensures B.Next(Ik(k), I(k, s), I(k, s'), vop)
  {
    A.NextPreservesInv(k, s, s', vop);
    match step {
      case ObtainPersistentLocStep => {
        assert B.NextStep(Ik(k), I(k, s), I(k, s'), vop, B.ObtainPersistentLocStep);
      }
      case AdvanceStep => {
        Ref.RefinesNext(k.k,
          s.ephemeralState.value,
          s'.ephemeralState.value,
          vop.uiop);
        assert B.NextStep(Ik(k), I(k, s), I(k, s'), vop, B.AdvanceStep);
      }
      case CrashStep => {
        assert B.NextStep(Ik(k), I(k, s), I(k, s'), vop, B.CrashStep);
      }
      case FreezeStep => {
        assert B.NextStep(Ik(k), I(k, s), I(k, s'), vop, B.FreezeStep);
      }
      case DiskChangeStep => {
        assert B.NextStep(Ik(k), I(k, s), I(k, s'), vop, B.DiskChangeStep);
      }
      case ProvideFrozenLocStep => {
        assert B.NextStep(Ik(k), I(k, s), I(k, s'), vop, B.ProvideFrozenLocStep);
      }
      case ForgetOldStep => {
        assert B.NextStep(Ik(k), I(k, s), I(k, s'), vop, B.ForgetOldStep);
      }
      case StutterStep => {
        assert B.NextStep(Ik(k), I(k, s), I(k, s'), vop, B.StutterStep);
      }
    }
  }

  lemma RefinesNext(k: A.Constants, s: A.Variables, s': A.Variables, vop: VOp)
    requires A.Inv(k, s)
    requires A.Next(k, s, s', vop)
    ensures A.Inv(k, s')
    ensures B.Next(Ik(k), I(k, s), I(k, s'), vop)
  {
    var step :| A.NextStep(k, s, s', vop, step);
    RefinesNextStep(k, s, s', vop, step);
  }
}
