include "BetreeJournalSystem.i.dfy"
include "../Versions/CompositeView.i.dfy"

module BetreeJournalSystem_Refines_CompositeView {
  import BJS = BetreeJournalSystem
  import CompositeView
  import UI

  import BS = BetreeSystem
  import JS = JournalSystem
  import BetreeSystemRef = BetreeSystem_Refines_StatesViewMap
  import JournalSystemRef = JournalSystem_Refines_JournalView
  import opened ViewOp

  function Ik(k: BJS.Constants) : CompositeView.Constants
  {
    BJS.Ik(k)
  }

  function I(k: BJS.Constants, s: BJS.Variables) : CompositeView.Variables
  requires BJS.Inv(k, s)
  {
    BJS.I(k, s)
  }

  lemma RefinesInit(k: BJS.Constants, s: BJS.Variables)
  requires BJS.Init(k, s)
  ensures BJS.Inv(k, s)
  ensures CompositeView.Init(Ik(k), I(k, s))
  {
    BJS.InitImpliesInv(k, s);
    var loc :|
      && BS.Init(k.bs, s.bs, loc)
      && JS.Init(k.js, s.js, loc);
    BS.InitImpliesInv(k.bs, s.bs, loc);
    JS.InitImpliesInv(k.js, s.js, loc);
    BetreeSystemRef.RefinesInit(k.bs, s.bs, loc);
    JournalSystemRef.RefinesInit(k.js, s.js, loc);
  }

  lemma RefinesNext(k: BJS.Constants, s: BJS.Variables, s': BJS.Variables, uiop: UI.Op)
  requires BJS.Inv(k, s)
  requires BJS.Next(k, s, s', uiop)
  ensures BJS.Inv(k, s')
  ensures CompositeView.Next(Ik(k), I(k, s), I(k, s'), uiop)
  {
    BJS.NextPreservesInv(k, s, s', uiop);
    var vop :|
      && VOpAgreesUIOp(vop, uiop)
      && BS.Next(k.bs, s.bs, s'.bs, vop)
      && JS.Next(k.js, s.js, s'.js, vop);
    BS.NextPreservesInv(k.bs, s.bs, s'.bs, vop);
    JS.NextPreservesInv(k.js, s.js, s'.js, vop);
    BetreeSystemRef.RefinesNext(k.bs, s.bs, s'.bs, vop);
    JournalSystemRef.RefinesNext(k.js, s.js, s'.js, vop);
    var step := CompositeView.Step(vop);
    assert CompositeView.NextStep(Ik(k), I(k, s), I(k, s'),
      step.vop, uiop);
    CompositeView.NextPreservesInv(Ik(k), I(k, s), I(k, s'), uiop);
  }
}
