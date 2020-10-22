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

  function I(s: BJS.Variables) : CompositeView.Variables
  requires BJS.Inv(s)
  {
    CompositeView.Variables(
      BetreeSystemRef.I(s.bs),
      JournalSystemRef.I(s.js)
    )
  }

  lemma RefinesInit(s: BJS.Variables)
  requires BJS.Init(s)
  ensures BJS.Inv(s)
  ensures CompositeView.Init(I(s))
  {
    BJS.InitImpliesInv(s);
    var loc :|
      && BS.Init(s.bs, loc)
      && JS.Init(s.js, loc);
    BS.InitImpliesInv(s.bs, loc);
    JS.InitImpliesInv(s.js, loc);
    BetreeSystemRef.RefinesInit(s.bs, loc);
    JournalSystemRef.RefinesInit(s.js, loc);
  }

  lemma RefinesNext(s: BJS.Variables, s': BJS.Variables, uiop: UI.Op)
  requires BJS.Inv(s)
  requires BJS.Next(s, s', uiop)
  ensures BJS.Inv(s')
  ensures CompositeView.Next(I(s), I(s'), uiop)
  {
    BJS.NextPreservesInv(s, s', uiop);
    var vop :|
      && VOpAgreesUIOp(vop, uiop)
      && BS.Next(s.bs, s'.bs, vop)
      && JS.Next(s.js, s'.js, vop);
    BS.NextPreservesInv(s.bs, s'.bs, vop);
    JS.NextPreservesInv(s.js, s'.js, vop);
    BetreeSystemRef.RefinesNext(s.bs, s'.bs, vop);
    JournalSystemRef.RefinesNext(s.js, s'.js, vop);
    var step := CompositeView.Step(vop);
    assert CompositeView.NextStep(I(s), I(s'),
      step.vop, uiop);
  }
}
