include "BetreeSystem.i.dfy"
include "JournalSystem.i.dfy"
include "BetreeSystem_Refines_StatesViewMap.i.dfy"
include "JournalSystem_Refines_JournalView.i.dfy"

module BetreeJournalSystem {
  import BS = BetreeSystem
  import JS = JournalSystem

  //import BlockSystemRef = BlockSystem_Refines_StatesView
  import BetreeSystemRef = BetreeSystem_Refines_StatesViewMap
  import JournalSystemRef = JournalSystem_Refines_JournalView
  import CompositeView

  datatype Constants = Constants(bs: BS.Constants, js: JS.Constants)
  datatype Variables = Variables(bs: BS.Variables, js: JS.Variables)

  predicate Init(k: Constants, s: Variables)
  {
    exists loc ::
      && BS.Init(k.bs, s.bs, loc)
      && JS.Init(k.js, s.js, loc)
  }

  predicate Next(k: Constants, s: Variables, s': Variables)
  {
    exists vop ::
      && BS.Next(k.bs, s.bs, s'.bs, vop)
      && JS.Next(k.js, s.js, s'.js, vop)
  }

  function Ik(k: Constants) : CompositeView.Constants {
    CompositeView.Constants(
      BetreeSystemRef.Ik(k.bs),
      JournalSystemRef.Ik(k.js)
    )
  }

  function I(k: Constants, s: Variables) : CompositeView.Variables {
    CompositeView.Variables(
      BetreeSystemRef.I(k.bs, s.js),
      JournalSystemRef.I(k.bs, s.js)
    )
  }

  predicate Inv(k: Constants, s: Variables)
  {
    && BS.Inv(k.bs, s.bs)
    && JS.Inv(k.js, s.js)
    //&& JS.PersistentLoc(s.js) in BS.BetreeDisk(k.bs, s.bs)
    && CompositeView.Inv(Ik(k), I(s))
  }

  lemma InitImpliesInv(k: Constants, s: Variables)
  requires Init(k, s)
  ensures Inv(k, s)
  {
    var loc :|
      && BS.Init(k.bs, s.bs, loc)
      && JS.Init(k.js, s.js, loc);
    BS.InitImpliesInv(k.bs, s.bs, loc);
    JS.InitImpliesInv(k.js, s.js, loc);
  }

  lemma NextImpliesInv(k: Constants, s: Variables, s': Variables)
  requires Inv(k, s)
  requires Next(k, s, s')
  ensures Inv(k, s')
  {
    var vop :|
      && BS.Next(k.bs, s.bs, s'.bs, vop)
      && JS.Next(k.js, s.js, s'.js, vop);
    BS.NextPreservesInv(k.bs, s.bs, s'.bs, vop);
    JS.NextPreservesInv(k.js, s.js, s'.js, vop);

    //var step :| BS.NextStep(k.bs, s.bs, s'.bs, vop);
    //BlockSystemRef.StepGraphs(k.bs, s.bs, s'.bs, vop

  }

  lemma InvImpliesPersistentLocInGraph(k: Constants, s: Variables)
  requires Inv(k, s)
  ensures JS.PersistentLoc(s.js) in BS.BetreeDisk(k.bs, s.bs)
  {
  }
}
