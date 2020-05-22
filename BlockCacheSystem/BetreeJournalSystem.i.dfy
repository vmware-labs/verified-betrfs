include "BetreeSystem.i.dfy"
include "JournalSystem.i.dfy"
include "BetreeSystem_Refines_StatesViewMap.i.dfy"
include "JournalSystem_Refines_JournalView.i.dfy"
include "../Versions/CompositeView.i.dfy"

module BetreeJournalSystem {
  import BS = BetreeSystem
  import JS = JournalSystem

  import BetreeSystemRef = BetreeSystem_Refines_StatesViewMap
  import JournalSystemRef = JournalSystem_Refines_JournalView
  import CompositeView
  import opened ViewOp
  import UI
  import BlockDisk
  import JournalDisk

  datatype Constants = Constants(bs: BS.Constants, js: JS.Constants)
  datatype Variables = Variables(bs: BS.Variables, js: JS.Variables)

  function Ik(k: Constants) : CompositeView.Constants {
    CompositeView.Constants(
      BetreeSystemRef.Ik(k.bs),
      JournalSystemRef.Ik(k.js)
    )
  }

  function I(k: Constants, s: Variables) : CompositeView.Variables
  requires BS.Inv(k.bs, s.bs)
  requires JS.Inv(k.js, s.js)
  {
    CompositeView.Variables(
      BetreeSystemRef.I(k.bs, s.bs),
      JournalSystemRef.I(k.js, s.js)
    )
  }

  predicate InitWithLoc(k: Constants, s: Variables, loc: Loc)
  {
    && BS.Init(k.bs, s.bs, loc)
    && JS.Init(k.js, s.js, loc)
    && (
      BS.InitImpliesInv(k.bs, s.bs, loc);
      JS.InitImpliesInv(k.js, s.js, loc);
      CompositeView.Init(Ik(k), I(k, s))
    )
  }

  predicate Init(k: Constants, s: Variables)
  {
    exists loc :: InitWithLoc(k, s, loc)
  }

  predicate Next(k: Constants, s: Variables, s': Variables, uiop: UI.Op)
  {
    exists vop ::
      && VOpAgreesUIOp(vop, uiop)
      && BS.Next(k.bs, s.bs, s'.bs, vop)
      && JS.Next(k.js, s.js, s'.js, vop)
  }

  predicate Inv(k: Constants, s: Variables)
  {
    && BS.Inv(k.bs, s.bs)
    && JS.Inv(k.js, s.js)
    //&& JS.PersistentLoc(s.js) in BS.BetreeDisk(k.bs, s.bs)
    && CompositeView.Inv(Ik(k), I(k, s))
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
    CompositeView.InitImpliesInv(Ik(k), I(k, s));
  }

  lemma NextPreservesInv(k: Constants, s: Variables, s': Variables, uiop: UI.Op)
  requires Inv(k, s)
  requires Next(k, s, s', uiop)
  ensures Inv(k, s')
  {
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

//~  lemma InvImpliesPersistentLocInGraph(k: Constants, s: Variables)
//~  requires Inv(k, s)
//~  ensures JS.PersistentLoc(s.js) in BS.BetreeDisk(k.bs, s.bs)
//~  {
//~  }

  lemma OkaySendPersistentLocStep(k: Constants, s: Variables, s': Variables, vop: VOp)
  requires Inv(k, s)
  //requires BS.Machine(k.bs, s.bs, s'.bs, BlockDisk.NoDiskOp, vop)
  //requires BS.M.Next(k.bs.machine, s.bs.machine, s'.bs.machine, BlockDisk.NoDiskOp, vop)
  //requires BS.D.Next(k.bs.disk, s.bs.disk, s'.bs.disk, BlockDisk.NoDiskOp)
  requires JS.Next(k.js, s.js, s'.js, vop)
  ensures
    (vop.SendPersistentLocOp? ==>
      BS.Inv(k.bs, s.bs) ==>
        && vop.loc in BS.Ref.DiskGraphMap(k.bs, s.bs)
        && BS.BT.Inv(BS.Ik(k.bs), BS.BT.Variables(BS.BI.Variables(BS.Ref.DiskGraphMap(k.bs, s.bs)[vop.loc])))
    )
  {
    if vop.SendPersistentLocOp? {
      assert I(k,s).jc.persistentLoc in I(k,s).tsm.disk;
      JS.FinishLoadingSuperblockPhaseStepPreservesJournals(
          k.js, s.js, s'.js, JournalDisk.NoDiskOp, vop);
      assert vop.loc == I(k,s).jc.persistentLoc;
    }
  }
}
