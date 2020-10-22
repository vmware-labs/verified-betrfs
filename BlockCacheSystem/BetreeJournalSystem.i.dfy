include "BetreeSystem.i.dfy"
include "JournalSystem.i.dfy"
include "BetreeSystem_Refines_StatesViewMap.i.dfy"
include "JournalSystem_Refines_JournalView.i.dfy"

module BetreeJournalSystem {
  import BS = BetreeSystem
  import JS = JournalSystem

  import BetreeSystemRef = BetreeSystem_Refines_StatesViewMap
  import JournalSystemRef = JournalSystem_Refines_JournalView
  import opened ViewOp
  import UI
  import BlockDisk
  import JournalDisk

  datatype Variables = Variables(bs: BS.Variables, js: JS.Variables)

  predicate InitWithLoc(s: Variables, loc: Loc)
  {
    && BS.Init(s.bs, loc)
    && JS.Init(s.js, loc)
  }

  predicate Init(s: Variables)
  {
    exists loc :: InitWithLoc(s, loc)
  }

  predicate Next(s: Variables, s': Variables, uiop: UI.Op)
  {
    exists vop ::
      && VOpAgreesUIOp(vop, uiop)
      && BS.Next(s.bs, s'.bs, vop)
      && JS.Next(s.js, s'.js, vop)
  }

  predicate Inv(s: Variables)
  {
    && BS.Inv(s.bs)
    && JS.Inv(s.js)
  }

  lemma InitImpliesInv(s: Variables)
  requires Init(s)
  ensures Inv(s)
  {
    var loc :|
      && BS.Init(s.bs, loc)
      && JS.Init(s.js, loc);
    BS.InitImpliesInv(s.bs, loc);
    JS.InitImpliesInv(s.js, loc);
  }

  lemma NextPreservesInv(s: Variables, s': Variables, uiop: UI.Op)
  requires Inv(s)
  requires Next(s, s', uiop)
  ensures Inv(s')
  {
    var vop :|
      && VOpAgreesUIOp(vop, uiop)
      && BS.Next(s.bs, s'.bs, vop)
      && JS.Next(s.js, s'.js, vop);
    BS.NextPreservesInv(s.bs, s'.bs, vop);
    JS.NextPreservesInv(s.js, s'.js, vop);
  }

  /*lemma OkaySendPersistentLocStep(s: Variables, s': Variables, vop: VOp)
  requires Inv(s)
  //requires BS.Machine(s.bs, s'.bs, BlockDisk.NoDiskOp, vop)
  //requires BS.M.Next(s.bs.machine, s'.bs.machine, BlockDisk.NoDiskOp, vop)
  //requires BS.D.Next(s.bs.disk, s'.bs.disk, BlockDisk.NoDiskOp)
  requires JS.Next(s.js, s'.js, vop)
  ensures
    (vop.SendPersistentLocOp? ==>
      BS.Inv(s.bs) ==>
        && vop.loc in BS.Ref.DiskGraphMap(s.bs)
        && BS.BT.Inv(BS.BT.Variables(BS.BI.Variables(BS.Ref.DiskGraphMap(s.bs)[vop.loc])))
    )
  {
    if vop.SendPersistentLocOp? {
      //assert I(s).jc.persistentLoc in I(s).tsm.disk;
      assert JS.PersistentLoc(s.js) in BS.Ref.DiskGraphMap(s.bs);
      JS.FinishLoadingSuperblockPhaseStepPreservesJournals(
          s.js, s'.js, JournalDisk.NoDiskOp, vop);
      //assert vop.loc == I(s).jc.persistentLoc;
    }
  }*/
}
