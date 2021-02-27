// Copyright 2018-2021 VMware, Inc.
// SPDX-License-Identifier: MIT

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

  datatype Variables = Variables(bs: BS.Variables, js: JS.Variables)

  function I(s: Variables) : CompositeView.Variables
  requires BS.Inv(s.bs)
  requires JS.Inv(s.js)
  {
    CompositeView.Variables(
      BetreeSystemRef.I(s.bs),
      JournalSystemRef.I(s.js)
    )
  }

  predicate InitWithLoc(s: Variables, loc: Loc)
  {
    && BS.Init(s.bs, loc)
    && JS.Init(s.js, loc)
    && (
      BS.InitImpliesInv(s.bs, loc);
      JS.InitImpliesInv(s.js, loc);
      CompositeView.Init(I(s))
    )
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
    //&& JS.PersistentLoc(s.js) in BS.BetreeDisk(s.bs)
    && CompositeView.Inv(I(s))
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
    CompositeView.InitImpliesInv(I(s));
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
    BetreeSystemRef.RefinesNext(s.bs, s'.bs, vop);
    JournalSystemRef.RefinesNext(s.js, s'.js, vop);
    var step := CompositeView.Step(vop);
    assert CompositeView.NextStep(I(s), I(s'),
      step.vop, uiop);
    CompositeView.NextPreservesInv(I(s), I(s'), uiop);
  }


  lemma OkaySendPersistentLocStep(s: Variables, s': Variables, vop: VOp)
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
      assert I(s).jc.persistentLoc in I(s).tsm.disk;
      JS.FinishLoadingSuperblockPhaseStepPreservesJournals(
          s.js, s'.js, JournalDisk.NoDiskOp, vop);
      assert vop.loc == I(s).jc.persistentLoc;
    }
  }
}
