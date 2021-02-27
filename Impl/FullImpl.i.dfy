// Copyright 2018-2021 VMware, Inc.
// SPDX-License-Identifier: MIT

include "StateBCImpl.i.dfy"
include "StateModel.i.dfy"
include "CommitterImpl.i.dfy"

module FullImpl {
  import opened Options
  import opened StateBCImpl
  import opened CommitterImpl
  import opened DiskOpImpl
  import StateModel
  import JC = JournalCache

  linear datatype Full = Full(
    linear bc: Variables,
    linear jc: Committer
  )
  {
    predicate W()
    {
      && this.bc.W()
      && this.jc.WF()
    }

    function I() : StateModel.Variables
    requires W()
    {
      StateModel.Variables(bc.I(), jc)
    }

    predicate WF()
    {
      && W()
      && this.bc.WF()
      && this.jc.WF()
    }

    predicate Inv()
    {
      && W()
      && StateModel.Inv(I())
    }

    static method Constructor() returns (linear f: Full)
    ensures f.Inv()
    ensures f.bc.Unready?
    ensures f.jc.I() == JC.LoadingSuperblock(
            None, None,
            JC.SuperblockUnfinished,
            JC.SuperblockUnfinished,
            map[])
    {
      linear var bc := StateBCImpl.Variables.Constructor();
      linear var cm := CommitterImpl.Committer.Constructor();
      f := Full(bc, cm);

      assert f.Inv();
    }
  }
}
