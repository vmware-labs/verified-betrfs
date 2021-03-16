// Copyright 2018-2021 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, and University of Washington
// SPDX-License-Identifier: BSD-2-Clause

include "StateBCImpl.i.dfy"
include "CommitterImpl.i.dfy"

module FullImpl {
  import opened Options
  import opened StateBCImpl
  import opened CommitterImpl
  import opened DiskOpImpl
  import JC = JournalCache
  import BJC = BlockJournalCache

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

    function I() : BJC.Variables
    requires W()
    {
      BJC.Variables(bc.I(), jc.I())
    }

    predicate WF()
    {
      && W()
      && bc.WFBCVars()
    }

    predicate Inv()
    {
      && WF()
      && bc.Inv()
      && jc.Inv()
      && BJC.Inv(I())
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
