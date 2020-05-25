include "CommitterReplayModel.i.dfy"
include "CommitterImpl.i.dfy"
include "DiskOpImpl.i.dfy"

module CommitterReplayImpl {
  import opened NativeTypes
  import opened Options

  import opened DiskLayout
  import opened KeyType
  import opened ValueType
  import opened Journal

  import opened DiskOpImpl
  import opened CommitterModel
  import CommitterReplayModel
  import opened CommitterImpl
  import JournalistImpl

  method JournalReplayOne(k: ImplConstants, cm: Committer)
  requires cm.Inv()
  requires cm.status == CommitterModel.StatusReady
  requires !JournalistModel.isReplayEmpty(cm.journalist.I())
  modifies cm.Repr
  ensures cm.Inv()
  ensures cm.Repr == old(cm.Repr)
  ensures cm.I() == CommitterReplayModel.JournalReplayOne(
      Ic(k), old(cm.I()))
  {
    CommitterReplayModel.reveal_JournalReplayOne();
    cm.reveal_ReprInv();

    cm.journalist.replayJournalPop();

    cm.reveal_ReprInv();
  }
}
