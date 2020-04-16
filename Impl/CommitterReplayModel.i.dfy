include "CommitterModel.i.dfy"
include "../ByteBlockCacheSystem/InterpretationDiskOps.i.dfy"
include "DiskOpModel.i.dfy"

module CommitterReplayModel {
  import opened NativeTypes
  import opened Options

  import opened DiskLayout
  import opened InterpretationDiskOps
  import opened ViewOp
  import JournalCache
  import opened KeyType
  import opened ValueType
  import opened Journal

  import opened CommitterModel
  import opened DiskOpModel

  function {:opaque} JournalReplayOne(k: Constants, cm: CM) : (cm' : CM)
  requires CommitterModel.WF(cm)
  requires cm.status == StatusReady
  requires !JournalistModel.isReplayEmpty(cm.journalist)
  {
    var journalist' := JournalistModel.replayJournalPop(cm.journalist);
    cm.(journalist := journalist')
  }

  lemma JournalReplayOneCorrect(k: Constants,
      cm: CM, je: JournalEntry)
  requires CommitterModel.WF(cm)
  requires cm.status == StatusReady
  requires !JournalistModel.isReplayEmpty(cm.journalist)
  requires je == JournalistModel.I(cm.journalist).replayJournal[0]
  ensures var cm' := JournalReplayOne(k, cm);
    && CommitterModel.WF(cm')
    && JournalCache.Next(Ik(k).jc,
        CommitterModel.I(cm), CommitterModel.I(cm'), JournalDisk.NoDiskOp,
        AdvanceOp(UI.PutOp(je.key, je.value), true));
  {
    var cm' := JournalReplayOne(k, cm);
    reveal_JournalReplayOne();
    var vop := AdvanceOp(UI.PutOp(je.key, je.value), true);

    assert JournalCache.Replay(Ik(k).jc,
        CommitterModel.I(cm), CommitterModel.I(cm'), JournalDisk.NoDiskOp,
        vop);
    assert JournalCache.NextStep(Ik(k).jc,
        CommitterModel.I(cm), CommitterModel.I(cm'), JournalDisk.NoDiskOp,
        vop,
        JournalCache.ReplayStep);
  }
}
