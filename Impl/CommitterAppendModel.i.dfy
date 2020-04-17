include "CommitterModel.i.dfy"
include "IOModel.i.dfy"

module CommitterAppendModel {
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
  import opened IOModel
  import opened DiskOpModel

  function {:opaque} JournalAppend(k: Constants, cm: CM,
      key: Key, value: Value) : (cm' : CM)
  requires CommitterModel.WF(cm)
  requires cm.status == StatusReady
  requires JournalistModel.canAppend(cm.journalist, JournalInsert(key, value))
  {
    var je := JournalInsert(key, value);
    var journalist' := JournalistModel.append(cm.journalist, je);
    cm.(journalist := journalist')
  }

  lemma JournalAppendCorrect(k: Constants,
      cm: CM, key: Key, value: Value)
  requires CommitterModel.WF(cm)
  requires cm.status == StatusReady
  requires JournalistModel.canAppend(cm.journalist, JournalInsert(key, value))
  requires JournalistModel.I(cm.journalist).replayJournal == []
  ensures var cm' := JournalAppend(k, cm, key, value);
    && CommitterModel.WF(cm')
    && JournalCache.Next(Ik(k).jc,
        CommitterModel.I(cm), CommitterModel.I(cm'), JournalDisk.NoDiskOp,
        AdvanceOp(UI.PutOp(key, value), false));
  {
    var cm' := JournalAppend(k, cm, key, value);
    reveal_JournalAppend();

    assert JournalCache.Advance(Ik(k).jc,
        CommitterModel.I(cm), CommitterModel.I(cm'), JournalDisk.NoDiskOp,
        AdvanceOp(UI.PutOp(key, value), false));
    assert JournalCache.NextStep(Ik(k).jc,
        CommitterModel.I(cm), CommitterModel.I(cm'), JournalDisk.NoDiskOp,
        AdvanceOp(UI.PutOp(key, value), false),
        JournalCache.AdvanceStep);
  }
}
