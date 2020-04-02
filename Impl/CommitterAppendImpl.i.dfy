include "CommitterAppendModel.i.dfy"
include "CommitterImpl.i.dfy"

module CommitterAppendImpl {
  import opened NativeTypes
  import opened Options

  import opened DiskLayout
  import opened KeyType
  import opened ValueType
  import opened Journal

  import opened CommitterModel
  import opened StateModel
  import opened IOModel
  import CommitterAppendModel
  import opened CommitterImpl
  import JournalistImpl

  method JournalAppend(
      k: Constants, cm: Committer,
      key: Key, value: Value)
  requires cm.Inv()
  requires cm.status == CommitterModel.StatusReady
  requires JournalistModel.canAppend(
    cm.journalist.I(), JournalInsert(key, value))
  modifies cm.Repr
  ensures cm.Inv()
  ensures cm.Repr == old(cm.Repr)
  ensures cm.I() == CommitterAppendModel.JournalAppend(
      k, old(cm.I()), key, value)
  {
    CommitterAppendModel.reveal_JournalAppend();
    cm.reveal_ReprInv();

    var je := JournalInsert(key, value);
    cm.journalist.append(je);

    cm.reveal_ReprInv();
  }
}
