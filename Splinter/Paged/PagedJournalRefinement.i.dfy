include "PagedJournalMod.i.dfy"

module PagedJournalRefinement {
  import opened Options
  import opened Sequences
  import opened Maps
  import opened ValueMessage
  import opened KeyType
  import opened StampedMapMod
  import opened MsgHistoryMod
  import opened PagedJournalMod

  function I(v: Variables) : MsgHistory
  {
  }

  lemma InitRefines(v: Variables)
    requires Init(v)
    ensures I(v) == JournalMkfs()
  {
  }

  lemma AppendRefines(v: Variables, v': Variables, lsn: LSN, msg: KeyedMessage)
    requires Append(v, v', msg)
    //requires v. // TODO(jonh): something about lsn == seqend
    ensures var singleton := MsgHistoryMod.Singleton(lsn, KeyedMessage(key, Define(val)));
      I(v') == I(v).Concat(singleton)
  {
  }

  lemma CommitStartRefines(v: Variables, v': Variables, lsn: LSN, msg: KeyedMessage)
}
