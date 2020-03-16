include "../lib/Base/KeyType.s.dfy"
include "../lib/Base/Message.i.dfy"
include "../lib/Base/sequences.i.dfy"
include "UI.s.dfy"

module Journal {
  import opened KeyType 
  import opened ValueMessage
  import opened Sequences
  import UI

  datatype JournalEntry = JournalInsert(key: Key, value: Value)

  function JournalEntriesForUIOp(uiop: UI.Op) : seq<JournalEntry>
  {
    if uiop.PutOp? then
      [JournalInsert(uiop.key, uiop.value)]
    else
      []
  }

  function JournalEntriesForUIOps(uiops: seq<UI.Op>) : seq<JournalEntry>
  {
    if uiops == [] then
      []
    else
      JournalEntriesForUIOps(DropLast(uiops))
          + JournalEntriesForUIOp(Last(uiops))
  }

  lemma JournalEntriesForUIOpsAdditive(a: seq<UI.Op>, b: seq<UI.Op>)
  ensures JournalEntriesForUIOps(a + b)
      == JournalEntriesForUIOps(a) + JournalEntriesForUIOps(b)
  {
  }
}
