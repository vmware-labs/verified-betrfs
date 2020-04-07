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
  decreases |b|
  {
    if b == [] {
      calc {
        JournalEntriesForUIOps(a + b);
        { assert a + b == a; }
        JournalEntriesForUIOps(a);
        JournalEntriesForUIOps(a) + JournalEntriesForUIOps(b);
      } 
    } else {
      calc {
        JournalEntriesForUIOps(a + b);
        JournalEntriesForUIOps(DropLast(a + b)) + JournalEntriesForUIOp(Last(a + b));
        {
          assert DropLast(a + b) == a + DropLast(b);
          assert Last(a + b) == Last(b);
        }
        JournalEntriesForUIOps(a + DropLast(b)) + JournalEntriesForUIOp(Last(b));
        {
          JournalEntriesForUIOpsAdditive(a, DropLast(b));
        }
        JournalEntriesForUIOps(a) + JournalEntriesForUIOps(DropLast(b)) + JournalEntriesForUIOp(Last(b));
        JournalEntriesForUIOps(a) + JournalEntriesForUIOps(b);
      } 
    }
  }
}
