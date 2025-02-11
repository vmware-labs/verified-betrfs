// Copyright 2018-2021 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, and University of Washington
// SPDX-License-Identifier: BSD-2-Clause

include "../lib/Base/KeyType.s.dfy"
include "../lib/Base/Message.i.dfy"
include "../lib/Base/Sequences.i.dfy"
include "UI.s.dfy"

module Journal {
  import opened KeyType 
  import opened ValueMessage
  import opened Sequences
  import UI

  datatype JournalEntry = JournalInsert(key: Key, value: Value) | JournalClone(from: Key, to: Key)

  function JournalEntriesForUIOp(uiop: UI.Op) : seq<JournalEntry>
  {
    if uiop.PutOp? then
      [JournalInsert(uiop.key, uiop.value)]
    else if uiop.CloneOp? then
      [JournalClone(uiop.from, uiop.to)]
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

  function JournalEntryToUIOp(je: JournalEntry) : UI.Op
  {
    match je {
      case JournalInsert(key, value) => UI.PutOp(key, value)
      case JournalClone(from, to) => UI.CloneOp(from, to)
    }
  }
}
