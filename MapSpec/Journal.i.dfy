include "../lib/Base/KeyType.s.dfy"
include "../lib/Base/Message.i.dfy"

module Journal {
  import opened KeyType 
  import opened ValueMessage
  import UI

  datatype JournalEntry = JournalInsert(key: Key, msg: Message)

  function JournalEntriesForUIOp(uiop: UI.Op) : seq<JournalEntry>
  {
    if uiop.PutOp? then
      [JournalInsert(uiop.key, Define(uiop.value))]
    else
      []
  }
}
