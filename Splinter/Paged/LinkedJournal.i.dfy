

module LinkedJournal {
  type Pointer = nat

  datatype JournalRecord = JournalRecord(
    messageSeq: MsgHistory,
    priorRec: Option<Pointer>
  )
  {
    function I(cacheView: CacheView) : PagedJournalIfc.JournalRecord
    {
      PagedJournalIfc.JournalRecord(messageSeq,
        if priorRec.None?
        then None
        else if priorRec.value !in cacheView
        then None
        else Some(cacheView[priorRec.value].I(cacheView))
      )
    }
  }

  type CacheView = map<Pointer, JournalRecord>

  datatype TruncatedJournal = TruncatedJournal(
    boundaryLSN : LSN,  // exclusive: lsns <= boundaryLSN are discarded
    freshestRec: Option<Pointer>,
    cacheView: CacheView)
  {
    function I() : PagedJournalIfc.TruncatedJournal
    {
  
    }
  }


}
