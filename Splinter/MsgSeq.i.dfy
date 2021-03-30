include "Allocation.i.dfy"

module MsgSeqMod {
  import opened MessageMod
  import opened InterpMod

  datatype MsgSeq = MsgSeq(msgs: map<LSN, Message>, seqStart: LSN, seqEnd: LSN)
    // seqEnd is exclusive
  {
    predicate WF()
    {
      forall k :: k in msgs <==> seqStart <= k < seqEnd
    }

    // Add a single message to the end of the sequence. It gets LSN 'seqEnd', since
    // that's exclusive (points at the next empty slot).
    function Extend(m: Message) : MsgSeq
    {
      MsgSeq(
        map k | k in Keys + { seqEnd } :: if k == seqEnd then m else msgs[k],
        seqStart,
        seqEnd+1)
    }
  }

  function Empty() : MsgSeq
  {
    MsgSeq(map[], 0, 0)
  }

  function IKey(key:Key, baseValue:Value, ms: MsgSeq) : Value
    requires ms.WF()
    // Gaah look up existing message delta definitions. For
    // replacement/deletion messages, returns the value in the most-recent
    // message matching key else baseValue.

  function Concat(interp: Interp, ms:MsgSeq) : Interp
    requires interp.WF()
    requires ms.WF()
    requires interp.seqEnd == ms.seqStart
  {
    Interp(imap k | InDomain(k) :: IKey(k, interp.mi[k], ms), ms.seqEnd)
  }
}
