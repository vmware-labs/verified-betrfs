include "Message.s.dfy"
include "../lib/Base/Option.s.dfy"
include "../lib/Base/Sequences.i.dfy"
include "../lib/Base/Maps.i.dfy"

/*
 * Helper module that deals with a collection of messages read from a splinterTree/BranchTree
 */
module MsgSeqMod {
  import opened Options
  import opened ValueMessage
  import opened Maps
  import opened Sequences

  function CombineDeltasNoDefine(msgSeq : seq<Message>) : (out : Option<Message>)
  function CombineDeltasWithDefine(msgSeq : seq<Message>) : (out : Option<Message>)
    ensures out.Some? ==> out.value.Define?

}
