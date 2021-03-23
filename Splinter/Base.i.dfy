include "../lib/Lang/NativeTypes.s.dfy"
include "../lib/Base/sequences.i.dfy"
include "../lib/Base/Option.s.dfy"
include "../lib/Base/Maps.i.dfy"

// TODO replace this stuff with the real key, value, message definitions

module MessageMod {
  type Key(!new,==)
  type Value(!new)
  type Message(!new)

  function AllKeys() : iset<Key> {
    iset key:Key | true
  }

  function DefaultValue() : Value
    // TODO
}

module InterpMod {
  import opened MessageMod

  datatype Interp = Interp(mi:imap<Key, Value>, seqEnd: nat)
  {
    predicate WF() {
      // TODO How is ImapComplete not in Maps.i?
      forall k :: k in mi
    }
  }

  predicate InDomain(k: Key) { true }

  function Empty() : Interp
    ensures Empty().WF()
  {
    Interp(imap k | InDomain(k) :: DefaultValue(), 0)
  }
  
}

