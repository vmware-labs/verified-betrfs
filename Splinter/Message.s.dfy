// Copyright 2018-2021 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, and University of Washington
// SPDX-License-Identifier: BSD-2-Clause


include "../lib/Base/KeyType.s.dfy"
include "../lib/Lang/NativeTypes.s.dfy"
include "../lib/Lang/LinearSequence.s.dfy"

abstract module MessageMod {
  type Value(!new)
  type Delta(!new)

  function method NopDelta() : Delta
  function method DefaultValue() : Value

  datatype Message =
    | Define(value: Value)
    | Update(delta: Delta)

  function method CombineDeltas(newdelta: Delta, olddelta: Delta) : (result: Delta)
  ensures newdelta == NopDelta() ==> result == olddelta
  ensures olddelta == NopDelta() ==> result == newdelta

  function method ApplyDelta(delta: Delta, value: Value) : (result: Value)
  ensures delta == NopDelta() ==> result == value

  function method Merge(newmessage: Message, oldmessage: Message) : Message {
    match (newmessage, oldmessage) {
      case (Define(newvalue), _) => Define(newvalue)
      case (Update(newdelta), Update(olddelta)) => Update(CombineDeltas(newdelta, olddelta))
      case (Update(delta), Define(value)) => Define(ApplyDelta(delta, value))
    }
  }

  function method IdentityMessage() : Message {
    Update(NopDelta())
  }

  function method DefaultMessage() : Message {
    Define(DefaultValue())
  }

  lemma DeltaIsAssociative(a: Delta, b: Delta, c: Delta)
    ensures CombineDeltas(CombineDeltas(a, b), c) == CombineDeltas(a, CombineDeltas(b, c))

  lemma ApplyIsAssociative(a: Delta, b: Delta, value: Value)
    ensures ApplyDelta(CombineDeltas(a, b), value) == ApplyDelta(a, ApplyDelta(b, value))

  lemma MergeIsAssociative(a: Message, b: Message, c: Message)
    ensures Merge(Merge(a, b), c) == Merge(a, Merge(b, c))
    {
      match a {
        case Define(a) => { }
        case Update(a) => {
          match b {
            case Define(b) => { }
            case Update(b) => {
              match c {
                case Define(c) => {
                  ApplyIsAssociative(a, b, c);
                }
                case Update(c) => {
                  DeltaIsAssociative(a, b, c);
                }
              }
            }
          }
        }
      }
    }
}

// No Delta Messages
module ValueMessage refines MessageMod {
  import ValueType`Internal
  import opened NativeTypes
  import opened LinearSequence_s
  //import opened Sequences

  type Value = ValueType.Value
  datatype Delta = NoDelta

  function method NopDelta() : Delta { NoDelta }
  function method DefaultValue() : Value { ValueType.DefaultValue() }

  function method CombineDeltas(newdelta: Delta, olddelta: Delta) : Delta { NoDelta }
  function method ApplyDelta(delta: Delta, value: Value) : Value { value }

  lemma DeltaIsAssociative(a: Delta, b: Delta, c: Delta)
  {
  }

  lemma ApplyIsAssociative(a: Delta, b: Delta, value: Value)
  {
  }

  predicate EncodableMessage(msg: Message)
  {
    && msg.Define?
  }

  function EvaluateMessage(m: Message) : Value
    requires m.Define?
  {
     m.value
  }
}
