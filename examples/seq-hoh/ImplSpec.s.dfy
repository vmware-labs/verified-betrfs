include "StateMachine.s.dfy"

abstract module DonateImplSpec {
  import opened SM : StateMachine
  import opened Options

  // TODO create abstract async Donate spec
  // and add proof obligation that SM refines it

  method donate(victim: nat, linear ticket: StateObject)
  returns (outidx: Option<nat>, linear stub: StateObject)
  requires exists tid :: ticket == donate_ticket(tid, victim)
  ensures exists tid :: stub == donate_stub(tid, outidx)

  // An infinite number of transform functions that the impl
  // will have access to

  method {:axiom} transform_2_1(
      linear a1: StateObject,
      linear a2: StateObject,
      ghost b: StateObject)
  returns (linear b': StateObject)
  requires transform(multiset{a1, a2}, multiset{b})
  ensures b' == b

  method {:axiom} transform_3_3(
      linear a1: StateObject,
      linear a2: StateObject,
      linear a3: StateObject,
      ghost b1: StateObject,
      ghost b2: StateObject,
      ghost b3: StateObject)
  returns (
    linear b1': StateObject,
    linear b2': StateObject,
    linear b3': StateObject)
  requires transform(multiset{a1, a2, a3}, multiset{b1, b2, b3})
  ensures b1' == b1
  ensures b2' == b2
  ensures b3' == b3

  method {:axiom} transform_3_2(
      linear a1: StateObject,
      linear a2: StateObject,
      linear a3: StateObject,
      ghost b1: StateObject,
      ghost b2: StateObject)
  returns (
    linear b1': StateObject,
    linear b2': StateObject)
  requires transform(multiset{a1, a2, a3}, multiset{b1, b2})
  ensures b1' == b1
  ensures b2' == b2

  method {:axiom} transform_2_3(
      linear a1: StateObject,
      linear a2: StateObject,
      ghost b1: StateObject,
      ghost b2: StateObject,
      ghost b3: StateObject)
  returns (
    linear b1': StateObject,
    linear b2': StateObject,
    linear b3': StateObject)
  requires transform(multiset{a1, a2}, multiset{b1, b2, b3})
  ensures b1' == b1
  ensures b2' == b2
  ensures b3' == b3

}
