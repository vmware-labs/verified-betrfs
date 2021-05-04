include "AppSpec.s.dfy"

// You can build your ShardedStateMachine out of smaller monoids. Code holding
// a glinear monoid can be split and joined, but not transformed until they're
// upgraded to a ShardedStateMachine resource. The upgrade mechanism isn't clear.
abstract module PartialCommutativeMonoid {
  type Variables(==, !new) // TODO user can't construct/destruct the Variables?
  function unit() : Variables
  function add(x: Variables, y: Variables) : Variables

  predicate le(x: Variables, y: Variables)
  {
    exists x1 :: add(x, x1) == y
  }

  function pow(x: Variables, n: nat) : Variables
  {
    if n == 0 then unit() else add(pow(x, n-1), x)
  }

  lemma add_unit(x: Variables)
  ensures add(x, unit()) == x

  lemma commutative(x: Variables, y: Variables)
  ensures add(x, y) == add(y, x)

  lemma associative(x: Variables, y: Variables, z: Variables)
  ensures add(x, add(y, z)) == add(add(x, y), z)

  predicate Valid(s: Variables)

  lemma valid_monotonic(x: Variables, y: Variables)
  requires Valid(add(x, y))
  ensures Valid(x)
}

abstract module ShardedStateMachine refines PartialCommutativeMonoid {
  import Ifc = MapIfc // TODO more module system crime. Wish this were a parameter we could apply later.
  
  // The state machine's variables are the (refined)
  // PartialCommutativeMonoid.Variables.  Being PCM makes them "shardable", so
  // we can split them off and cart them around separately.

  predicate Init(s: Variables)
  predicate Next(s: Variables, s': Variables)

  // The Valid predicate is true over any 'valid' Variables, even those that are
  // fragments of the whole system state.  Contrast with Inv, which is an
  // invariant that's only true over whole system states.
  lemma update_monotonic(x: Variables, y: Variables, z: Variables)
  requires Next(x, y)
  requires Valid(add(x, z))
  ensures Next(add(x, z), add(y, z))

  glinear method {:extern} resources_obey_inv(glinear b: Variables)
  ensures Valid(b)

  glinear method {:extern} do_transform(
      glinear b: Variables,
      ghost expected_out: Variables)
  returns (glinear c: Variables)
  requires Next(b, expected_out)
  ensures c == expected_out

  function method {:extern} get_unit() : (glinear u: Variables)
  ensures u == unit()

  function method {:extern} get_unit_shared() : (gshared u: Variables)
  ensures u == unit()

  function method {:extern} join(glinear a: Variables, glinear b: Variables) : (glinear sum: Variables)
  ensures sum == add(a, b)

  glinear method {:extern} split(glinear sum: Variables, ghost a: Variables, ghost b: Variables)
  returns (glinear a': Variables, glinear b': Variables)
  requires sum == add(a, b)
  ensures a' == a && b' == b

  glinear method {:extern} sub(gshared s: Variables, ghost t: Variables)
  returns (glinear t': Variables)
  requires le(t, s)
  ensures t' == t

  // Refining module (.i) needs to prove these properties
  // in order to reap the benefit from the meta-properties above.

  lemma InitImpliesValid(s: Variables)
  requires Init(s)
  ensures Valid(s)

  lemma NextPreservesValid(s: Variables, s': Variables)
  requires Next(s, s')
  requires Valid(s)
  ensures Valid(s')

  // IO interface -- explains how your SSM interacts with user-visible IO events.

  function input_ticket(id: int, input: Ifc.Input) : Variables
  function output_stub(id: int, output: Ifc.Output) : Variables

  lemma NewTicketPreservesValid(r: Variables, id: int, input: Ifc.Input)
    requires Valid(r)
    ensures Valid(add(r, input_ticket(id, input)))

  // The resulting IO-enhanced state machine
  predicate Internal(s: Variables, s': Variables)
  {
    Next(s, s')
  }

  predicate NewTicket(s: Variables, s': Variables, id: int, input: Ifc.Input)
  {
    s' == add(s, input_ticket(id, input))
  }

  predicate ReturnStub(s: Variables, s': Variables, id: int, output: Ifc.Output)
  {
    // Note s',s in unusual order to express subtraction
    s == add(s', output_stub(id, output))
  }
}
