include "../../../lib/Lang/NativeTypes.s.dfy"
include "../../../lib/Base/Option.s.dfy"
include "ConcurrencyModel.s.dfy"
include "AppSpec.s.dfy"
include "Limits.i.dfy"

// Build up the insert_capacity monoid first so we can talk about it separately
// in the CapacityAllocator impl, and not have to cart around an entire ShardedHashTable.
module Count refines PartialCommutativeMonoid {
  import opened Limits

  datatype Variables = Variables(value: nat)

  function unit() : Variables { Variables(0) }

  function add(x: Variables, y: Variables) : Variables {
    Variables(x.value + y.value)
  }

  lemma add_unit(x: Variables)
  ensures add(x, unit()) == x
  {
  }

  lemma commutative(x: Variables, y: Variables)
  ensures add(x, y) == add(y, x)
  {
  }

  lemma associative(x: Variables, y: Variables, z: Variables)
  ensures add(x, add(y, z)) == add(add(x, y), z)
  {
  }

  predicate Inv(s: Variables)
  {
    s.value <= Capacity()
  }

  predicate Valid(s: Variables)
  {
    exists t :: Inv(add(s, t))
  }

  function {:opaque} GetRemainder(s: Variables): (t: Variables)
    requires Valid(s)
    ensures Inv(add(s, t))
  {
    // reveal Valid();
    var t :| Inv(add(s, t));
    t
  }

  lemma valid_monotonic(x: Variables, y: Variables)
  //requires Valid(add(x, y))
  ensures Valid(x)
  {
  }
}
