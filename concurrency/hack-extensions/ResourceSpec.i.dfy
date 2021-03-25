include "MinimalResourceSpec.s.dfy"

module ResourceSpec refines MinimalResourceSpec {
  predicate Update(s: R, s': R)

  lemma update_monotonic(x: R, y: R, z: R)
  requires Update(x, y)
  requires Valid(add(x, z))
  ensures Update(add(x, z), add(y, z))

  function method is_valid_linear(linear b: R) : ()
  ensures Valid(b)
  {
    add_unit(b);
    commutative(unit(), b);
    is_valid(get_unit_shared(), b)
  }

  function method do_transform_linear(
      linear b: R,
      ghost expected_out: R)
    : (linear c: R)
  requires Update(b, expected_out)
  ensures c == expected_out
  {
    assert add(unit(), b) == b by {
      commutative(unit(), b);
      add_unit(b);
    }
    assert add(unit(), expected_out) == expected_out by {
      commutative(unit(), expected_out);
      add_unit(expected_out);
    }
    assert frame_preserving(b, expected_out) by {
      forall x | Valid(add(b, x)) ensures Valid(add(expected_out, x))
      {
        update_monotonic(b, expected_out, x);
        UpdatePreservesValid(add(b, x), add(expected_out, x));
      }
    }
    frame_preserving_update(get_unit_shared(), b, expected_out)
  }

  // Refining module needs to prove these properties
  // in order to reap the benefit from the meta-properties above.

  lemma UpdatePreservesValid(s: R, t: R)
  requires Update(s, t)
  requires Valid(s)
  ensures Valid(t)
}
