include "../framework/AsyncSSM.s.dfy"
include "../../lib/Lang/NativeTypes.s.dfy"
include "../../lib/Base/Option.s.dfy"
include "../framework/Rw.i.dfy"
include "../../lib/Base/Maps.i.dfy"

module OG refines Rw {
  datatype M = M(
    ghost counter: Option<nat>,
    ghost inc_a: Option<bool>,
    ghost inc_b: Option<bool>
  ) | Fail

  /*
   * ============================================================================================
   * Invariant
   * ============================================================================================
   */

  predicate Inv(x: M) {
    x != unit() ==> (
      && x.M?
      && x.counter.Some?
      && x.inc_a.Some?
      && x.inc_b.Some?
      && x.counter.value ==
          (if x.inc_a.value then 1 else 0) +
          (if x.inc_b.value then 1 else 0)
    )
  }

  lemma inv_unit()
  ensures Inv(unit())
  ensures I(unit()) == None
  {
  }

  /*
   * ============================================================================================
   * Initialization
   * ============================================================================================
   */

  predicate Init(s: M) {
    s == M(
        Some(0),
        Some(false),
        Some(false)
    )
  }

  lemma InitImpliesInv(x: M)
    requires Init(x)
    ensures Inv(x)
  {
  }

   /*
   * ============================================================================================
   * Dot
   * ============================================================================================
   */

  function dot(x: M, y: M) : M {
    if (
      && x.M?                &&  y.M?
      && !(x.counter.Some?  &&  y.counter.Some?)
      && !(x.inc_a.Some?  &&  y.inc_a.Some?)
      && !(x.inc_b.Some?  &&  y.inc_b.Some?)
    )
    then
      M(
        if x.counter.Some? then x.counter else y.counter,
        if x.inc_a.Some? then x.inc_a else y.inc_a,
        if x.inc_b.Some? then x.inc_b else y.inc_b
      )
    else
      Fail
  }

  function unit() : M {
    M(None, None, None)
  }

  lemma dot_unit(x: M)
  ensures dot(x, unit()) == x
  {
    assert unit().M?;
    assert dot(unit(), unit()).M?;
    assert dot(unit(), unit()) == unit();
    assert dot(x, unit()) == x;
  }

  lemma commutative(x: M, y: M)
  ensures dot(x, y) == dot(y, x)
  {
    if dot(x, y) == Fail {
      assert dot(x, y) == dot(y, x);
    } else {
      assert dot(x, y) == dot(y, x);
    }
  }

  lemma associative(x: M, y: M, z: M)
  ensures dot(x, dot(y, z)) == dot(dot(x, y), z)
  {
    if dot(x, dot(y, z)) == Fail {
      assert dot(x, dot(y, z)) == dot(dot(x, y), z);
    } else {
      assert dot(x, dot(y, z)) == dot(dot(x, y), z);
    }
  }


  /*
   * ============================================================================================
   * Interpretation Function
   * ============================================================================================
   */
  // don't need?
  function I(x: M) : Option<StoredType> {
    None
  }

  /*
   * ============================================================================================
   * State Transitions
   * ============================================================================================
   */

  // -------------------------------- IncA ------------------------------------------

  predicate DoIncA(m: M, m': M) {
    && m.M?
    && m.inc_a.Some?
    && m.counter.Some?
    && m.inc_a.value == false

    && m' == m
        .(inc_a := Some(true))
        .(counter := Some(m.counter.value + 1))
  }

  lemma DoIncA_is_transition(m: M, m': M)
  requires DoIncA(m, m')
  ensures transition(m, m')
  {

  }

  // -------------------------------- IncB ------------------------------------------

  predicate DoIncB(m: M, m': M) {
    && m.M?
    && m.inc_b.Some?
    && m.counter.Some?
    && m.inc_b.value == false

    && m' == m
        .(inc_b := Some(true))
        .(counter := Some(m.counter.value + 1))
  }

  lemma DoIncB_is_transition(m: M, m': M)
  requires DoIncB(m, m')
  ensures transition(m, m')
  {

  }

}
