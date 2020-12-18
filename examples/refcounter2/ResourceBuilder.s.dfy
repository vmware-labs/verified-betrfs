include "Frac.s.dfy"
include "ResourceSpec.s.dfy"
include "../../lib/Base/Options.s.dfy"

abstract module ResourceBuilder refines ResourceSpec {
  import FracLogic
  import Rationals
  import opened Options

  type V(==,!new)

  /*
   * User-provided properties
   */

  type Q
  function qconst(v: V) : Q
  function qexc(v: V) : Q
  function qconst_v(q: Q) : Option<V>

  datatype Variables = Variables(m: multiset<Q>, saved: multiset<V>)
  predicate Init(s: Variables)
  predicate transform(a: multiset<Q>, b: multiset<Q>)

  predicate NewExc(s: Variables, s': Variables)
  {
    exists v ::
      && s'.saved == s.saved + multiset{v}
      && s'.m == s.m + multiset{Exc(v)}
  }

  predicate InternalStep(s: Variables, s': Variables)
  {
    && s'.saved == s.saved
    && (exists a, b, c ::
      s.m == a + c && s'.m == b + c && transform(a, b))
  }

  predicate QNext(s: Variables, s': Variables)
  {
    || NewExc(s, s')
    || NewExc(s', s)
    || InternalStep(s, s')
  }

  predicate QInv(s: Variables)

  lemma InitImpliesQInv(s: Variables)
  requires Init(s)
  ensures QInv(s)

  lemma NextPreservesQInv(s: Variables, s': Variables)
  requires QInv(s)
  requires QNext(s, s')
  ensures QInv(s')

  lemma QInvWorksConst(s: Variables, v: V)
  requires QInv(s)
  requires qconst(v) in s.m
  ensures v in s.saved

  lemma QInvWorksExc(s: Variables, v: V)
  requires QInv(s)
  requires qexc(v) in s.m
  ensures v in s.saved

  /*
   * Const logic
   */

  datatype R =
    | RG(s: Variables, fracs: map<V, multiset<RationalFraction>>)
    | RFrac(v: V, r: Rationals.PositiveRational)
    | Internal(q: Q)

  linear datatype PreConst = Const(
      linear rf: FracLogic.Frac<V>,
      linear r: R)
  {
    function value() : V {
      this.rf.v
    }

    predicate WF() {
      && this.r == RFrac(this.rf.v, this.rf.r)
    }
  }

  type Const = c : PreConst | c.WF()
      witness (assume false; var c:PreConst :| true; c) // XXX

  function method borrow(shared con: Const) : (shared v : V)
  {
    FracLogic.borrow(con.rf)
  }

  linear datatype G = G(store: LinearMap<V, Frac<V>>, state: R)

  predicate HasQuote(store: LinearMap<V, Frac<V>>, m: multiset<V>, v: V)
  {
    var n := CountValue(m, v);
    (n > 0 ==> 
      && v in store
      && store[v].v == v
      && Rational.lt(Rational.of_nat(n-1), store[v].r)
    )
  }

  predicate GInv(g: G)
  {
    && g.state.RG?
    && QInv(g.state.s)
    && (forall v :: HasQuota(store, state.saved, v))
  }

  method unsafe_obtain() returns (linear g: G)
  ensures GInv(g)

  method unsafe_dispose(linear g: G)
  requires GInv(g)

  method acquire_const(linear r: R)
  returns (linear c: Const)
  requires r.Internal? && qconst_v(r.q).Some?
  ensures c.value() == qconst_v(r.q).value
  {
    linear var g := unsafe_obtain();

    linear var G(store, state) := g;

    var v := qconst_v(r.q);

    var count := CountValue(state.s.saved, qconst_v(r.q));
    CountValue_ge_1(state.s.saved, qconst_v(r.q));
    assert count > 0;

    var mid := RationalUtil.in_between(lower, upper);

    linear var store', v_frac := LinearMap.remove(store, v);
    linear var (v_frac', v_frac_lend) := FracLogic.frac_split(v_frac, mid);
    store := LinearMap.add(v, v_frac');

    linear var state', frac_tracker := transform_1_2(state,
        state.(fracs := state.fracs[v := state.fracs[v] + multiset{v_frac_lend}]),
        RFrac(v, v_frac_lend));

    c := Const(
      v_frac_lend,
      frac_tracker);

    unsafe_dispose(G(store, state'));
  }
}
