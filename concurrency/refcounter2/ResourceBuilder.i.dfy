include "Frac.s.dfy"
include "ResourceSpec.s.dfy"
include "LinearMap.s.dfy"
include "Multisets.i.dfy"
include "RationalUtil.i.dfy"
include "../../lib/Base/Option.s.dfy"

abstract module ResourceBuilder refines ResourceSpec {
  import FracLogic
  import Rationals
  import LinearMaps
  import RationalUtil
  import opened Options
  import Multisets

  type V(==,!new)

  /*
   * User-provided properties
   */

  type Q(==,!new)

  function qconst(v: V) : (q: Q)
  function qexc(v: V) : Q

  function qconst_v(q: Q) : Option<V>
  ensures qconst_v(q).Some? ==> qconst(qconst_v(q).value) == q

  function qexc_v(q: Q) : Option<V>
  ensures qexc_v(q).Some? ==> qexc(qexc_v(q).value) == q

  //lemma qconst_injective(v: V)
  //ensures qconst_v(qconst(v)) == Some(v)

  datatype Variables = Variables(m: multiset<Q>, saved: multiset<V>)
  predicate qinit(a: multiset<Q>)
  predicate qtransform(a: multiset<Q>, b: multiset<Q>)

  predicate NewExc(s: Variables, s': Variables)
  {
    exists v ::
      && s'.saved == s.saved + multiset{v}
      && s'.m == s.m + multiset{qexc(v)}
  }

  predicate InternalStep(s: Variables, s': Variables)
  {
    && s'.saved == s.saved
    && (exists a, b, c ::
      s.m == a + c && s'.m == b + c && qtransform(a, b))
  }

  predicate QNext(s: Variables, s': Variables)
  {
    || NewExc(s, s')
    || NewExc(s', s)
    || InternalStep(s, s')
  }

  predicate QInv(s: Variables)

  lemma QInitImpliesQInv(s: Variables)
  requires qinit(s.m)
  requires s.saved == multiset{}
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
    | RG(s: Variables, fracs: imap<V, multiset<Rationals.PositiveRational>>)
    | RFrac(v: V, r: Rationals.PositiveRational)
    | Internal(q: Q)

  datatype RStep =
    | ConstToFrac(state: R, v: V, r: Rationals.PositiveRational)

  predicate transform_const_to_frac(a: multiset<R>, b: multiset<R>,
      state: R,
      v: V, r: Rationals.PositiveRational)
  {
    && state.RG?
    && v in state.fracs
    && a == multiset{state, Internal(qconst(v))}
    && b == multiset{
      state.(fracs := state.fracs[v := state.fracs[v] + multiset{r}]),
      RFrac(v, r)
    }
  }

  predicate transform_step(a: multiset<R>, b: multiset<R>, step: RStep)
  {
    match step {
      case ConstToFrac(state, v, r) => transform_const_to_frac(a, b, state, v, r)
    }
  }

  predicate transform(a: multiset<R>, b: multiset<R>)
  {
    exists step :: transform_step(a, b, step)
  }

  function filter_internal(r: R) : Option<Q>
  {
    if r.Internal? then Some(r.q) else None
  }

  function filter_frac_v(r: R, v: V) : Option<Rationals.PositiveRational>
  {
    if r.RFrac? && r.v == v then Some(r.r) else None
  }

  predicate fracs_correct(g: R, s: multiset<R>, v: V)
  requires g.RG?
  {
    && v in g.fracs
    && g.fracs[v] == Multisets.ApplyFilter((r) => filter_frac_v(r, v), s)
  }

  predicate global_inv(g: R, s: multiset<R>)
  requires g.RG?
  {
    && g.s.m == Multisets.ApplyFilter(filter_internal, s)
    && (forall v :: fracs_correct(g, s, v))
  }

  predicate Inv(s: multiset<R>)
  {
    && (forall g | g in s && g.RG? :: global_inv(g, s))
  }

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

  linear datatype G = G(
    linear store: LinearMaps.LinearMap<V, FracLogic.Frac<V>>,
    linear state: R)

  predicate HasQuota(store: LinearMaps.LinearMap<V, FracLogic.Frac<V>>, m: multiset<V>, v: V)
  {
    var n := Multisets.CountValue(v, m);
    var st := LinearMaps.map_of(store);
    (n > 0 ==> 
      && v in st
      && st[v].v == v
      && (n > 1 ==> Rationals.lt(RationalUtil.of_nat(n-1), st[v].r))
    )
  }

  predicate GInv(g: G)
  {
    && g.state.RG?
    && QInv(g.state.s)
    && (forall v :: HasQuota(g.store, g.state.s.saved, v))
  }

  method unsafe_obtain() returns (linear g: G)
  ensures GInv(g)

  method unsafe_dispose(linear g: G)
  requires GInv(g)

  method internal_implies_in_global_saved_set(shared r: R, shared g: R)
  requires r.Internal?
  requires g.RG?
  ensures r.q in g.s.m
  {
    var t := is_allowed_2(r, g);
    assert global_inv(g, t);
    Multisets.ApplyFilterInFwd(filter_internal, t, r);
  }

  method v_in_fracs(shared g: R, ghost v: V)
  requires g.RG?
  ensures v in g.fracs
  {
    var t := is_allowed_1(g);
    assert global_inv(g, t);
    assert fracs_correct(g, t, v);
  }

  method acquire_const(linear r: R)
  returns (linear c: Const)
  requires r.Internal? && qconst_v(r.q).Some?
  ensures c.value() == qconst_v(r.q).value
  {
    linear var g := unsafe_obtain();

    linear var G(store, state) := g;

    ghost var v := qconst_v(r.q).value;
    assert HasQuota(store, state.s.saved, v); // trigger
    ghost var st := LinearMaps.map_of(store);

    assert qconst(v) == r.q;

    internal_implies_in_global_saved_set(r, state);
    assert r.q in state.s.m;

    assert qconst(v) in state.s.m;
    QInvWorksConst(state.s, v);
    ghost var count := Multisets.CountValue(v, state.s.saved);
    Multisets.CountValue_ge_1(v, state.s.saved);
    assert count > 0;

    var mid;
    if count > 1 {
      mid := RationalUtil.in_between(RationalUtil.of_nat(count-1), st[v].r);
    } else {
      mid := RationalUtil.get_smaller(st[v].r);
    }

    linear var store', v_frac;
    store', v_frac := LinearMaps.remove(store, v);
    linear var v_frac', v_frac_lend := FracLogic.frac_split(v_frac, mid);
    store' := LinearMaps.add(store', v, v_frac');

    v_in_fracs(state, v);

    assert transform_step(
        multiset{state, r},
        multiset{
          state.(fracs := state.fracs[v := state.fracs[v] + multiset{v_frac_lend.r}]),
          RFrac(v, v_frac_lend.r)
        },
        ConstToFrac(state, v, v_frac_lend.r)
    );

    linear var state', frac_tracker := transform_2_2(
        state,
        r,
        state.(fracs := state.fracs[v := state.fracs[v] + multiset{v_frac_lend.r}]),
        RFrac(v, v_frac_lend.r));

    c := Const(
      v_frac_lend,
      frac_tracker);

    forall v
    ensures HasQuota(store', state'.s.saved, v)
    {
      assert HasQuota(store, state.s.saved, v);
    }

    unsafe_dispose(G(store', state'));
  }

  method acquire_exc(linear r: R)
  returns (linear v: V)
  requires r.Internal? && qexc_v(r.q).Some?
  ensures v == qexc_v(r.q).value
  {
  }
}
