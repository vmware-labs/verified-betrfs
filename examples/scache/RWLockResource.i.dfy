include "ResourceSpec.s.dfy"
include "RWLock.i.dfy"
include "../../lib/Base/Multisets.i.dfy"

module RWLockResource refines ResourceSpec {
  import opened ReadWriteLockResources
  import opened Multisets

  datatype R =
    | LargeFootprint(m: multiset<Q>)
    | Toe(q: Q)

  predicate Init(s: multiset<R>)
  {
    s == multiset{}
  }

  datatype Step = Step(
      s: multiset<Q>,
      s': multiset<Q>,
      rest: multiset<Q>,
      qstep: QStep)

  function toe_multiset(s: multiset<Q>) : multiset<R>
  {
    Apply((q) => Toe(q), s)
  }

  predicate transform_step(a: multiset<R>, b: multiset<R>, step: Step)
  {
    var lf := LargeFootprint(step.s + step.rest);
    var lf' := LargeFootprint(step.s' + step.rest);
    var t := toe_multiset(step.s);
    var t' := toe_multiset(step.s');
    && transform_qstep(t, t', step.qstep)
    && a == multiset{lf} + t
    && b == multiset{lf'} + t'
  }

  predicate transform(a: multiset<R>, b: multiset<R>)
  {
    exists step :: transform_step(a, b, step)
  }
}
