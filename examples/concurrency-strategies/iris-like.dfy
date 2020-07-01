include "spec.s.dfy"

// This is not actually Iris at all
module IrisImpl {
  import opened Options
  import opened Abstract

  class Resources {
    function abstract_state() : State
    reads this

    function op_done() : UI
    reads this

    ghost method update(s': State, op: Op)
    requires op_done().None?
    requires Next(abstract_state(), s', Some(op))
    modifies this
    ensures abstract_state() == s'
    ensures op_done() == Some(op)

    predicate can_return(victim: nat, outidx: Option<nat>)
    reads this
    {
      && op_done() == Some(DonateOp(victim, outidx))
    }
  }

  function size() : int
  ensures size() > 0

  datatype Well = Well(stones: nat, locked: bool, ghost suffix: Abstract.View)

  class ImplState {
    var w: seq<Well>;
  }

  function ghost_cons(w: seq<Well>, i: int) : seq<nat>
  requires 0 <= i < |w|
  {
    if i == |w| - 1 then
      [w[i].stones]
    else
      [w[i].stones] + w[i+1].suffix
  }

  predicate ghost_inv_at(board: seq<nat>, w: seq<Well>, i: int)
  requires |board| == |w|
  requires 0 <= i < |board|
  {
    !w[i].locked ==>
      w[i].suffix == ghost_cons(w, i)
  }

  predicate inv(s: State, w: seq<Well>)
  {
    && |s.board| == size()
    && |w| == size()
    && s.board == w[0].suffix
    && (forall i | 0 <= i < |s.board| :: ghost_inv_at(s.board, w, i))
  }

  predicate Inv(s: State, is: ImplState)
  reads is
  {
    inv(s, is.w)
  }

  //lemma DonatePrepend(a: nat, view: seq<nat>, victim: nat)
  //requires a != victim
  //ensures Donate([a] + view, victim).0 == [a] + Donate(view, victim).0
  //ensures Donate([a] + view, victim).1 == 1 + Donate(view, victim).1

  method donate_impl(ghost r: Resources, is: ImplState, victim: nat)
  returns (outidx: Option<nat>)
  requires Inv(r.abstract_state(), is)
  requires r.op_done().None?
  modifies r
  modifies is
  ensures Inv(r.abstract_state(), is)
  ensures r.can_return(victim, outidx)
  {
    var idx := 0;
    assert ghost_inv_at(r.abstract_state().board, is.w, 0);

    // Lock the root.

    assume !is.w[0].locked;
    is.w := is.w[0 := is.w[0].(locked := true)];

    // Update some ghost state.

    ghost var (suffix', g_outidx) := Abstract.Donate(is.w[0].suffix, victim);
    is.w := is.w[0 := is.w[0].(suffix := suffix')];

    assert DonateStep(r.abstract_state(), State(suffix'),
        victim, Some(DonateOp(victim, g_outidx)));
    r.update(State(suffix'), DonateOp(victim, g_outidx));

    forall i | 0 <= i < |r.abstract_state().board|
    ensures ghost_inv_at(r.abstract_state().board, is.w, i)
    {
      assert ghost_inv_at(old(r.abstract_state().board), old(is.w), i);
    }

    while true
    invariant Inv(r.abstract_state(), is)
    invariant r == old(r)
    invariant is == old(is)

    invariant r.can_return(victim, g_outidx)
    invariant 0 <= idx < size()
    invariant is.w[idx].suffix
        == Abstract.Donate(ghost_cons(is.w, idx), victim).0
    invariant g_outidx.Some? ==> Abstract.Donate(ghost_cons(is.w, idx), victim).1.Some?
        && g_outidx.value == idx + Abstract.Donate(ghost_cons(is.w, idx), victim).1.value
    invariant g_outidx.None? ==> Abstract.Donate(ghost_cons(is.w, idx), victim).1.None?
    decreases size() - idx
    {
      // imaginary yield point here
      // The rest of this while-loop is just assumed to be atomic.
      // Pretend we have CIVL or something similar to justify that.

      ghost var old_s := r.abstract_state();
      ghost var old_w := is.w;

      assert ghost_inv_at(old_s.board, old_w, idx);

      if is.w[idx].stones == victim {
        is.w := is.w[idx := is.w[idx].(stones := victim + 1)];

        forall i | 0 <= i < |r.abstract_state().board|
        ensures ghost_inv_at(r.abstract_state().board, is.w, i)
        {
          assert ghost_inv_at(old_s.board, old_w, i);
        }

        return Some(idx);
      } else if idx == |is.w| - 1 {
        return None;
      } else {
        // take lock
        assume !is.w[idx+1].locked;
        is.w := is.w[idx+1 := is.w[idx+1].(locked := true)];

        // update ghost state
        ghost var (suffix', o) := Abstract.Donate(is.w[idx+1].suffix, victim);
        is.w := is.w[idx+1 := is.w[idx+1].(suffix := suffix')];

        // release lock
        is.w := is.w[idx := is.w[idx].(locked := false)];

        forall i | 0 <= i < |r.abstract_state().board|
        ensures ghost_inv_at(r.abstract_state().board, is.w, i)
        {
          assert ghost_inv_at(old_s.board, old_w, i);
        }

        /*calc {
          is.w[idx+1].suffix;
          {
            assert is.w[idx+1].suffix
                == suffix'
                == Abstract.Donate(old_w[idx+1].suffix, victim).0;
          }
          Abstract.Donate(old_w[idx+1].suffix, victim).0;
          { assert ghost_inv_at(old_s.board, old_w, idx+1); }
          Abstract.Donate(ghost_cons(old_w, idx+1), victim).0;
          Abstract.Donate(ghost_cons(is.w, idx+1), victim).0;
        }*/
        assert ghost_inv_at(old_s.board, old_w, idx+1);

        idx := idx + 1;
      }
    }
  }
}
