include "OGTokens.i.dfy"
include "../framework/Mutex.i.dfy"
include "../framework/Ptrs.s.dfy"

module OGImpl {
  import opened OGTokens
  import opened Mutexes
  import opened Ptrs

  linear datatype Stored = Stored(
      n: nat,
      glinear token: Counter)
  {
      predicate WF(loc_s: nat) {
          token == Counter(loc_s, n)
      }
  }

  linear datatype Impl = Impl(
      ghost loc_s: nat,
      linear lock: Mutex<Stored>
  )
  {
      predicate WF() {
          && lock.WF()
          && (forall v :: lock.inv(v) <==> v.WF(loc_s))
      }
  }

  method thread_1(shared impl: Impl, glinear token: IncA)
  returns (glinear token': IncA)
  requires impl.WF()
  requires token.loc_s == impl.loc_s
  requires token.b == false
  ensures token'.loc_s == impl.loc_s
  ensures token'.b == true
  decreases *
  {
    linear var v;
    glinear var handle;
    v, handle := impl.lock.acquire();

    linear var Stored(n, counter_token) := v;

    n := n + 1;
    counter_token, token' := do_incA(counter_token, token);

    v := Stored(n, counter_token);
    impl.lock.release(v, handle);
  }

  method thread_2(shared impl: Impl, glinear token: IncB)
  returns (glinear token': IncB)
  requires impl.WF()
  requires token.loc_s == impl.loc_s
  requires token.b == false
  ensures token'.loc_s == impl.loc_s
  ensures token'.b == true
  decreases *
  {
    linear var v;
    glinear var handle;
    v, handle := impl.lock.acquire();

    linear var Stored(n, counter_token) := v;

    n := n + 1;
    counter_token, token' := do_incB(counter_token, token);

    v := Stored(n, counter_token);
    impl.lock.release(v, handle);
  }

  method main()
  returns (linear impl: Impl)
  decreases *
  {
    glinear var counter_token, inca_token, incb_token := og_initialize();
    ghost var loc_s := counter_token.loc_s;

    // Put the counter value 0 into the lock.
    linear var m := new_mutex(
        Stored(0, counter_token),
        (v: Stored) => v.WF(loc_s));
    impl := Impl(loc_s, m);

    // Pretend these happen on different threads.
    inca_token := thread_1(impl, inca_token);
    incb_token := thread_2(impl, incb_token);
    
    // Load the counter value from the lock.
    linear var v;
    glinear var handle;
    v, handle := impl.lock.acquire();
    linear var Stored(n, counter_token0) := v;

    counter_token0, inca_token, incb_token := finalize(counter_token0, inca_token, incb_token);
    dispose_anything(inca_token);
    dispose_anything(incb_token);

    // And obtain that the counter value we read is equal to 2:
    assert n == 2;

    // Clean up
    v := Stored(n, counter_token0);
    impl.lock.release(v, handle);
  }
}
