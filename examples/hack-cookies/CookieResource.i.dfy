include "../hack-concurrency-framework/ApplicationResourceSpec.s.dfy"

module CookieResource refines ApplicationResourceSpec {
  datatype Ticket = Ticket(rid: int, input: Ifc.Input)
  datatype Stub = Stub(rid: int, output: Ifc.Output)

  datatype R = R(
    tickets: multiset<Ticket>,
    stubs: multiset<Stub>,
    butter: nat,
    sugar: nat)

  function unit() : R {
    R(multiset{}, multiset{}, 0, 0)
  }

  function add(x: R, y: R) : R {
    R(x.tickets + y.tickets,
      x.stubs + y.stubs,
      x.butter + y.butter,
      x.sugar + y.sugar)
  }

  lemma add_unit(x: R)
  ensures add(x, unit()) == x
  {
  }

  lemma commutative(x: R, y: R)
  ensures add(x, y) == add(y, x)
  {
  }

  lemma associative(x: R, y: R, z: R)
  ensures add(x, add(y, z)) == add(add(x, y), z)
  {
  }

  predicate Init(s: R) {
    s == unit()
  }

  predicate do_request(s: R, s': R, ticket: Ticket, batches: nat)
  {
    && batches <= ticket.input.sugar + s.sugar
    && batches <= ticket.input.butter + s.butter
    && ticket in s.tickets
    && s'.tickets == s.tickets - multiset{ticket}
    && s'.stubs == s.stubs + multiset{Stub(ticket.rid, Ifc.Output(6 * batches))}
    && s'.sugar == ticket.input.sugar + s.sugar - batches
    && s'.butter == ticket.input.butter + s.butter - batches
  }

  predicate Update(s: R, s': R) {
    exists ticket, batches :: do_request(s, s', ticket, batches)
  }

  predicate Valid(s: R) {
    true
  }

  lemma valid_monotonic(x: R, y: R)
  //requires Valid(add(x, y))
  ensures Valid(x)
  {
  }

  lemma update_monotonic(x: R, y: R, z: R)
  //requires Update(x, y)
  ensures Update(add(x, z), add(y, z))
  {
    var ticket, batches :| do_request(x, y, ticket, batches);
    assert do_request(add(x, z), add(y, z), ticket, batches);
  }

  function input_ticket(id: int, input: Ifc.Input) : R {
    R(multiset{Ticket(id, input)}, multiset{}, 0, 0)
  }

  function output_stub(id: int, output: Ifc.Output) : R {
    R(multiset{}, multiset{Stub(id, output)}, 0, 0)
  }

  predicate Inv(s: R) {
    true
  }

  lemma UpdatePreservesInv(s: R, s': R)
  //requires Inv(s)
  //requires Update(s, s')
  ensures Inv(s')
  {
  }

  lemma NewTicketPreservesInv(s: R, s': R)
  //requires Inv(s)
  //requires NewTicket(s, s')
  ensures Inv(s')
  {
  }

  lemma ConsumeStubPreservesInv(s: R, s': R)
  //requires Inv(s)
  //requires ConsumeStub(s, s')
  ensures Inv(s')
  {
  }

  lemma radical_of_unit(a: R)
  requires radical(a, unit())
  ensures a == unit()
  {
    reveal_radical();
  }

  method {:extern} easy_transform(
      linear b: R,
      ghost expected_out: R)
  returns (linear c: R)
  requires Update(b, expected_out)
  ensures c == expected_out
  {
    shared var u := get_unit_shared();
    ghost var a := u;
    forall a' | radical(a', a) && Valid(add(a', b))
    ensures Update(add(a', b), add(a', expected_out))
    {
      radical_of_unit(a');
      assert add(a', b) == b;
      assert add(a', expected_out) == expected_out;
    }
    c := do_transform(u, b, expected_out);
  }

  method do_tr(linear t: R, linear s: R, ticket: Ticket, batches: nat)
  returns (linear stub: R, linear s': R)
  requires t == input_ticket(ticket.rid, ticket.input)
  requires batches <= ticket.input.sugar + s.sugar
  requires batches <= ticket.input.butter + s.butter
  ensures stub == output_stub(ticket.rid, Ifc.Output(6 * batches))
  ensures s' == s
    .(sugar := ticket.input.sugar + s.sugar - batches)
    .(butter := ticket.input.butter + s.butter - batches)
  {
    linear var total := join(t, s);
    ghost var total_exp := total
      .(tickets := total.tickets - multiset{ticket})
      .(stubs := total.stubs + multiset{Stub(ticket.rid, Ifc.Output(6 * batches))})
      .(sugar := ticket.input.sugar + s.sugar - batches)
      .(butter := ticket.input.butter + s.butter - batches);
    assert do_request(total, total_exp, ticket, batches);
    linear var total' := easy_transform(total, total_exp);
    stub, s' := split(total', 
        output_stub(ticket.rid, Ifc.Output(6 * batches)),
        s.(sugar := ticket.input.sugar + s.sugar - batches)
         .(butter := ticket.input.butter + s.butter - batches)
    );
  }
}
