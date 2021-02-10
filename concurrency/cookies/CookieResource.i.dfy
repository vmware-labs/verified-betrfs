module CookieResource refines ApplicationResourceSpec(CookieIfc) {
  datatype R =
    | ButterAndSugar(rid: RequestId, butter: nat, sugar: nat)
    | Pantry(butter: nat, sugar: nat)
    | Cookies(rid: RequestId, cookies: nat)

  predicate Init(m: multiset<R>) {
    m == multiset{Pantry(0, 0)}
  }

  function input_ticket(id: int, input: Ifc.Input) : R {
    ButterAndSugar(input.butter, input.sugar)
  }

  function output_stub(id: int, output: Ifc.Output) : R {
    Cookies(output.cookies)
  }

  predicate Bake(a: multiset<R>, b: multiset<R>) {
    exists rid, butter, sugar, pantry_butter, pantry_sugar, batches ::
    && batches <= pantry_butter + butter
    && batches <= pantry_sugar + sugar
    && a == multiset{
      ButterAndSugar(rid, butter, sugar),
      Pantry(pantry_butter, pantry_sugar)
    }
    && b == multiset{
      Pantry(pantry_butter + butter - batches, pantry_sugar + sugar - batches),
      Cookies(rid, batches * 6)
    }
  }

  predicate Transform(readonly_set: set<R>, a: multiset<R>, b: multiset<R>) {
    && Bake(a, b)
  }

  predicate Inv(s: multiset<R>) {
    true
  }

  lemma InitImpliesInv(s: multiset<R>)
  requires Init(s)
  ensures Inv(s)
  {
  }

  lemma NextPreservesInv(s: multiset<R>, s': multiset<R>)
  requires Inv(s)
  requires Next(s, s')
  ensures Inv(s')
  {
  }
}
