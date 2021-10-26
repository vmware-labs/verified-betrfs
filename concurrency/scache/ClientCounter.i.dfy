include "../framework/BasicPCM.i.dfy"

module CounterPCM refines BasicPCM {
  ghost const max: nat := 0xff

  datatype M = Counter(ghost n: nat)

  function dot(x: M, y: M) : M
  {
    Counter(x.n + y.n)
  }

  predicate valid(x: M) 
  {
    x.n <= max
  }

  function unit() : M
  {
    Counter(0)
  }

  lemma dot_unit(x: M)
  ensures dot(x, unit()) == x
  {
  }

  lemma valid_unit(x: M)
  ensures valid(unit())
  {
  }

  lemma commutative(x: M, y: M)
  ensures dot(x, y) == dot(y, x)
  {
  }

  lemma associative(x: M, y: M, z: M)
  ensures dot(x, dot(y, z)) == dot(dot(x, y), z)
  {
  }
}

module ClientCounter {
  import T = Tokens(CounterPCM)
  import opened GhostLoc
  import opened CounterPCM

  datatype {:glinear_fold} Client = Client(ghost loc: Loc)
  {
    function defn() : T.Token {
      T.Token(loc, Counter(1))
    }
  }

  datatype {:glinear_fold} Clients = Clients(ghost loc: Loc, ghost n: nat)
  {
    function defn() : T.Token {
      T.Token(loc, Counter(n))
    }
  }

  glinear method counter_init()
  returns (glinear cl: Clients)
  ensures cl.n == max
  {
    glinear var t := T.init(Counter(max));
    cl := Clients_fold(Clients(t.loc, max), t);
  }

  glinear method get_bound(gshared cs: Clients)
  ensures cs.n <= max
  {
    gshared var s := Clients_unfold_borrow(cs);
    glinear var u := T.get_unit(cs.loc);
    T.is_valid(s, inout u);
    T.dispose(u);
  }

  glinear method merge(glinear cs: Clients, glinear c: Client)
  returns (glinear cs': Clients)
  requires cs.loc == c.loc
  ensures cs' == Clients(cs.loc, cs.n + 1)
  {
    glinear var a := Clients_unfold(cs);
    glinear var b := Client_unfold(c);
    glinear var x := T.join(a, b);
    cs' := Clients_fold(Clients(cs.loc, cs.n + 1), x);
  }

  glinear method split(glinear cs: Clients)
  returns (glinear cs': Clients, glinear c': Client)
  requires cs.n >= 1
  ensures cs' == Clients(cs.loc, cs.n - 1)
  ensures c' == Client(cs.loc)
  {
    glinear var a := Clients_unfold(cs);
    glinear var x, y := T.split(a,
        Counter(cs.n - 1),
        Counter(1));
    cs' := Clients_fold(Clients(cs.loc, cs.n - 1), x);
    c' := Client_fold(Client(cs.loc), y);
  }

  glinear method empty_counter(ghost loc: Loc)
  returns (glinear cs': Clients)
  ensures cs'.n == 0
  ensures cs'.loc == loc
  {
    glinear var t := T.get_unit(loc);
    cs' := Clients_fold(Clients(loc, 0), t);
  }
}
