include "ShardedHashTable.i.dfy"

module ShardedHashTableTokens refines TicketStubSSM(MapIfc) {
  import T = TicketStubToken(MapIfc, ShardedHashTable)
  import opened TicketStubSingletonLoc
  import opened ShardedHashTable

  type Token = T.Tokens.Token

  //// Count sub-system

  datatype {:glinear_fold} Count = Count(capacity: nat)
  {
    function defn() : T.Token {
      T.Tokens.Token(loc(), M(unitTable(), capacity, multiset{}, multiset{}))
    }
  }

  glinear method enclose(glinear a: Count) returns (glinear h: Token)
  ensures h.val == ShardedHashTable.unit().(insert_capacity := a.capacity)
  ensures h.loc == loc()
  {
    h := Count_unfold(a);
  }

  glinear method declose(glinear h: Token) returns (glinear a: Count)
  requires h.loc == loc()
  requires h.val.M?
  requires h.val.table == unitTable() // h is a unit() except for a
  requires h.val.tickets == multiset{}
  requires h.val.stubs == multiset{}
  ensures a.capacity == h.val.insert_capacity
  {
    a := Count_fold(Count(h.val.insert_capacity), h);
  }

  glinear method count_join(glinear a: Count, glinear b: Count)
  returns (glinear c: Count)
  ensures c.capacity == a.capacity + b.capacity
  {
    glinear var a1 := enclose(a);
    glinear var b1 := enclose(b);
    glinear var c1 := T.Tokens.join(a1, b1);
    c := declose(c1);
  }

  glinear method count_split(glinear c: Count, ghost x: nat)
  returns (glinear a: Count, glinear b: Count)
  requires x <= c.capacity
  ensures a.capacity == x
  ensures b.capacity == c.capacity - x
  {
    glinear var c1 := enclose(c);
    glinear var a1, b1 := T.Tokens.split(c1, Count(x).defn().val, Count(c.capacity-x).defn().val);
    a := declose(a1);
    b := declose(b1);
  }

}
