
datatype Thing = Thing(things: array<Thing>, other: set<int>, ghost repr: set<object>)

predicate WF(t: Thing)
  reads t.repr
  decreases t.other
{
  && t.things in t.repr
  && (forall i: nat | i < t.things.Length :: t.things[i].other < t.other)
  && (forall i: nat | i < t.things.Length :: t.things[i].repr < t.repr)
  && (forall i: nat | i < t.things.Length :: WF(t.things[i]))
}
