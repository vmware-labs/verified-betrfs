include "../framework/SSM.i.dfy"
include "../../lib/Base/Option.s.dfy"

// queue:
//                 tail                  head
//                  |                      |
//                  v                      v
// [         ,      F     ,     F    ,           ,          ,            ]

module QueueSSM refines SSM {
  import opened Options
 
  type V(!new)

  function size(): nat {
    32
  }

  datatype Producer = ProducerUnknown | ProducerIdle(head: nat) | ProducerInProgress(head: nat)
  datatype Consumer = ConsumerUnknown | ConsumerIdle(tail: nat) | ConsumerInProgress(tail: nat)
  datatype Cell = Empty | Full(v: V)

  datatype M = MInvalid | M(
    head: Option<nat>,
    tail: Option<nat>,
    cells: map<nat, Cell>,
    producer: Producer,
    consumer: Consumer
  )

  predicate Init(s: M) {
    && s.M?
    && s.head == Some(0)
    && s.tail == Some(0)
    && (s.cells == map i: nat | i < size() :: Empty)
    && s.producer == ProducerIdle(0)
    && s.consumer == ConsumerIdle(0)
  }

  predicate producer_begin(m: M, m': M)
  {
    && m.M?
    && m.tail.Some?
    && m.producer.ProducerIdle?
    && ((m.producer.head + 1) % size()) != m.tail.value

    && m' == m.(producer := ProducerInProgress(m.producer.head))
  }

  predicate producer_end(m: M, m': M, v: V)
  {
    && m.M?
    && m.head.Some?
    && m.producer.ProducerInProgress?
    && var head := m.producer.head;
    && head < size()

    && head in m.cells
    && m.cells[head].Empty?

    && var newHead := (head + 1) % size();
    && m' == m.(
      producer := ProducerIdle(newHead),
      head := Some(newHead),
      cells := m.cells[head := Full(v)])
  }

  predicate consumer_begin(m: M, m': M)
  {
    && m.M?
    && m.head.Some?
    && m.consumer.ConsumerIdle?
    && m.consumer.tail != m.head.value

    && m' == m.(consumer := ConsumerInProgress(m.consumer.tail))
  }

  predicate consumer_end(m: M, m': M, v: V)
  {
    && m.M?
    && m.tail.Some?
    && m.consumer.ConsumerInProgress?
    && var tail := m.consumer.tail;
    && tail < size()
    && tail in m.cells
    && m.cells[tail].Full?
    && m.cells[tail].v == v

    && var newTail := (tail + 1) % size();
    && m' == m.(
      consumer := ConsumerIdle(newTail),
      tail := Some(newTail),
      cells := m.cells[tail := Empty])
  }

  predicate Next(shard: M, shard': M)
  {
    || producer_begin(shard, shard')
    || (exists v :: producer_end(shard, shard', v))
    || consumer_begin(shard, shard')
    || (exists v :: consumer_end(shard, shard', v))
  }

  predicate Inv(s: M)
  {
    && s.M?
    && s.head.Some?
    && s.tail.Some?
    && (forall i: nat :: i < size() <==> i in s.cells.Keys)
    && (!s.producer.ProducerUnknown?)
    && (!s.consumer.ConsumerUnknown?)

    && s.head.value < size()
    && s.tail.value < size()

    && s.producer.head == s.head.value
    && s.consumer.tail == s.tail.value

    && (s.producer.ProducerInProgress? ==> 
      ((s.producer.head + 1) % size()) != s.tail.value)
    && (s.consumer.ConsumerInProgress? ==> 
      s.consumer.tail != s.head.value)

    && (
      var head := s.head.value;
      var tail := s.tail.value;
      forall i: nat | i < size() :: (
        var i_2 := if i < tail then i + size() else i;
        var head_2 := if head < tail then head + size() else head;
        if i_2 < head_2
          then s.cells[i].Full?
          else s.cells[i].Empty?
    ))
  }

  function dot(x: M, y: M) : M
  {
    if (
      || (x.MInvalid?)
      || (y.MInvalid?)
      || (x.head.Some? && y.head.Some?)
      || (x.tail.Some? && y.tail.Some?)
      || (exists i: nat :: i in x.cells && i in y.cells)
      || (!x.producer.ProducerUnknown? && !y.producer.ProducerUnknown?)
      || (!x.consumer.ConsumerUnknown? && !y.consumer.ConsumerUnknown?)
    ) then MInvalid else
      M(
        if x.head.Some? then x.head else y.head,
        if x.tail.Some? then x.tail else y.tail,
        map i: nat | (i in (x.cells.Keys + y.cells.Keys)) ::
          if i in x.cells then x.cells[i] else y.cells[i],
        if !x.producer.ProducerUnknown? then x.producer else y.producer,
        if !x.consumer.ConsumerUnknown? then x.consumer else y.consumer
      )
  }

  function unit() : M
  {
    M(
      None,
      None,
      map [],
      ProducerUnknown,
      ConsumerUnknown)
  }

  lemma InitImpliesInv(s: M)
  ensures Inv(s)
  {
  }

  lemma NextImpliesInv(shard: M, shard': M, rest: M)
  // requires Inv(dot(shard, rest))
  // requires Next(shard, shard')
  // ensures Inv(dot(shard', rest))
  {
    if producer_begin(shard, shard') {
      assert Inv(dot(shard', rest));
    } else if (exists v :: producer_end(shard, shard', v)) {
      assert Inv(dot(shard', rest)) by {
        assert dot(shard, rest).cells.Keys == shard.cells.Keys + rest.cells.Keys;
        assert forall i: nat | i < size() :: i in dot(shard', rest).cells.Keys;
      }
    } else if consumer_begin(shard, shard') {
      assert Inv(dot(shard', rest));
    } else if (exists v :: consumer_end(shard, shard', v)) {
      assert Inv(dot(shard', rest)) by {
        assert dot(shard, rest).cells.Keys == shard.cells.Keys + rest.cells.Keys;
        assert forall i: nat :: i < size() <==> i in dot(shard', rest).cells.Keys;

        assert (dot(shard', rest).producer.ProducerInProgress? ==> 
          ((dot(shard', rest).producer.head + 1) % size()) != dot(shard', rest).tail.value);
      }
    } else {
      assert false;
    }
  }

  lemma dot_unit(x: M)
  {
    assert dot(x, unit()) == x;
  }

  lemma commutative(x: M, y: M)
  {
    assert dot(x, y) == dot(y, x);
  }

  lemma associative(x: M, y: M, z: M)
  {
    assert dot(x, dot(y, z)) == dot(dot(x, y), z);
  }

  lemma exists_inv_state()
  returns (s: M)
  ensures Inv(s)
  {
    s := M(
      Some(0),
      Some(0),
      map i: nat | i < size() :: Empty,
      ProducerIdle(0),
      ConsumerIdle(0));
  }
}
