include "../framework/MultiRw.i.dfy"
include "../../lib/Base/Option.s.dfy"

// queue:
//                 tail                     head
//                  |                         |
//                  v                         v
// [         ,     0: F     ,    1: F    ,           ,          ,            ]

module QueueSSM refines MultiRw {
  import opened Options

  type Key = nat

  function size(): nat {
    32
  }

  datatype Producer = ProducerUnknown | ProducerIdle(head: nat) | ProducerInProgress(head: nat)
  datatype Consumer = ConsumerUnknown | ConsumerIdle(tail: nat) | ConsumerInProgress(tail: nat)
  datatype Cell = CellUninit | Empty(v: StoredType) | Producing | Full(v: StoredType) | Consuming

  datatype M =
    | MInvalid
    | MUninit(
      cells: map<nat, Cell>
    )
    | M(
      head: Option<nat>,
      tail: Option<nat>,
      cells: map<nat, Cell>,
      producer: Producer,
      consumer: Consumer
    )

  function I(x: M) : map<Key, StoredType> {
    assert Inv(x);
    assert !x.MInvalid?;
    if x == unit() then map [] else
    map i: nat | i in x.cells.Keys && (
      || x.cells[i].Empty?
      || x.cells[i].Full?
    ) :: x.cells[i].v
  }
  
  predicate Init(s: M) {
    && s.MUninit?
    && s.cells == map i: nat | i < size() :: CellUninit
  }

  predicate Inited(s: M) {
    && s.M?
    && s.head == Some(0)
    && s.tail == Some(0)
    && (forall i: nat :: (i < size() <==> i in s.cells.Keys &&
         exists v :: s.cells[i] == Empty(v))
       )
    && s.producer == ProducerIdle(0)
    && s.consumer == ConsumerIdle(0)
  }

  predicate init_cell(m: M, m': M, idx: nat, v: StoredType)
  {
    && m.MUninit?
    && idx < size()
    && forall i :: (
      if i < idx
      then i in m.cells && m.cells[i].Empty?
      else if i < size()
      then i in m.cells && m.cells[i].CellUninit?
      else i !in m.cells
    )

    && m' == m.(cells := m.cells[idx := Empty(v)])
  }

  lemma init_cell_is_deposit(a: M, b: M, key: nat, x: StoredType)
  requires init_cell(a, b, key, x)
  ensures deposit(a, b, key, x)
  {
    forall p: M | Inv(dot(a, p))
    ensures Inv(dot(b, p))
        && key !in I(dot(a, p))
        && I(dot(b, p)) == I(dot(a, p))[key := x] {

      assert Inv(dot(b, p)) by {
        assert dot(a, p).cells.Keys == a.cells.Keys + p.cells.Keys;
        assert b == a.(cells := a.cells[key := Empty(x)]);
      }
      assert key !in I(dot(a, p));
      assert I(dot(b, p)) == I(dot(a, p))[key := x];
    }
    assert deposit(a, b, key, x);
  }

  predicate producer_begin(m: M, m': M, v: StoredType)
  {
    && m.M?
    && m.tail.Some?
    && m.producer.ProducerIdle?
    && ((m.producer.head + 1) % size()) != m.tail.value
    && var head := m.producer.head;
    && head < size()
    
    && head in m.cells
    && m.cells[head].Empty?
    && m.cells[head].v == v

    && m' == m.(
      producer := ProducerInProgress(m.producer.head),
      cells := m.cells[head := Producing])
  }

  lemma producer_begin_is_withdraw(a: M, b: M, x: StoredType)
  requires producer_begin(a, b, x)
  ensures exists key :: withdraw(a, b, key, x)
  {
    var key := a.producer.head;
    forall p: M | Inv(dot(a, p))
    ensures Inv(dot(b, p))
      && I(dot(a, p)) == I(dot(b, p))[key := x]
      && key !in I(dot(b, p)) {

      assert Inv(dot(b, p)) by {
        assert dot(a, p).cells.Keys == a.cells.Keys + p.cells.Keys;
      }
      assert I(dot(a, p)) == I(dot(b, p))[key := x];
      assert key !in I(dot(b, p));
    }
    assert withdraw(a, b, key, x);
  }

  predicate producer_end(m: M, m': M, v: StoredType)
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

  lemma producer_end_is_deposit(a: M, b: M, x: StoredType)
  requires producer_end(a, b, x)
  ensures exists key :: deposit(a, b, key, x)
  {
    var key := a.head.value;
    forall p: M | Inv(dot(a, p))
    ensures Inv(dot(b, p))
        && key !in I(dot(a, p))
        && I(dot(b, p)) == I(dot(a, p))[key := x] {

      assert Inv(dot(b, p)) by {
        assert dot(a, p).cells.Keys == a.cells.Keys + p.cells.Keys;
      }
      assert key !in I(dot(a, p));
      assert I(dot(b, p)) == I(dot(a, p))[key := x];
    }
    assert deposit(a, b, key, x);
  }

  predicate consumer_begin(m: M, m': M, v: StoredType)
  {
    && m.M?
    && m.head.Some?
    && m.consumer.ConsumerIdle?
    && m.consumer.tail != m.head.value
    && var tail := m.consumer.tail;
    && tail < size()

    && tail in m.cells
    && m.cells[tail].Full?
    && m.cells[tail].v == v

    && m' == m.(
      consumer := ConsumerInProgress(m.consumer.tail),
      cells := m.cells[tail := Consuming])
  }

  lemma consumer_begin_is_withdraw(a: M, b: M, x: StoredType)
  requires consumer_begin(a, b, x)
  ensures exists key :: withdraw(a, b, key, x)
  {
    var key := a.consumer.tail;
    forall p: M | Inv(dot(a, p))
    ensures Inv(dot(b, p))
      && I(dot(a, p)) == I(dot(b, p))[key := x]
      && key !in I(dot(b, p)) {

      assert Inv(dot(b, p)) by {
        assert dot(a, p).cells.Keys == a.cells.Keys + p.cells.Keys;
      }
      assert I(dot(a, p)) == I(dot(b, p))[key := x];
      assert key !in I(dot(b, p));
    }
    assert withdraw(a, b, key, x);
  }


  predicate consumer_end(m: M, m': M, v: StoredType)
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
      cells := m.cells[tail := Empty(v)])
  }

  lemma consumer_end_is_deposit(a: M, b: M, x: StoredType)
  requires consumer_end(a, b, x)
  ensures exists key :: deposit(a, b, key, x)
  {
    var key := a.tail.value;

    forall p: M | Inv(dot(a, p))
    ensures Inv(dot(b, p))
        && key !in I(dot(a, p))
        && I(dot(b, p)) == I(dot(a, p))[key := x] {
      
      assert Inv(dot(b, p)) by {
        assert dot(a, p).cells.Keys == a.cells.Keys + p.cells.Keys;
      }
      assert I(dot(b, p)) == I(dot(a, p))[key := x];
      assert key !in I(dot(a, p));
    }
    assert deposit(a, b, key, x);
  }

  predicate MUninitInv(x: M)
  requires x.MUninit?
  {
    && (forall i: nat :: i < size() <==> i in x.cells.Keys)
  }

  predicate MInv(x: M)
  requires x.M?
  {
    && x.head.Some?
    && x.tail.Some?
    && (forall i: nat :: i < size() <==> i in x.cells.Keys)
    && (forall i: nat :: i < size() ==> !x.cells[i].CellUninit?)
    && (!x.producer.ProducerUnknown?)
    && (!x.consumer.ConsumerUnknown?)

    && x.head.value < size()
    && x.tail.value < size()

    && x.producer.head == x.head.value
    && x.consumer.tail == x.tail.value

    && (x.producer.ProducerInProgress? ==> 
      ((x.producer.head + 1) % size()) != x.tail.value)
    && (x.consumer.ConsumerInProgress? ==> 
      x.consumer.tail != x.head.value)

    && (
      var head := x.head.value;
      var tail := x.tail.value;
      forall i: nat | i < size() :: (
        var i_2 := if i < tail then i + size() else i;
        var head_2 := if head < tail then head + size() else head;
        if i_2 < head_2
          then (
            if x.consumer.ConsumerInProgress? && x.consumer.tail == i then
              x.cells[i].Consuming?
            else
              x.cells[i].Full?
          )
          else (
            if x.producer.ProducerInProgress? && x.producer.head == i then
              x.cells[i].Producing?
            else
              x.cells[i].Empty?
          )
    ))
  }

  predicate Inv(x: M)
  {
    if x.MUninit? then
      MUninitInv(x)
    else if x.M? then
      (
        || MInv(x)
        || x == unit()
      )
    else
      false
  }

  function dot(x: M, y: M) : M
  ensures (x.M? && y.M?) ==> (dot(x, y).M? || dot(x, y).MInvalid?)
  {
    if x.MUninit? && y.MUninit? then
      if (exists i: nat :: i in x.cells && i in y.cells)
      then MInvalid
      else MUninit(
        map i: nat | (i in (x.cells.Keys + y.cells.Keys)) ::
          if i in x.cells then x.cells[i] else y.cells[i])
    else if x.MUninit? || y.MUninit?
    then (
      if (x.MUninit? && y == unit())
      then x
      else if (x == unit() && y.MUninit?)
      then y
      else MInvalid
    )
    else if (
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

  lemma InitImpliesInv(x: M)
  ensures Inv(x)
  {
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

  lemma inv_unit()
  ensures Inv(unit())
  ensures I(unit()) == map[]
  {

  }
}
