include "../framework/Ptrs.s.dfy"
include "../framework/MultiRw.i.dfy"
include "../../lib/Base/Option.s.dfy"

// queue:
//                 tail                     write_head  reserve_head
//                  |                         |           |
//                  v                         v           v
// [         ,     0: F     ,    1: F    ,           ,          ,            ]

abstract module ItemModule { type Item }

module Ring {
  function size(): nat { 32 }

  type inbounds = n: nat | n < size()

  function successor(v: inbounds): inbounds
  {
    if v == size() - 1 then
      0
    else
      v + 1
  }

  function predecessor(v: inbounds): inbounds
  {
    if v == 0 then
      size() - 1
    else
      v - 1
  }

  // [from, to]
  predicate between(from: inbounds, i: inbounds, to: inbounds)
  {
    if from <= to then
      from <= i <= to
    else
      (from <= i || i <= to)
  }

  // [from, to)
  predicate within(from: inbounds, i: inbounds, to: inbounds)
  {
    if from <= to then
      from <= i < to
    else
      (from <= i || i < to)
  }
}

module MpscQueueMultiRw(item: ItemModule) refines MultiRw {
  import Ring
  import opened Options
  import Ptrs

  type Key = Ring.inbounds
  type StoredType = Ptrs.PointsToLinear<item.Item>

  type InboundsMap<V> = map<Ring.inbounds, V>

  datatype Producer = ProducerUnknown | ProducerIdle | ProducerInProgress(tail: Ring.inbounds) | ProducerReserving(tail: Ring.inbounds, reserve_head: Ring.inbounds) | ProducerProducing(head: Ring.inbounds)
  datatype Consumer = ConsumerUnknown | ConsumerIdle(tail: Ring.inbounds) | ConsumerInProgress(tail: Ring.inbounds)
  datatype Cell = CellUninit | Empty(v: StoredType) | Producing | Full(v: StoredType) | Consuming

  datatype M =
    | MInvalid
    | MUninit(
      cells: InboundsMap<Cell>
    )
    | M(
      reserve_head: Option<Ring.inbounds>,
      write_head: Option<Ring.inbounds>,
      tail: Option<Ring.inbounds>,
      cells: InboundsMap<Cell>,
      producer: Producer,
      consumer: Consumer
    )

  function I(x: M) : map<Key, StoredType> {
    assert Inv(x);
    assert !x.MInvalid?;
    if x == unit() then map [] else
    map i: Ring.inbounds | i in x.cells.Keys && (
      || x.cells[i].Empty?
      || x.cells[i].Full?
    ) :: x.cells[i].v
  }
  
  predicate Init(s: M) {
    && s.MUninit?
    && s.cells == map i: Ring.inbounds :: CellUninit
  }

  predicate Inited(s: M) {
    && s.M?
    && s.reserve_head == Some(0)
    && s.write_head == Some(0)
    && s.tail == Some(0)
    && (forall i: Ring.inbounds :: i in s.cells.Keys && exists v :: s.cells[i] == Empty(v))
    && s.producer == ProducerIdle
    && s.consumer == ConsumerIdle(0)
  }

  predicate init_cell(m: M, m': M, idx: Ring.inbounds, v: StoredType)
  {
    && m.MUninit?
    && (forall i: Ring.inbounds :: (
      && i in m.cells
      && if i < idx then m.cells[i].Empty? else m.cells[i].CellUninit?
    ))

    && m' == m.(cells := m.cells[idx := Empty(v)])
  }

  lemma init_cell_is_deposit(a: M, b: M, key: Ring.inbounds, x: StoredType)
  requires init_cell(a, b, key, x)
  ensures deposit(a, b, key, x)
  {
    forall p: M | Inv(dot(a, p))
    ensures Inv(dot(b, p))
        && key !in I(dot(a, p))
        && I(dot(b, p)) == I(dot(a, p))[key := x] {

      reveal_dot_XY_Cells();
      assert Inv(dot(b, p)) by {
        assert dot(a, p).cells.Keys == a.cells.Keys + p.cells.Keys;
        assert b == a.(cells := a.cells[key := Empty(x)]);
      }
      assert key !in I(dot(a, p));
      assert I(dot(b, p)) == I(dot(a, p))[key := x];
    }
    assert deposit(a, b, key, x);
  }

  predicate producer_begin(m: M, m': M)
  {
    && m.M?
    && m.tail.Some?
    && m.producer.ProducerIdle?
    
    && m' == m.(
      producer := ProducerInProgress(m.tail.value))
  }

  lemma producer_begin_is_transition(a: M, b: M)
  requires producer_begin(a, b)
  ensures transition(a, b)
  {
    forall p: M | Inv(dot(a, p))
    ensures Inv(dot(b, p))
      && I(dot(a, p)) == I(dot(b, p)) {

      reveal_dot_XY_Cells();
      assert Inv(dot(b, p)) by {
        assert dot(a, p).cells.Keys == a.cells.Keys + p.cells.Keys;
        forall i: Ring.inbounds
        ensures MInvCell(dot(b, p), i)
        {
          assert MInvCell(dot(a, p), i);
        }
      }
    }
    assert transition(a, b);
  }

  predicate producer_read_reserve_head(m: M, m': M)
  {
    && m.M?
    && m.reserve_head.Some?
    && (m.producer.ProducerInProgress? || m.producer.ProducerReserving?)

    && m' == m.(
      producer := ProducerReserving(m.producer.tail, m.reserve_head.value))
  }

  lemma producer_read_reserve_head_is_transition(a: M, b: M)
  requires producer_read_reserve_head(a, b)
  ensures transition(a, b)
  {
    forall p: M | Inv(dot(a, p))
    ensures Inv(dot(b, p))
      && I(dot(a, p)) == I(dot(b, p)) {

      reveal_dot_XY_Cells();
      assert Inv(dot(b, p)) by {
        assert dot(a, p).cells.Keys == a.cells.Keys + p.cells.Keys;
        forall i: Ring.inbounds
        ensures MInvCell(dot(b, p), i)
        {
          assert MInvCell(dot(a, p), i);
        }
      }
    }
    assert transition(a, b);
  }

  predicate producer_reserve(m: M, m': M, v: StoredType)
  {
    && m.M?
    && m.producer.ProducerReserving?
    && Ring.successor(m.producer.reserve_head) != m.producer.tail

    && var reserve_head := m.producer.reserve_head;

    && m.reserve_head.Some?
    && reserve_head == m.reserve_head.value

    && var tail := m.producer.tail;
    
    && reserve_head in m.cells
    && m.cells[reserve_head].Empty?
    && m.cells[reserve_head].v == v

    && m' == m.(
      producer := ProducerProducing(m.producer.reserve_head),
      reserve_head := Some(Ring.successor(reserve_head)),
      cells := m.cells[reserve_head := Producing])
  }

  lemma producer_reserve_is_withdraw(a: M, b: M, x: StoredType)
  requires producer_reserve(a, b, x)
  ensures exists key :: withdraw(a, b, key, x)
  {
    var key := a.producer.reserve_head;
    forall p: M | Inv(dot(a, p))
    ensures Inv(dot(b, p))
      && I(dot(a, p)) == I(dot(b, p))[key := x]
      && key !in I(dot(b, p)) {

      reveal_dot_XY_Cells();
      assert Inv(dot(b, p)) by {
        assert dot(b, p).reserve_head.value == Ring.successor(dot(a, p).reserve_head.value);
        assert dot(b, p).reserve_head.value != dot(b, p).tail.value;

        assert dot(a, p).cells.Keys == a.cells.Keys + p.cells.Keys;
        forall i: Ring.inbounds
        ensures MInvCell(dot(b, p), i)
        {
          assert MInvCell(dot(a, p), i);

          var x := dot(b, p);

          var write_head := x.write_head.value;
          var reserve_head := x.write_head.value;
          var tail := x.tail.value;

          if Ring.within(tail, i, write_head) {
            if x.consumer.ConsumerInProgress? && x.consumer.tail == i {
              assert x.cells[i].Consuming?;
            } else {
              assert x.cells[i].Full?;
            }
          } else if Ring.within(write_head, i, reserve_head) {
            assert x.cells[i].Producing?;
          } else {
            assert Ring.between(reserve_head, i, Ring.predecessor(tail));
            assert x.cells[i].Empty?;
          }
        }
        assert MInv(dot(b, p));
      }
      assert I(dot(a, p)) == I(dot(b, p))[key := x];
      assert key !in I(dot(b, p));
    }
    assert withdraw(a, b, key, x);
  }

  predicate producer_end(m: M, m': M, v: StoredType)
  {
    && m.M?
    && m.write_head.Some?
    && m.producer.ProducerProducing?
    && m.write_head.value == m.producer.head
    && var head := m.producer.head;

    && head in m.cells
    && m.cells[head].Producing?

    && var newHead := Ring.successor(head);
    && m' == m.(
      producer := ProducerIdle,
      write_head := Some(newHead),
      cells := m.cells[head := Full(v)])
  }

  lemma producer_end_is_deposit(a: M, b: M, x: StoredType)
  requires producer_end(a, b, x)
  ensures exists key :: deposit(a, b, key, x)
  {
    var key := a.producer.head;
    forall p: M | Inv(dot(a, p))
    ensures Inv(dot(b, p))
        && key !in I(dot(a, p))
        && I(dot(b, p)) == I(dot(a, p))[key := x] {

      reveal_dot_XY_Cells();
      assert Inv(dot(b, p)) by {
        assert dot(a, p).cells.Keys == a.cells.Keys + p.cells.Keys;
        forall i: Ring.inbounds
        ensures MInvCell(dot(b, p), i)
        {
          assert MInvCell(dot(a, p), i);
        }
      }
      assert key !in I(dot(a, p));
      assert I(dot(b, p)) == I(dot(a, p))[key := x];
    }
    assert deposit(a, b, key, x);
  }

  predicate consumer_begin(m: M, m': M, v: StoredType)
  {
    && m.M?
    && m.write_head.Some?
    && m.consumer.ConsumerIdle?
    && m.consumer.tail != m.write_head.value
    && var tail := m.consumer.tail;

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

      reveal_dot_XY_Cells();
      assert Inv(dot(b, p)) by {
        assert dot(a, p).cells.Keys == a.cells.Keys + p.cells.Keys;
        forall i: Ring.inbounds
        ensures MInvCell(dot(b, p), i)
        {
          assert MInvCell(dot(a, p), i);
        }
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
    && tail in m.cells
    && m.cells[tail].Consuming?

    && var newTail := Ring.successor(tail);
    && m' == m.(
      consumer := ConsumerIdle(newTail),
      tail := Some(newTail),
      cells := m.cells[tail := Empty(v)])
  }

  lemma consumer_end_is_deposit(a: M, b: M, x: StoredType)
  requires consumer_end(a, b, x)
  ensures exists key :: deposit(a, b, key, x)
  // {
  //   var key := a.tail.value;

  //   forall p: M | Inv(dot(a, p))
  //   ensures Inv(dot(b, p))
  //       && key !in I(dot(a, p))
  //       && I(dot(b, p)) == I(dot(a, p))[key := x] {
  //     
  //     reveal_dot_XY_Cells();
  //     assert Inv(dot(b, p)) by {
  //       assert dot(a, p).cells.Keys == a.cells.Keys + p.cells.Keys;
  //       forall i: Ring.inbounds
  //       ensures MInvCell(dot(b, p), i)
  //       {
  //         assert MInvCell(dot(a, p), i);
  //       }
  //     }
  //     assert I(dot(b, p)) == I(dot(a, p))[key := x];
  //     assert key !in I(dot(a, p));
  //   }
  //   assert deposit(a, b, key, x);
  // }

  predicate MUninitInv(x: M)
  requires x.MUninit?
  {
    && (forall i: Ring.inbounds :: i in x.cells.Keys)
  }

  predicate MInvCell(x: M, i: Ring.inbounds)
  requires x.M?
  requires x.tail.Some?
  requires x.write_head.Some?
  requires x.reserve_head.Some?
  requires Ring.between(x.tail.value, x.write_head.value, x.reserve_head.value)
  requires forall i: Ring.inbounds :: i in x.cells.Keys
  requires forall i: Ring.inbounds :: !x.cells[i].CellUninit?
  {
    var write_head := x.write_head.value;
    var reserve_head := x.write_head.value;
    var tail := x.tail.value;

    if Ring.within(tail, i, write_head)
    then (
      if x.consumer.ConsumerInProgress? && x.consumer.tail == i
      then x.cells[i].Consuming?
      else x.cells[i].Full?)
    else if Ring.within(write_head, i, reserve_head) then
      x.cells[i].Producing?
    else (
      assert Ring.between(reserve_head, i, Ring.predecessor(tail));
      x.cells[i].Empty?)
  }

  predicate MInv(x: M)
  requires x.M?
  {
    && x.reserve_head.Some?
    && x.write_head.Some?
    && x.tail.Some?
    && (forall i: nat :: i < Ring.size() <==> i in x.cells.Keys)
    && (forall i: Ring.inbounds :: !x.cells[i].CellUninit?)
    && (!x.producer.ProducerUnknown?)
    && (!x.consumer.ConsumerUnknown?)

    && x.consumer.tail == x.tail.value
    && Ring.between(x.tail.value, x.write_head.value, x.reserve_head.value)

    && ((x.producer.ProducerInProgress? || x.producer.ProducerReserving?) ==>
      Ring.between(x.producer.tail, x.tail.value, x.write_head.value))
      
    && (x.producer.ProducerReserving? ==> 
      && Ring.between(x.write_head.value, x.producer.reserve_head, x.reserve_head.value))
    && (x.producer.ProducerProducing? ==> (
      && Ring.within(x.write_head.value, x.producer.head, x.reserve_head.value)
      && Ring.successor(x.producer.head) != x.tail.value
      && x.write_head.value != Ring.successor(x.producer.head)))
    && (x.consumer.ConsumerInProgress? ==> 
      x.consumer.tail != x.write_head.value)

    && (forall i: Ring.inbounds :: MInvCell(x, i))
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

  // TODO opaquing this function doens't actually seem to help
  function {:opaque} dot_XY_Cells(x_cells: InboundsMap<Cell>, y_cells: InboundsMap<Cell>): InboundsMap<Cell>
  {
    map i: nat | (i in (x_cells.Keys + y_cells.Keys)) :: if i in x_cells then x_cells[i] else y_cells[i]
  }

  function dot(x: M, y: M) : M
  ensures (x.M? && y.M?) ==> (dot(x, y).M? || dot(x, y).MInvalid?)
  {
    if x.MUninit? && y.MUninit? then
      if (exists i: Ring.inbounds :: i in x.cells && i in y.cells)
      then MInvalid
      else MUninit(dot_XY_Cells(x.cells, y.cells))
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
      || (x.reserve_head.Some? && y.reserve_head.Some?)
      || (x.write_head.Some? && y.write_head.Some?)
      || (x.tail.Some? && y.tail.Some?)
      || (exists i: Ring.inbounds :: i in x.cells && i in y.cells)
      || (!x.producer.ProducerUnknown? && !y.producer.ProducerUnknown?)
      || (!x.consumer.ConsumerUnknown? && !y.consumer.ConsumerUnknown?)
    ) then MInvalid else
      M(
        if x.reserve_head.Some? then x.reserve_head else y.reserve_head,
        if x.write_head.Some? then x.write_head else y.write_head,
        if x.tail.Some? then x.tail else y.tail,
        dot_XY_Cells(x.cells, y.cells),
        if !x.producer.ProducerUnknown? then x.producer else y.producer,
        if !x.consumer.ConsumerUnknown? then x.consumer else y.consumer
      )
  }

  function unit() : M
  {
    M(
      None,
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
    reveal_dot_XY_Cells();
    assert dot(x, unit()) == x;
  }

  lemma commutative(x: M, y: M)
  {
    reveal_dot_XY_Cells();
    assert dot(x, y) == dot(y, x);
  }

  lemma associative(x: M, y: M, z: M)
  {
    reveal_dot_XY_Cells();
    assert dot(x, dot(y, z)) == dot(dot(x, y), z);
  }

  lemma inv_unit()
  ensures Inv(unit())
  ensures I(unit()) == map[]
  {

  }
}
