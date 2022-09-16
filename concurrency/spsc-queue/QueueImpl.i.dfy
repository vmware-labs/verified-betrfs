include "../../lib/Lang/NativeTypes.s.dfy"
include "../../lib/Base/LinearOption.i.dfy"
include "../framework/GlinearOption.s.dfy"
include "../framework/PCM.s.dfy"
include "../framework/Ptrs.s.dfy"
include "../framework/Atomic.s.dfy"
include "../framework/MultiRw.i.dfy"
include "QueueMultiRw.i.dfy"

module QueueImpl(item: ItemModule) {
  import opened Options
  import opened LinearOption
  import opened GlinearOption
  import opened GhostLoc
  import Ptrs
  import opened NativeTypes
  import opened Atomics
  import opened QueueMultiRw = QueueMultiRw(item)
  import Tokens = MultiRwTokens(QueueMultiRw)

  linear datatype ConsumerToken = ConsumerToken(glinear token: Tokens.Token, tail: uint32)
  {
    predicate Valid(loc: Loc) {
      && this.token.loc == loc

      && this.token.val == M(None, None, map[], ProducerUnknown, ConsumerIdle(this.tail as nat))
    }
  }

  linear datatype ProducerToken = ProducerToken(glinear token: Tokens.Token, head: uint32)
  {
    predicate Valid(loc: Loc) {
      && this.token.loc == loc

      && this.token.val == M(None, None, map[], ProducerIdle(this.head as nat), ConsumerUnknown)
    }
  }

  function method sizeUint32(): uint32
  ensures sizeUint32() as nat == size()
  {
    32
  }

  datatype Queue = Queue(
    cells: seq<Ptrs.Ptr>,
    head: Atomic<uint32, Tokens.Token>,
    tail: Atomic<uint32, Tokens.Token>,

    ghost cellToken: GhostAtomic<Tokens.Token>,
    ghost loc: Loc
  ) {

    predicate HeadInv(head_v: uint32, t: Tokens.Token, loc: Loc)
    {
      && t.loc == loc
      && t.val == M(Some(head_v as nat), None, map[], ProducerUnknown, ConsumerUnknown)
    }

    predicate TailInv(tail_v: uint32, t: Tokens.Token, loc: Loc)
    {
      && t.loc == loc
      && t.val == M(None, Some(tail_v as nat), map[], ProducerUnknown, ConsumerUnknown)
    }

    predicate CellInvCell(cells_v: map<nat, Cell>, i: nat)
    requires |this.cells| == size()
    requires i < size()
    {
      && i in cells_v.Keys
      && ((cells_v[i].Full? || cells_v[i].Empty?) ==> cells_v[i].v.ptr == this.cells[i])
      && (cells_v[i].Full? ==> cells_v[i].v.PointsToLinear?)
      && (cells_v[i].Empty? ==> cells_v[i].v.PointsToEmpty?)
    }

    predicate CellInv(t: Tokens.Token, loc: Loc)
    requires |this.cells| == size()
    {
      && t.loc == loc
      && exists cells_v :: (
        && t.val == M(None, None, cells_v, ProducerUnknown, ConsumerUnknown)
        && (forall i: nat | i < size() :: CellInvCell(cells_v, i))
      )
    }

    predicate Inv()
    {
      && this.loc.ExtLoc?
      && this.loc.base_loc == Tokens.Wrap.singleton_loc()

      && |this.cells| == size()

      && this.head.namespace() == 1
      && this.tail.namespace() == 2
      && this.cellToken.namespace() == 3

      && (forall v, g :: atomic_inv(this.head, v, g) <==> HeadInv(v, g, this.loc))
      && (forall v, g :: atomic_inv(this.tail, v, g) <==> TailInv(v, g, this.loc))
      && (forall v: (), g :: atomic_inv(this.cellToken, v, g) <==> CellInv(g, this.loc))
    }

    method consume(linear inout consumerToken: ConsumerToken)
    returns (linear item: lOption<item.Item>)
    requires this.Inv()
    requires old_consumerToken.Valid(this.loc)
    ensures consumerToken.Valid(this.loc)
    {
      linear var ConsumerToken(consumer_g, tail) := consumerToken;

      glinear var pointsToCell;

      atomic_block var head_value := execute_atomic_load(this.head) {
        ghost_acquire head_g;
        atomic_block var _ := execute_atomic_noop(this.cellToken) {
          ghost_acquire cellToken_g;

          assert head_g.val == M(Some(head_value as nat), None, map[], ProducerUnknown, ConsumerUnknown);
          assert consumer_g.val == M(None, None, map[], ProducerUnknown, ConsumerIdle(tail as nat));

          ghost var rest := Tokens.obtain_invariant_3(
            inout consumer_g, inout head_g, inout cellToken_g);

          ghost var m := dot(dot(consumer_g.val, head_g.val), cellToken_g.val);
          assert MInv(dot(m, rest));

          ghost var cellToken_g0 := cellToken_g;

          if head_value != tail {
            assert MInvCell(dot(m, rest), tail as nat); // trigger
            assert dot(m, rest).cells[tail as nat].Full?;
            assert CellInvCell(cellToken_g.val.cells, tail as nat); // trigger
            assert cellToken_g.val.cells[tail as nat].Full?;

            ghost var m' := m.(
              consumer := ConsumerInProgress(tail as nat),
              cells := m.cells[tail as nat := Consuming]);

            ghost var consumer_g_val' := M(None, None, map[], ProducerUnknown, ConsumerInProgress(tail as nat));
            ghost var cellToken_g_val' := cellToken_g.val.(cells := cellToken_g.val.cells[tail as nat := Consuming]);

            assert m' == dot(dot(consumer_g_val', head_g.val), cellToken_g_val');

            ghost var expected_v := cellToken_g.val.cells[tail as nat].v;
            assert consumer_begin(m, m', expected_v);

            consumer_begin_is_withdraw(m, m', expected_v);

            assert withdraw(m, m', tail as nat, expected_v);

            glinear var pointsToCell_v;
            consumer_g, head_g, cellToken_g, pointsToCell_v :=
              Tokens.withdraw_3_3(
                consumer_g,
                head_g,
                cellToken_g, 

                consumer_g_val',
                head_g.val,
                cellToken_g_val',

                tail as nat,
                expected_v);

            pointsToCell := glSome(pointsToCell_v);
          } else {
            pointsToCell := glNone;
          }

          forall i: nat | i < size()
          ensures CellInvCell(cellToken_g.val.cells, i) {
            if i != tail as nat {
              assert CellInvCell(cellToken_g0.val.cells, i); // trigger
            }
          }
          ghost_release cellToken_g;
        }
        ghost_release head_g;
      }

      if head_value != tail {
        linear var item_v := this.cells[tail].read_linear(inout pointsToCell.value);
        item := lSome(item_v);

        var newTail: uint32 := (tail + 1) % sizeUint32();

        atomic_block var _ := execute_atomic_store(this.tail, newTail) {
          ghost_acquire tail_g;

          atomic_block var _ := execute_atomic_noop(this.cellToken) {
            ghost_acquire cellToken_g;

            ghost var cellToken_g0 := cellToken_g;

            ghost var m := dot(dot(consumer_g.val, tail_g.val), cellToken_g.val);

            ghost var rest := Tokens.obtain_invariant_3(
              inout consumer_g, inout tail_g, inout cellToken_g);
            
            assert MInvCell(dot(m, rest), tail as nat); // trigger
            assert dot(m, rest).cells[tail as nat].Consuming?;
            assert CellInvCell(cellToken_g.val.cells, tail as nat); // trigger
            assert cellToken_g.val.cells[tail as nat].Consuming?;

            glinear var depositing_v := GlinearOption.unwrap_value(pointsToCell);

            ghost var m' := m.(
              consumer := ConsumerIdle(newTail as nat),
              tail := Some(newTail as nat),
              cells := m.cells[tail as nat := Empty(depositing_v)]);

            ghost var consumer_g_val' := consumer_g.val.(consumer := ConsumerIdle(newTail as nat));
            ghost var tail_g_val' := tail_g.val.(tail := Some(newTail as nat));
            ghost var cellToken_g_val' := cellToken_g.val.(cells := cellToken_g.val.cells[tail as nat := Empty(depositing_v)]);

            assert m' == dot(dot(consumer_g_val', tail_g_val'), cellToken_g_val');

            assert consumer_end(m, m', depositing_v);
            consumer_end_is_deposit(m, m', depositing_v);

            consumer_g, tail_g, cellToken_g :=
              Tokens.deposit_3_3(
                consumer_g,
                tail_g,
                cellToken_g, 

                tail as nat,
                depositing_v,

                consumer_g_val',
                tail_g_val',
                cellToken_g_val');

            forall i: nat | i < size()
            ensures CellInvCell(cellToken_g.val.cells, i) {
              if i != tail as nat {
                assert CellInvCell(cellToken_g0.val.cells, i); // trigger
              }
            }
            ghost_release cellToken_g;
          }

          ghost_release tail_g;
        }

        consumerToken := ConsumerToken(consumer_g, newTail);
      } else {
        consumerToken := ConsumerToken(consumer_g, tail);
        item := lNone;
        GlinearOption.dispose_glnone(pointsToCell);
      }

      assert consumerToken.Valid(this.loc);
    }

    method produce(linear inout producerToken: ProducerToken, linear item: item.Item)
    returns (linear item': lOption<item.Item>)
    requires this.Inv()
    requires old_producerToken.Valid(this.loc)
    ensures producerToken.Valid(this.loc)
    {
      linear var ProducerToken(producer_g, head) := producerToken;

      glinear var pointsToCell;

      atomic_block var tail_value := execute_atomic_load(this.tail) {
        ghost_acquire tail_g;
        atomic_block var _ := execute_atomic_noop(this.cellToken) {
          ghost_acquire cellToken_g;

          assert tail_g.val == M(None, Some(tail_value as nat), map[], ProducerUnknown, ConsumerUnknown);
          assert producer_g.val == M(None, None, map[], ProducerIdle(head as nat), ConsumerUnknown);

          ghost var rest := Tokens.obtain_invariant_3(
            inout producer_g, inout tail_g, inout cellToken_g);

          ghost var m := dot(dot(producer_g.val, tail_g.val), cellToken_g.val);
          assert MInv(dot(m, rest));

          ghost var cellToken_g0 := cellToken_g;

          if ((head + 1) % sizeUint32()) != tail_value {
            assert MInvCell(dot(m, rest), head as nat); // trigger
            assert dot(m, rest).cells[head as nat].Empty?;
            assert CellInvCell(cellToken_g.val.cells, head as nat); // trigger
            assert cellToken_g.val.cells[head as nat].Empty?;

            ghost var m' := m.(
              producer := ProducerInProgress(head as nat),
              cells := m.cells[head as nat := Producing]);

            ghost var producer_g_val' := M(None, None, map[], ProducerInProgress(head as nat), ConsumerUnknown);
            ghost var cellToken_g_val' := cellToken_g.val.(cells := cellToken_g.val.cells[head as nat := Producing]);

            assert m' == dot(dot(producer_g_val', tail_g.val), cellToken_g_val');

            ghost var expected_v := cellToken_g.val.cells[head as nat].v;
            assert producer_begin(m, m', expected_v);

            producer_begin_is_withdraw(m, m', expected_v);

            assert withdraw(m, m', head as nat, expected_v);

            glinear var pointsToCell_v;
            producer_g, tail_g, cellToken_g, pointsToCell_v :=
              Tokens.withdraw_3_3(
                producer_g,
                tail_g,
                cellToken_g, 

                producer_g_val',
                tail_g.val,
                cellToken_g_val',

                head as nat,
                expected_v);

            pointsToCell := glSome(pointsToCell_v);
          } else {
            pointsToCell := glNone;
          }

          forall i: nat | i < size()
          ensures CellInvCell(cellToken_g.val.cells, i) {
            if i != head as nat {
              assert CellInvCell(cellToken_g0.val.cells, i); // trigger
            }
          }

          ghost_release cellToken_g;
        }
        ghost_release tail_g;
      }

      if ((head + 1) % sizeUint32()) != tail_value {
        this.cells[head].write_linear(inout pointsToCell.value, item);
        item' := lNone;

        var newHead: uint32 := (head + 1) % sizeUint32();

        atomic_block var _ := execute_atomic_store(this.head, newHead) {
          ghost_acquire head_g;

          atomic_block var _ := execute_atomic_noop(this.cellToken) {
            ghost_acquire cellToken_g;

            ghost var cellToken_g0 := cellToken_g;

            ghost var m := dot(dot(producer_g.val, head_g.val), cellToken_g.val);

            ghost var rest := Tokens.obtain_invariant_3(
              inout producer_g, inout head_g, inout cellToken_g);
            
            assert MInvCell(dot(m, rest), head as nat); // trigger
            assert dot(m, rest).cells[head as nat].Producing?;
            assert CellInvCell(cellToken_g.val.cells, head as nat); // trigger
            assert cellToken_g.val.cells[head as nat].Producing?;

            glinear var depositing_v := GlinearOption.unwrap_value(pointsToCell);

            ghost var m' := m.(
              producer := ProducerIdle(newHead as nat),
              head := Some(newHead as nat),
              cells := m.cells[head as nat := Full(depositing_v)]);

            ghost var producer_g_val' := producer_g.val.(producer := ProducerIdle(newHead as nat));
            ghost var head_g_val' := head_g.val.(head := Some(newHead as nat));
            ghost var cellToken_g_val' := cellToken_g.val.(cells := cellToken_g.val.cells[head as nat := Full(depositing_v)]);

            assert m' == dot(dot(producer_g_val', head_g_val'), cellToken_g_val');

            assert producer_end(m, m', depositing_v);
            producer_end_is_deposit(m, m', depositing_v);

            producer_g, head_g, cellToken_g :=
              Tokens.deposit_3_3(
                producer_g,
                head_g,
                cellToken_g, 

                head as nat,
                depositing_v,

                producer_g_val',
                head_g_val',
                cellToken_g_val');

            forall i: nat | i < size()
            ensures CellInvCell(cellToken_g.val.cells, i) {
              if i != head as nat {
                assert CellInvCell(cellToken_g0.val.cells, i); // trigger
              }
            }
            ghost_release cellToken_g;
          }

          ghost_release head_g;
        }
        
        producerToken := ProducerToken(producer_g, newHead);
      } else {
        producerToken := ProducerToken(producer_g, head);
        item' := lSome(item);
        GlinearOption.dispose_glnone(pointsToCell);
      }
    }

  }
}
