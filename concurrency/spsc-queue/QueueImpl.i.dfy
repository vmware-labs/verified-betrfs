include "../../lib/Lang/NativeTypes.s.dfy"
include "../../lib/Base/LinearOption.i.dfy"
include "../scache/GlinearOption.i.dfy"
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

    predicate CellInv(t: Tokens.Token, loc: Loc)
    requires |this.cells| == size()
    {
      && t.loc == loc
      && exists cells_v :: (
        && t.val == M(None, None, cells_v, ProducerUnknown, ConsumerUnknown)
        && (forall i: nat | i < size() :: 
          && i in cells_v.Keys
          && ((cells_v[i].Full? || cells_v[i].Empty?) ==> cells_v[i].v.ptr == this.cells[i])
          && (cells_v[i].Full? ==> cells_v[i].v.PointsToLinear?)
          && (cells_v[i].Empty? ==> cells_v[i].v.PointsToEmpty?)
        )
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

          assert head_g.loc == cellToken_g.loc == consumer_g.loc;
          assert head_g.val == M(Some(head_value as nat), None, map[], ProducerUnknown, ConsumerUnknown);
          assert consumer_g.val == M(None, None, map[], ProducerUnknown, ConsumerIdle(tail as nat));

          ghost var rest := Tokens.obtain_invariant_3(
            inout consumer_g, inout head_g, inout cellToken_g);

          ghost var m := dot(dot(consumer_g.val, head_g.val), cellToken_g.val);
          assert MInv(dot(m, rest));

          if head_value != tail {
            assert dot(m, rest).cells[tail as nat].Full?;
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

          ghost_release cellToken_g;
        }
        ghost_release head_g;
      }

      if head_value != tail {
        linear var item_v := this.cells[tail].read_linear(inout pointsToCell.value);
        item := lSome(item_v);

        var newTail := tail + 1;

        atomic_block var _ := execute_atomic_store(this.tail, newTail) {
          ghost_acquire tail_g;

          atomic_block var _ := execute_atomic_noop(this.cellToken) {
            ghost_acquire cellToken_g;

            ghost var m := dot(dot(consumer_g.val, tail_g.val), cellToken_g.val);

            ghost var rest := Tokens.obtain_invariant_3(
              inout consumer_g, inout tail_g, inout cellToken_g);
            
            assert dot(m, rest).cells[tail as nat].Consuming?;
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

            ghost_release cellToken_g;
          }

          ghost_release tail_g;
        }

      } else {
        item := lNone;
        GlinearOption.dispose_glnone(pointsToCell);
      }

      consumerToken := ConsumerToken(consumer_g, tail);
      assert consumerToken.Valid(this.loc);
    }

  }
}
