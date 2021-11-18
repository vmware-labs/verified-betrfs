include "../../lib/Lang/NativeTypes.s.dfy"
include "InfiniteLogTokens.i.dfy"
include "CyclicBuffer.i.dfy"
include "../framework/Cells.s.dfy"
include "../framework/GlinearOption.s.dfy"
include "Constants.i.dfy"

module CyclicBufferTokens(nrifc: NRIfc) {
  import opened NativeTypes
  import opened Options

  import opened IL = InfiniteLogSSM(nrifc)
  import opened ILT = InfiniteLogTokens(nrifc)
  import opened GhostLoc
  import opened GlinearOption
  import opened Cells
  import opened Constants
  import CB = CyclicBufferRw(nrifc)
  import CBTokens = MultiRwTokens(CB)

  function cb_loc() : Loc // XXX TODO(andrea)
  ensures cb_loc().ExtLoc? && cb_loc().base_loc == CBTokens.Wrap.singleton_loc()

  // TODO add 'ghost loc' to these types

  // Use 'CB' prefix to distinguish these from the corresponding state in the InfiniteLog
  // state machine.
  datatype {:glinear_fold} CBHead = CBHead(ghost head: nat)
  {
    function defn(): CBTokens.Token {
      CBTokens.T.Token(cb_loc(),
        CB.M(Some(head), None, map[], None, map[], map[])
      )
    }
  }

  datatype {:glinear_fold} CBLocalTail = CBLocalTail(ghost nodeId: nat, ghost tail: nat)
  {
    function defn(): CBTokens.Token {
      CBTokens.T.Token(cb_loc(),
        CB.M(None, None, map[nodeId := tail], None, map[], map[])
      )
    }
  }

  datatype {:glinear_fold} CBGlobalTail = CBGlobalTail(ghost tail: nat)
  {
    function defn(): CBTokens.Token {
      CBTokens.T.Token(cb_loc(),
        CB.M(None, Some(tail), map[], None, map[], map[])
      )
    }
  }

  // The 'alive' bit flips back and forth. So sometimes 'true' means 'alive',
  // and sometimes 'false' means 'alive'.
  // entry is an index into the buffer (0 <= entry < LOG_SIZE)
  datatype {:glinear_fold} CBAliveBit = CBAliveBit(ghost entry: nat, ghost bit: bool)
  {
    function defn(): CBTokens.Token {
      CBTokens.T.Token(cb_loc(),
        CB.M(None, None, map[], None, map[entry := bit], map[])
      )
    }
  }

  // For advancing the head. We iterate idx from 0 .. NUM_REPLICAS and collect
  // the min of all tails. Then we can set head to min_tail.
  // datatype CBAdvanceHeadState = CBAdvanceHeadState(ghost idx: nat, ghost min_tail: nat)

  // For advancing the tail and writing new log entries.
  // First read the head, then advance the tail to some value allowed by the head.
  // Then write the actual log entries.
  datatype CBAdvanceTailState = CBAdvanceTailState(ghost observed_head: nat)
  datatype CBAppendState = CBAppendState(ghost cur_idx: nat, ghost tail: nat)

  // Contents stored in the log.
  //
  // `contents` maps an unbounded int to the resource protected there.
  // The user of the CyclicBuffer state machine can thus maintain an invariant
  // between the (unbounded) int and the resource.
  //
  // The way this is used is that the user, who is ready to write log-entry N,
  //    * Advances the tail, obtaining access to buffer entry N % LOG_SIZE
  //      which currently has entry N - LOG_SIZE
  //    * They overwrite that entry with log entry N
  //    * Return write-access to the CyclicBuffer protocol by setting the 'alive' bit
  //
  // Thus, for convenience, the `contents` needs to be initialized with
  // -LOG_SIZE, ..., -1

  datatype {:glinear_fold} CBContents = CBContents(ghost contents: map<int, CB.StoredType>)
  {
    function defn(): CBTokens.Token {
      CBTokens.T.Token(cb_loc(),
        CB.M(None, None, map[], Some(contents), map[], map[])
      )
    }
  }

  // For reading
  // To begin reading, you can go
  //
  //      ReaderIdle --> CBReaderStarting --> CBReaderRange
  //
  // by reading first the localTail and the globalTail. This gives you the ability
  // to read elements from that range.
  // To actually read an element, you have to move into the guard state
  //
  //      CBReaderRange --> CBReaderGuard
  //
  // by checking that the 'alive' bit on that element is correct.
  // When you're done with a guard you can go back to the CBReaderRange state:
  //
  //      CBReaderGuard --> CBReaderRange
  //
  // (This only allows a guard for a single element at once, but this is all we need
  // and makes it a bit easier to maintain a simple state.)
  // Finally when we are done we can return to the idle state
  //
  //      CBReaderRange --> ReaderIdle
  //
  // by writing to the localTail.

  // datatype CBReaderState =
  //   | CBReaderStarting(ghost start: nat)
  //   | CBReaderRange(ghost start: nat, ghost end: nat)
  //   | CBReaderGuard(ghost start: nat, ghost end: nat, ghost cur: nat, ghost val: StoredType)

  // datatype CBCombinerState =
  //   | CBCombinerIdle
  //   | CBCombinerReading(ghost readerState: CBReaderState)
  //   | CBCombinerAdvancingHead(ghost idx: nat, ghost min_tail: nat)
  //   | CBCombinerAdvancingTail(ghost obvserve_head: nat)
  //   | CBCombinerAppendState(ghost cur_idx: nat, ghost tail: nat)

  datatype {:glinear_fold} CBCombinerToken = CBCombinerToken(ghost nodeId: CB.NodeId, ghost rs: CB.CombinerState)
  {
    function defn(): CBTokens.Token {
      CBTokens.T.Token(cb_loc(),
        CB.M(None, None, map[], None, map[], map[nodeId := rs])
      )
    }
  }

  glinear method init_advance_head_state(glinear combiner: CBCombinerToken, gshared first_local_tail: CBLocalTail)
  returns (glinear combiner': CBCombinerToken)
  requires first_local_tail.nodeId == 0
  requires combiner.rs == CB.CombinerIdle
  ensures combiner'.nodeId == combiner.nodeId
  ensures combiner'.rs == CB.CombinerAdvancingHead(1, first_local_tail.tail)
  {
    gshared var t_token := CBLocalTail_unfold_borrow(first_local_tail);
    ghost var nodeId := combiner.nodeId;
    glinear var c_token := CBCombinerToken_unfold(combiner);

    ghost var out_expect := CBCombinerToken(nodeId, CB.CombinerAdvancingHead(1, first_local_tail.tail));
    ghost var out_token_expect := CBCombinerToken_unfold(out_expect);

    CB.InitAdvanceHead_is_transition(
      CB.dot(t_token.val, c_token.val),
      CB.dot(t_token.val, out_token_expect.val),
      nodeId);

    glinear var out_token := CBTokens.internal_transition_1_1_1(c_token, t_token, out_token_expect.val);

    combiner' := CBCombinerToken_fold(out_expect, out_token);
  }

  glinear method step_advance_head_state(glinear combiner: CBCombinerToken, gshared local_tail: CBLocalTail)
  returns (glinear combiner': CBCombinerToken)
  requires combiner.rs.CombinerAdvancingHead?
  requires local_tail.nodeId == combiner.rs.idx
  requires combiner.rs.idx != NUM_REPLICAS as nat
  ensures combiner'.nodeId == combiner.nodeId
  ensures combiner'.rs == CB.CombinerAdvancingHead(combiner.rs.idx + 1,
      if combiner.rs.min_tail < local_tail.tail then combiner.rs.min_tail else local_tail.tail)
  {
    gshared var t_token := CBLocalTail_unfold_borrow(local_tail);
    ghost var nodeId := combiner.nodeId;
    glinear var c_token := CBCombinerToken_unfold(combiner);

    ghost var out_expect := CBCombinerToken(nodeId, CB.CombinerAdvancingHead(
      combiner.rs.idx + 1, if combiner.rs.min_tail < local_tail.tail then combiner.rs.min_tail else local_tail.tail));
    ghost var out_token_expect := CBCombinerToken_unfold(out_expect);

    assert combiner.rs.idx <= NUM_REPLICAS as nat; // TODO for Travis: from the invariant
    assert combiner.rs.idx < NUM_REPLICAS as nat; // invariant + requires
    CB.StepAdvanceHead_is_transition(
      CB.dot(t_token.val, c_token.val),
      CB.dot(t_token.val, out_token_expect.val),
      nodeId);

    glinear var out_token := CBTokens.internal_transition_1_1_1(c_token, t_token, out_token_expect.val);

    combiner' := CBCombinerToken_fold(out_expect, out_token);
  }

  glinear method abandon_advance_head_state(glinear combiner: CBCombinerToken)
  returns (glinear combiner': CBCombinerToken)
  requires combiner.rs.CombinerAdvancingHead?
  requires combiner.rs.idx == NUM_REPLICAS as nat
  ensures combiner'.nodeId == combiner.nodeId
  ensures combiner'.rs == CB.CombinerIdle
  {
    ghost var nodeId := combiner.nodeId;
    glinear var c_token := CBCombinerToken_unfold(combiner);

    ghost var out_expect_1 := CBCombinerToken(nodeId, CB.CombinerIdle);
    ghost var out_token_expect_1 := CBCombinerToken_unfold(out_expect_1);

    CB.AbandonAdvanceHead_is_transition(
      c_token.val,
      out_token_expect_1.val,
      nodeId);

    glinear var out_token_1 := CBTokens.internal_transition(c_token, out_token_expect_1.val);
    combiner' := CBCombinerToken_fold(out_expect_1, out_token_1);
  }

  glinear method finish_advance_head_state(glinear combiner: CBCombinerToken, glinear head: CBHead)
  returns (glinear combiner': CBCombinerToken, glinear head': CBHead)
  requires combiner.rs.CombinerAdvancingHead?
  requires combiner.rs.idx == NUM_REPLICAS as int
  ensures combiner'.nodeId == combiner.nodeId
  ensures combiner'.rs == CB.CombinerIdle
  ensures head' == CBHead(combiner.rs.min_tail)
  {
    glinear var h_token := CBHead_unfold(head);
    ghost var nodeId := combiner.nodeId;
    glinear var c_token := CBCombinerToken_unfold(combiner);

    ghost var out_expect_1 := CBCombinerToken(nodeId, CB.CombinerIdle);
    ghost var out_token_expect_1 := CBCombinerToken_unfold(out_expect_1);

    ghost var out_expect_2 := CBHead(combiner.rs.min_tail);
    ghost var out_token_expect_2 := CBHead_unfold(out_expect_2);

    CB.FinishAdvanceHead_is_transition(
      CB.dot(c_token.val, h_token.val),
      CB.dot(out_token_expect_1.val, out_token_expect_2.val),
      nodeId);

    glinear var out_token_1, out_token_2 := CBTokens.internal_transition_2_2(c_token, h_token, out_token_expect_1.val, out_token_expect_2.val);
    combiner' := CBCombinerToken_fold(out_expect_1, out_token_1);
    head' := CBHead_fold(out_expect_2, out_token_2);
  }

  glinear method init_advance_tail_state(glinear combiner: CBCombinerToken, gshared head: CBHead)
  returns (glinear combiner': CBCombinerToken)
  requires combiner.rs == CB.CombinerIdle
  ensures combiner'.nodeId == combiner.nodeId
  ensures combiner'.rs == CB.CombinerAdvancingTail(head.head)
  {
    gshared var h_token := CBHead_unfold_borrow(head);
    ghost var nodeId := combiner.nodeId;
    glinear var c_token := CBCombinerToken_unfold(combiner);

    ghost var out_expect := CBCombinerToken(nodeId, CB.CombinerAdvancingTail(head.head));
    ghost var out_token_expect := CBCombinerToken_unfold(out_expect);

    CB.InitAdvanceTail_is_transition(
      CB.dot(h_token.val, c_token.val),
      CB.dot(h_token.val, out_token_expect.val),
      nodeId);

    glinear var out_token := CBTokens.internal_transition_1_1_1(c_token, h_token, out_token_expect.val);

    combiner' := CBCombinerToken_fold(out_expect, out_token);
  }

  ghost method XXX_TODO_invent<A>() returns (a: A)
  glinear method XXX_TODO_invent_glinear<A>() returns (glinear a: A)

  glinear method abandon_advance_tail(glinear combiner: CBCombinerToken)
  returns (glinear combiner': CBCombinerToken)
  requires combiner.rs.CombinerAdvancingTail?
  ensures combiner'.nodeId == combiner.nodeId
  ensures combiner'.rs == CB.CombinerIdle
  {
    ghost var nodeId := combiner.nodeId;
    glinear var c_token := CBCombinerToken_unfold(combiner);

    ghost var out_expect_1 := CBCombinerToken(nodeId, CB.CombinerIdle);
    ghost var out_token_expect_1 := CBCombinerToken_unfold(out_expect_1);

    CB.AbandonAdvanceTail_is_transition(
      c_token.val,
      out_token_expect_1.val,
      nodeId);

    glinear var out_token_1 := CBTokens.internal_transition(c_token, out_token_expect_1.val);
    combiner' := CBCombinerToken_fold(out_expect_1, out_token_1);
  }

  glinear method finish_advance_tail(glinear combiner: CBCombinerToken, glinear tail: CBGlobalTail,
      glinear contents: CBContents, ghost new_tail: nat)
  returns (glinear combiner': CBCombinerToken, glinear tail': CBGlobalTail, glinear contents': CBContents, glinear entries': map<nat, CB.StoredType>)
  requires combiner.rs.CombinerAdvancingTail?
  requires tail.tail <= new_tail <= combiner.rs.observed_head + LOG_SIZE as int
  ensures combiner'.nodeId == combiner.nodeId
  ensures tail'.tail == new_tail
  ensures forall i | tail.tail <= i < new_tail ::
      && i in entries'
      && (i - LOG_SIZE as int) in contents.contents
      && entries'[i] == contents.contents[i - LOG_SIZE as int]
  ensures forall i | i in contents'.contents :: i in contents.contents && contents.contents[i] == contents'.contents[i]
  ensures combiner'.rs == CB.CombinerAppending(tail.tail, new_tail)
  {
    glinear var t_token := CBGlobalTail_unfold(tail);
    ghost var nodeId := combiner.nodeId;
    glinear var c_token := CBCombinerToken_unfold(combiner);
    glinear var contents_token := CBContents_unfold(contents);

    ghost var out_expect_1 := CBCombinerToken(nodeId, CB.CombinerIdle);
    ghost var out_token_expect_1 := CBCombinerToken_unfold(out_expect_1);

    ghost var out_expect_2 := CBGlobalTail(new_tail);
    ghost var out_token_expect_2 := CBGlobalTail_unfold(out_expect_2);

    ghost var out_expect_3 := XXX_TODO_invent<CBContents>();
    ghost var out_token_expect_3 := CBContents_unfold(out_expect_3);

    ghost var withdrawn := map i |
      && tail.tail <= i < new_tail
      // TODO
      :: (assume i - LOG_SIZE as int in contents.contents; contents.contents[i - LOG_SIZE as int]);

    assume false; // TODO
    CB.FinishAdvanceTail_is_withdraw_many(
      CB.dot(CB.dot(c_token.val, t_token.val), contents_token.val),
      CB.dot(CB.dot(out_token_expect_1.val, out_token_expect_2.val), out_token_expect_3.val),
      nodeId, new_tail, withdrawn);

    glinear var out_token_1, out_token_2, out_token_3, w_entries := CBTokens.withdraw_many_3_3(c_token, t_token, contents_token, out_token_expect_1.val, out_token_expect_2.val, out_token_expect_3.val, withdrawn);
    combiner' := CBCombinerToken_fold(out_expect_1, out_token_1);
    tail' := CBGlobalTail_fold(out_expect_2, out_token_2);
    contents' := CBContents_fold(out_expect_3, out_token_3);

    // TODO entries' keys should be shifted down by LOG_SIZE

    entries' := w_entries;
    assume false;
  }

  glinear method append_flip_bit(
      glinear combiner: CBCombinerToken, glinear bit: CBAliveBit, glinear contents: CBContents, glinear value: CB.StoredType)
  returns (glinear combiner': CBCombinerToken, glinear bit': CBAliveBit, glinear contents': CBContents)
  requires combiner.rs.CombinerAppending?
  requires combiner.rs.cur_idx < combiner.rs.tail
  requires bit.entry == CB.LogicalToPhysicalIndex(combiner.rs.cur_idx)
  ensures combiner'.nodeId == combiner.nodeId
  ensures combiner'.rs == combiner.rs.(cur_idx := combiner.rs.cur_idx + 1)
  ensures bit' == bit.(bit := CB.LogicalToAliveBitAliveWhen(combiner.rs.cur_idx))
  ensures contents' == contents.(contents := contents.contents[combiner.rs.cur_idx := value])
  {
    glinear var a_token := CBAliveBit_unfold(bit);
    ghost var nodeId := combiner.nodeId;
    glinear var c_token := CBCombinerToken_unfold(combiner);

    glinear var contents_token := CBContents_unfold(contents);

    ghost var out_expect_1 := CBCombinerToken(nodeId, combiner.rs.(cur_idx := combiner.rs.cur_idx + 1));
    ghost var out_token_expect_1 := CBCombinerToken_unfold(out_expect_1);

    ghost var out_expect_2 := bit.(bit := CB.LogicalToAliveBitAliveWhen(combiner.rs.cur_idx));
    ghost var out_token_expect_2 := CBAliveBit_unfold(out_expect_2);

    ghost var out_expect_3 := contents.(contents := contents.contents[combiner.rs.cur_idx := value]);
    ghost var out_token_expect_3 := CBContents_unfold(out_expect_3);

    ghost var key := combiner.rs.cur_idx;

    assume key !in contents.contents; // TODO ask Travis
    assume !CB.EntryIsAlive(a_token.val.aliveBits, key); // TODO ask Travis
    CB.AppendFlipBit_is_deposit(
      CB.dot(CB.dot(c_token.val, a_token.val), contents_token.val),
      CB.dot(CB.dot(out_token_expect_1.val, out_token_expect_2.val), out_token_expect_3.val),
      nodeId,
      value);

    glinear var out_token_1, out_token_2, out_token_3 := CBTokens.deposit_3_3(c_token, a_token, contents_token, key, value,
      out_token_expect_1.val, out_token_expect_2.val, out_token_expect_3.val);

    combiner' := CBCombinerToken_fold(out_expect_1, out_token_1);
    bit' := CBAliveBit_fold(out_expect_2, out_token_2);
    contents' := CBContents_fold(out_expect_3, out_token_3);
  }

  glinear method finish_appending(glinear combiner: CBCombinerToken)
  returns (glinear combiner': CBCombinerToken)
  requires combiner.rs.CombinerAppending?
  requires combiner.rs.cur_idx == combiner.rs.tail
  ensures combiner'.nodeId == combiner.nodeId
  ensures combiner'.rs == CB.CombinerIdle
  {
    ghost var nodeId := combiner.nodeId;
    glinear var c_token := CBCombinerToken_unfold(combiner);

    ghost var out_expect_1 := CBCombinerToken(nodeId, CB.CombinerIdle);
    ghost var out_token_expect_1 := CBCombinerToken_unfold(out_expect_1);

    CB.FinishAppending_is_transition(
      c_token.val,
      out_token_expect_1.val,
      nodeId);

    glinear var out_token_1 := CBTokens.internal_transition(c_token, out_token_expect_1.val);

    combiner' := CBCombinerToken_fold(out_expect_1, out_token_1);
  }

  glinear method reader_start(glinear combiner: CBCombinerToken, gshared localTail: CBLocalTail)
  returns (glinear combiner': CBCombinerToken)
  requires combiner.nodeId == localTail.nodeId
  requires combiner.rs.CombinerIdle?
  ensures combiner' == combiner.(rs := CB.CombinerReading(CB.ReaderStarting(localTail.tail)))

  glinear method reader_abort(glinear combiner: CBCombinerToken)
  returns (glinear combiner': CBCombinerToken)
  requires combiner.rs.CombinerReading? && combiner.rs.readerState.ReaderStarting?
  ensures combiner' == combiner.(rs := CB.CombinerIdle)

  glinear method reader_enter(glinear combiner: CBCombinerToken, gshared globalTail: CBGlobalTail)
  returns (glinear combiner': CBCombinerToken)
  requires combiner.rs.CombinerReading? && combiner.rs.readerState.ReaderStarting?
  ensures combiner' == combiner.(rs := CB.CombinerReading(CB.ReaderRange(combiner.rs.readerState.start, globalTail.tail, combiner.rs.readerState.start)))

  glinear method reader_guard(glinear combiner: CBCombinerToken, gshared aliveBit: CBAliveBit, ghost i: nat,
      gshared contents: CBContents)
  returns (glinear combiner': CBCombinerToken)
  requires combiner.rs.CombinerReading? && combiner.rs.readerState.ReaderRange?
  requires combiner.rs.readerState.start <= i < combiner.rs.readerState.end
  requires i % LOG_SIZE as int == aliveBit.entry
  requires aliveBit.bit == ((i / LOG_SIZE as int) % 2 == 0)
  ensures i in contents.contents
  ensures combiner' == combiner.(rs := CB.CombinerReading(CB.ReaderGuard(combiner.rs.readerState.start, combiner.rs.readerState.end,
      i, contents.contents[i])))

  glinear method reader_unguard(glinear combiner: CBCombinerToken)
  returns (glinear combiner': CBCombinerToken)
  requires combiner.rs.CombinerReading? && combiner.rs.readerState.ReaderGuard?
  ensures combiner' == combiner.(rs := CB.CombinerReading(CB.ReaderRange(combiner.rs.readerState.start, combiner.rs.readerState.end, combiner.rs.readerState.cur + 1)))

  glinear method reader_finish(glinear combiner: CBCombinerToken, glinear localTail: CBLocalTail)
  returns (glinear combiner': CBCombinerToken, glinear localTail': CBLocalTail)
  requires combiner.nodeId == localTail.nodeId
  requires combiner.rs.CombinerReading? && combiner.rs.readerState.ReaderRange?
  requires combiner.rs.readerState.cur == combiner.rs.readerState.end;
  ensures combiner' == combiner.(rs := CB.CombinerIdle)
  ensures localTail' == localTail.(tail := combiner.rs.readerState.end)
  {
    glinear var l_token := CBLocalTail_unfold(localTail);
    ghost var nodeId := combiner.nodeId;
    glinear var c_token := CBCombinerToken_unfold(combiner);

    ghost var out_expect_1 := CBCombinerToken(nodeId, CB.CombinerIdle);
    ghost var out_token_expect_1 := CBCombinerToken_unfold(out_expect_1);

    ghost var out_expect_2 := localTail.(tail := combiner.rs.readerState.end);
    ghost var out_token_expect_2 := CBLocalTail_unfold(out_expect_2);

    CB.ReaderDoFinish_is_transition(
      CB.dot(c_token.val, l_token.val),
      CB.dot(out_token_expect_1.val, out_token_expect_2.val),
      nodeId);

    glinear var out_token_1, out_token_2 := CBTokens.internal_transition_2_2(c_token, l_token, out_token_expect_1.val, out_token_expect_2.val);

    combiner' := CBCombinerToken_fold(out_expect_1, out_token_1);
    localTail' := CBLocalTail_fold(out_expect_2, out_token_2);
  }

  function method reader_borrow(gshared combiner: CBCombinerToken)
    : (gshared v: CB.StoredType)
  requires combiner.rs.CombinerReading? && combiner.rs.readerState.ReaderGuard?
  ensures v == combiner.rs.readerState.val

  glinear method cyclic_buffer_init(glinear m: map<int, CB.StoredType>)
  returns (
    glinear head: CBHead,
    glinear globalTail: CBGlobalTail,
    glinear localTails: map<nat, CBLocalTail>,
    glinear alive: map<nat, CBAliveBit>,
    glinear contents: CBContents,
    glinear readers: map<nat, CBCombinerToken>
  )
  requires forall i :: -(LOG_SIZE as int) <= i < 0 <==> i in m
  ensures head == CBHead(0)
  ensures globalTail == CBGlobalTail(0)
  ensures forall i | 0 <= i < NUM_REPLICAS as int ::
      && i in localTails && localTails[i] == CBLocalTail(i, 0)
      && i in readers && readers[i] == CBCombinerToken(i, CB.CombinerIdle)
  ensures forall i | 0 <= i < LOG_SIZE as int ::
      i in alive && alive[i] == CBAliveBit(i, false)
  ensures contents == CBContents(m)
}
