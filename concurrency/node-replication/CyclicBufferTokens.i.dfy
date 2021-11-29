include "../../lib/Lang/NativeTypes.s.dfy"
include "InfiniteLogTokens.i.dfy"
include "CyclicBuffer.i.dfy"
include "../framework/Cells.s.dfy"
include "../framework/GlinearOption.s.dfy"
include "../framework/GlinearMap.s.dfy"
include "../framework/Ptrs.s.dfy"
include "Constants.i.dfy"

module CyclicBufferTokens(nrifc: NRIfc) {
  import opened NativeTypes
  import opened Options

  import opened IL = InfiniteLogSSM(nrifc)
  import opened ILT = InfiniteLogTokens(nrifc)
  import opened GhostLoc
  import opened GlinearOption
  import GlinearMap
  import opened Cells
  import opened Constants
  import Maps
  import CB = CyclicBufferRw(nrifc)
  import CBTokens = MultiRwTokens(CB)
  import Ptrs

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

  /* ----------------------------------------------------------------------------------------- */

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

  /* ----------------------------------------------------------------------------------------- */

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

    ghost var rest := CBTokens.obtain_invariant_1_1(t_token, inout c_token);

    assert combiner.rs.idx <= NUM_REPLICAS as nat by {
      assert nodeId in c_token.val.combinerState && c_token.val.combinerState[nodeId].idx <= NUM_REPLICAS as nat; // observe
    }

    CB.StepAdvanceHead_is_transition(
      CB.dot(t_token.val, c_token.val),
      CB.dot(t_token.val, out_token_expect.val),
      nodeId);

    glinear var out_token := CBTokens.internal_transition_1_1_1(c_token, t_token, out_token_expect.val);

    combiner' := CBCombinerToken_fold(out_expect, out_token);
  }

  /* ----------------------------------------------------------------------------------------- */

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

  /* ----------------------------------------------------------------------------------------- */

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

  /* ----------------------------------------------------------------------------------------- */

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

  /* ----------------------------------------------------------------------------------------- */

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

  /* ----------------------------------------------------------------------------------------- */

  glinear method finish_advance_tail(glinear combiner: CBCombinerToken, glinear tail: CBGlobalTail,
      glinear contents: CBContents, ghost new_tail: nat)
  returns (glinear combiner': CBCombinerToken, glinear tail': CBGlobalTail, glinear contents': CBContents, glinear entries': map<int, CB.StoredType>)
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

    ghost var out_expect_1 := CBCombinerToken(nodeId, CB.CombinerAppending(tail.tail, new_tail));
    ghost var out_token_expect_1 := CBCombinerToken_unfold(out_expect_1);

    ghost var out_expect_2 := CBGlobalTail(new_tail);
    ghost var out_token_expect_2 := CBGlobalTail_unfold(out_expect_2);

    ghost var rest := CBTokens.obtain_invariant_3(inout c_token, inout t_token, inout contents_token);
    assert contents_token.val.contents.Some? && contents.contents == contents_token.val.contents.value;
    assert t_token.val.tail.Some? && t_token.val.tail.value == tail.tail;
    assert nodeId in c_token.val.combinerState && combiner.rs == c_token.val.combinerState[nodeId];

    ghost var all := CB.dot(CB.dot(CB.dot(c_token.val, t_token.val), contents_token.val), rest);
    assert CB.Inv(all);

    assert forall i: int |  tail.tail <= i < new_tail :: i !in contents.contents;

    assert forall i: int |  tail.tail - LOG_SIZE as int <= i < new_tail - LOG_SIZE as int :: i in contents.contents by {
      assert all.contents.value == contents.contents;
      assert all.tail.value == tail.tail;

      assert combiner.rs.observed_head  <= CB.MinLocalTail(all.localTails) by {
        CB.reveal_MinLocalTail();
      }
    }

    ghost var withdrawn := map i : int | tail.tail - LOG_SIZE as int <= i < new_tail - LOG_SIZE as int :: contents.contents[i];

    assert forall i: int | i in withdrawn.Keys :: i in contents.contents && withdrawn[i] == contents.contents[i];

    // remove the withdrawn keys from contents
    ghost var out_expect_3 := CBContents(Maps.MapRemove(contents.contents, withdrawn.Keys));
    ghost var out_token_expect_3 := CBContents_unfold(out_expect_3);

    CB.FinishAdvanceTail_is_withdraw_many(
      CB.dot(CB.dot(c_token.val, t_token.val), contents_token.val),
      CB.dot(CB.dot(out_token_expect_1.val, out_token_expect_2.val), out_token_expect_3.val),
      nodeId, new_tail, withdrawn);

    glinear var out_token_1, out_token_2, out_token_3, w_entries := CBTokens.withdraw_many_3_3(c_token, t_token, contents_token, out_token_expect_1.val, out_token_expect_2.val, out_token_expect_3.val, withdrawn);
    combiner' := CBCombinerToken_fold(out_expect_1, out_token_1);
    tail' := CBGlobalTail_fold(out_expect_2, out_token_2);
    contents' := CBContents_fold(out_expect_3, out_token_3);

    assert forall k: int :: tail.tail - LOG_SIZE as int <= k < new_tail - LOG_SIZE as int <==> k in w_entries;

    entries' := GlinearMap.glmap_empty();

    ghost var j: int := tail.tail - LOG_SIZE as int;

    while j < new_tail - LOG_SIZE as int
    invariant tail.tail - LOG_SIZE as int <= j
    invariant j <= new_tail - LOG_SIZE as int
    invariant forall k: int :: (
      && (k < j ==> k !in w_entries)
      && (j <= k < new_tail - LOG_SIZE as int ==> k in w_entries)
      && (new_tail - LOG_SIZE as int <= k ==> k !in w_entries)
    )
    invariant forall k: int :: (
      && (k < tail.tail ==> k !in entries')
      && (tail.tail <= k < j + LOG_SIZE as int ==> k in entries')
      && (j + LOG_SIZE as int <= k ==> k !in entries')
    )
    invariant forall k: int | k in w_entries :: w_entries[k] == contents.contents[k]
    invariant forall k: int | tail.tail <= k < j + LOG_SIZE as int :: entries'[k] == contents.contents[k - LOG_SIZE as int]
    {
      glinear var v;
      w_entries, v := GlinearMap.glmap_take(w_entries, j);
      entries' := GlinearMap.glmap_insert(entries', j + LOG_SIZE as int, v);

      j := j + 1;
    }
    Ptrs.dispose_anything(w_entries);
  }

  /* ----------------------------------------------------------------------------------------- */

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

    ghost var rest := CBTokens.obtain_invariant_3(inout a_token, inout c_token, inout contents_token);
    ghost var all := CB.dot(CB.dot(CB.dot(a_token.val, c_token.val), contents_token.val), rest);
    assert CB.CombinerStateValid(all);
    assert nodeId in c_token.val.combinerState && combiner.rs == c_token.val.combinerState[nodeId];
    assert bit.entry in a_token.val.aliveBits && a_token.val.aliveBits[bit.entry] == bit.bit;
    assert all.aliveBits[CB.LogicalToPhysicalIndex(key)] == a_token.val.aliveBits[bit.entry];
    assert contents_token.val.contents.Some? && contents.contents == contents_token.val.contents.value;

    assert CB.Inv(all);

    assert !CB.EntryIsAlive(a_token.val.aliveBits, key) by {
      assert forall i : nat | combiner.rs.cur_idx <= i < combiner.rs.tail :: (
        && CB.LogicalToPhysicalIndex(i) < LOG_SIZE as nat
        && CB.LogicalToPhysicalIndex(i) in all.aliveBits
      ) by {
        CB.reveal_AliveBitsComplete();
      }
      // do we need the non-overlap thing here?

      CB.reveal_RangesNoOverlapCombinerReader();
      CB.reveal_RangesNoOverlapCombinerCombiner();

      assert forall i : nat | combiner.rs.cur_idx <= i < combiner.rs.tail :: (
        && !(CB.EntryIsAlive(all.aliveBits, i))
      );
    }

    // we know that the entry is not alive
    // we know that MinLocalTails <= localTail[nodeId] <= key
    // thus:
    assert key !in contents.contents by {
      CB.reveal_LocalTailsComplete();
      CB.reveal_CombinerStateComplete();
      assert CB.MinLocalTail(all.localTails) <= all.localTails[nodeId];
      assert CB.MinLocalTail(all.localTails) <= key;
    }

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

  /* ----------------------------------------------------------------------------------------- */

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

  /* ----------------------------------------------------------------------------------------- */

  glinear method reader_start(glinear combiner: CBCombinerToken, gshared localTail: CBLocalTail)
  returns (glinear combiner': CBCombinerToken)
  requires combiner.nodeId == localTail.nodeId
  requires combiner.rs.CombinerIdle?
  ensures combiner' == combiner.(rs := CB.CombinerReading(CB.ReaderStarting(localTail.tail)))
  {
    gshared var t_token := CBLocalTail_unfold_borrow(localTail);
    ghost var nodeId := combiner.nodeId;
    glinear var c_token := CBCombinerToken_unfold(combiner);

    ghost var out_expect := CBCombinerToken(nodeId, CB.CombinerReading(CB.ReaderStarting(localTail.tail)));
    ghost var out_token_expect := CBCombinerToken_unfold(out_expect);

    CB.ReaderDoStart_is_transition(
      CB.dot(t_token.val, c_token.val),
      CB.dot(t_token.val, out_token_expect.val),
      nodeId);

    glinear var out_token := CBTokens.internal_transition_1_1_1(c_token, t_token, out_token_expect.val);

    combiner' := CBCombinerToken_fold(out_expect, out_token);

  }

  /* ----------------------------------------------------------------------------------------- */

  glinear method reader_abort(glinear combiner: CBCombinerToken)
  returns (glinear combiner': CBCombinerToken)
  requires combiner.rs.CombinerReading? && combiner.rs.readerState.ReaderStarting?
  ensures combiner' == combiner.(rs := CB.CombinerIdle)
  {
    // get the node id and combiner token
    ghost var nodeId := combiner.nodeId;
    glinear var c_token := CBCombinerToken_unfold(combiner);

    // updated result
    ghost var out_expect := CBCombinerToken(nodeId, CB.CombinerIdle);
    ghost var out_token_expect := CBCombinerToken_unfold(out_expect);

    // the transition
    CB.ReaderDoAbort_is_transition(c_token.val,out_token_expect.val,nodeId);

    // do the internal transition
    glinear var out_token := CBTokens.internal_transition(c_token, out_token_expect.val);

    // update the combiner
    combiner' := CBCombinerToken_fold(out_expect, out_token);
  }

  /* ----------------------------------------------------------------------------------------- */

  glinear method reader_enter(glinear combiner: CBCombinerToken, gshared globalTail: CBGlobalTail)
  returns (glinear combiner': CBCombinerToken)
  requires combiner.rs.CombinerReading? && combiner.rs.readerState.ReaderStarting?
  ensures combiner' == combiner.(rs := CB.CombinerReading(CB.ReaderRange(combiner.rs.readerState.start, globalTail.tail, combiner.rs.readerState.start)))
  {

    // get the node id and combiner token
    ghost var nodeId := combiner.nodeId;
    glinear var c_token := CBCombinerToken_unfold(combiner);

    // the local tail
    gshared var t_token := CBGlobalTail_unfold_borrow(globalTail);

    // updated result
    ghost var out_expect := CBCombinerToken(nodeId, CB.CombinerReading(CB.ReaderRange(combiner.rs.readerState.start, globalTail.tail, combiner.rs.readerState.start)));
    ghost var out_token_expect := CBCombinerToken_unfold(out_expect);

    // the transition
    CB.ReaderDoEnter_is_transition(
        CB.dot(t_token.val, c_token.val),
        CB.dot(t_token.val, out_token_expect.val),
        nodeId);

    // do the internal transition
    glinear var out_token := CBTokens.internal_transition_1_1_1(c_token, t_token, out_token_expect.val);

    // update the combiner
    combiner' := CBCombinerToken_fold(out_expect, out_token);
  }

  /* ----------------------------------------------------------------------------------------- */

  glinear method reader_guard(glinear combiner: CBCombinerToken, gshared aliveBit: CBAliveBit, ghost i: nat,
      glinear contents: CBContents)
  returns (glinear combiner': CBCombinerToken, glinear contents': CBContents)
  requires combiner.rs.CombinerReading? && combiner.rs.readerState.ReaderRange?
  requires combiner.rs.readerState.start <= i < combiner.rs.readerState.end
  requires i % LOG_SIZE as int == aliveBit.entry
  requires aliveBit.bit == ((i / LOG_SIZE as int) % 2 == 0)
  requires i == combiner.rs.readerState.cur
  ensures i in contents.contents
  ensures combiner' == combiner.(rs := CB.CombinerReading(CB.ReaderGuard(combiner.rs.readerState.start, combiner.rs.readerState.end,
      i, contents.contents[i])))
  ensures contents' == contents
  {
    // get the node id and combiner token
    ghost var nodeId := combiner.nodeId;
    glinear var c_token := CBCombinerToken_unfold(combiner);
    gshared var a_token := CBAliveBit_unfold_borrow(aliveBit);

    glinear var contents_token := CBContents_unfold(contents);

    ghost var expected_x := CB.dot(a_token.val, contents_token.val);
    ghost var rest := CBTokens.obtain_invariant_1_2(a_token, inout contents_token, inout c_token);
    ghost var all := CB.dot(CB.dot(a_token.val, CB.dot(contents_token.val, c_token.val)), rest);
    assert CB.Inv(all);

    assert contents_token.val.contents.value == contents.contents;
    assert nodeId in c_token.val.combinerState && combiner.rs == c_token.val.combinerState[nodeId];
    assert combiner.rs.readerState == c_token.val.combinerState[nodeId].readerState;
    assert aliveBit.entry in a_token.val.aliveBits && a_token.val.aliveBits[aliveBit.entry] == aliveBit.bit;

    assert CB.Complete(all);
    assert CB.ReaderStateValid(all);
    assert c_token.val.combinerState[nodeId].readerState.cur in contents_token.val.contents.value by {
      CB.reveal_AliveBitsComplete();
      CB.reveal_LocalTailsComplete();
      CB.reveal_ContentsComplete();

      assert c_token.val.combinerState[nodeId].readerState.cur == i;
      assert c_token.val.combinerState[nodeId].readerState.start <= i;
      assert nodeId in all.localTails by {
        CB.reveal_CombinerStateComplete();
        CB.reveal_LocalTailsComplete();
      }

      assert c_token.val.combinerState[nodeId].readerState.end <= all.tail.value;
      assert c_token.val.combinerState[nodeId].readerState.cur < c_token.val.combinerState[nodeId].readerState.end;

      assert c_token.val.combinerState[nodeId].readerState.start  == all.localTails[nodeId];
      assert i < all.tail.value;
      assert all.tail.value - (LOG_SIZE as nat) <= i;

      assert all.tail.value - (LOG_SIZE as nat) <= i < all.tail.value;
      assert CB.EntryIsAlive(a_token.val.aliveBits, i);
    }
    assert c_token.val.combinerState[nodeId].readerState.start <= c_token.val.combinerState[nodeId].readerState.cur < c_token.val.combinerState[nodeId].readerState.end by {
      CB.reveal_LocalTailsComplete();
      CB.reveal_CombinerStateComplete();
    }
    assert combiner.rs.readerState.cur < combiner.rs.readerState.end;

    assert contents_token.val.contents.value[i] == contents.contents[i];

    ghost var out_expect := CBCombinerToken(nodeId, CB.CombinerReading(CB.ReaderGuard(combiner.rs.readerState.start, combiner.rs.readerState.end, i, contents.contents[i])));
    ghost var out_token_expect := CBCombinerToken_unfold(out_expect);

    assert CB.LogicalToPhysicalIndex(i) in a_token.val.aliveBits;

    // the transition
    // CB.ReaderDoGuard_is_transition(
    //   CB.dot(CB.dot(a_token.val, contents_token.val), c_token.val),
    //   CB.dot(CB.dot(a_token.val, contents_token.val), out_token_expect.val), nodeId, i);

    // the transition
    CB.ReaderDoGuard_is_transition(
      CB.dot(a_token.val, CB.dot(contents_token.val, c_token.val)),
      CB.dot(a_token.val, CB.dot(contents_token.val, out_token_expect.val)), nodeId, i);

    // do the internal transition
    glinear var out_token1, out_token2 := CBTokens.internal_transition_1_2_1(a_token, contents_token, c_token, contents_token.val, out_token_expect.val);

    // update the combiner
    contents' := CBContents_fold(contents, out_token1);
    combiner' := CBCombinerToken_fold(out_expect, out_token2);
  }

  /* ----------------------------------------------------------------------------------------- */

  glinear method reader_unguard(glinear combiner: CBCombinerToken)
  returns (glinear combiner': CBCombinerToken)
  requires combiner.rs.CombinerReading? && combiner.rs.readerState.ReaderGuard?
  ensures combiner' == combiner.(rs := CB.CombinerReading(CB.ReaderRange(combiner.rs.readerState.start, combiner.rs.readerState.end, combiner.rs.readerState.cur + 1)))
  {
    // get the node id and combiner token
    ghost var nodeId := combiner.nodeId;
    glinear var c_token := CBCombinerToken_unfold(combiner);

    // updated result
    ghost var out_expect := CBCombinerToken(nodeId, CB.CombinerReading(CB.ReaderRange(combiner.rs.readerState.start, combiner.rs.readerState.end, combiner.rs.readerState.cur + 1)));
    ghost var out_token_expect := CBCombinerToken_unfold(out_expect);

    // the transition
    CB.ReaderDoUnguard_is_transition(c_token.val,out_token_expect.val,nodeId);

    // do the internal transition
    glinear var out_token := CBTokens.internal_transition(c_token, out_token_expect.val);

    // update the combiner
    combiner' := CBCombinerToken_fold(out_expect, out_token);
  }

  /* ----------------------------------------------------------------------------------------- */

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

  /* ----------------------------------------------------------------------------------------- */

  function method reader_borrow(gshared combiner: CBCombinerToken)
    : (gshared v: CB.StoredType)
  requires combiner.rs.CombinerReading? && combiner.rs.readerState.ReaderGuard?
  ensures v == combiner.rs.readerState.val
  {
    ghost var nodeId := combiner.nodeId;

    gshared var combiner_t := CBCombinerToken_unfold_borrow(combiner);
    //ghost var rest := CBTokens.obtain_invariant_borrow(combiner_t);

    assert combiner.rs.readerState == combiner_t.val.combinerState[nodeId].readerState;

    assert CBTokens.rw.guard(combiner_t.val, combiner.rs.readerState.cur, combiner.rs.readerState.val);
    CBTokens.borrow_from_guard(combiner_t, combiner.rs.readerState.cur, combiner.rs.readerState.val)
  }

  /* ----------------------------------------------------------------------------------------- */

  glinear method do_init_local_tails(glinear t: CBTokens.Token)
  returns (glinear localTails: map<nat, CBLocalTail>)
  requires t.loc == cb_loc()
  requires (
    var localTailsM := map i: nat | 0 <= i < NUM_REPLICAS as nat :: 0;
    t.val == CB.M(None, None, localTailsM, None, map[], map[]))
  ensures forall i | 0 <= i < NUM_REPLICAS as nat ::
      i in localTails && localTails[i] == CBLocalTail(i, 0)
  // {
  //   glinear var t' := t;
  //   ghost var j := 0;
  //   localTails := GlinearMap.glmap_empty();
  //   while j < NUM_REPLICAS as nat
  //   invariant 0 <= j <= NUM_REPLICAS as nat
  //   invariant t'.loc == loc()
  //   invariant t'.val.M?
  // }

  glinear method do_init_alive(glinear t: CBTokens.Token)
  returns (glinear alive: map<nat, CBAliveBit>)
  requires t.loc == cb_loc()
  requires (
    var aliveBitsM := map i: nat | 0 <= i < LOG_SIZE as nat :: false;
    t.val == CB.M(None, None, map[], None, aliveBitsM, map[]))
  ensures forall i | 0 <= i < LOG_SIZE as int ::
      i in alive && alive[i] == CBAliveBit(i, false)

  glinear method do_init_combiners(glinear t: CBTokens.Token)
  returns (glinear combiners: map<nat, CBCombinerToken>)
  requires t.loc == cb_loc()
  requires (
    var combinersM := map i: nat | 0 <= i < NUM_REPLICAS as nat :: CB.CombinerIdle;
    t.val == CB.M(None, None, map[], None, map[], combinersM))
  ensures forall i | 0 <= i < NUM_REPLICAS as int ::
      i in combiners && combiners[i] == CBCombinerToken(i, CB.CombinerIdle)

  glinear method cyclic_buffer_init(glinear b: map<int, CB.StoredType>)
  returns (
    glinear head: CBHead,
    glinear globalTail: CBGlobalTail,
    glinear localTails: map<nat, CBLocalTail>,
    glinear alive: map<nat, CBAliveBit>,
    glinear contents: CBContents,
    glinear combiners: map<nat, CBCombinerToken>
  )
  requires forall i :: -(LOG_SIZE as int) <= i < 0 <==> i in b
  ensures head == CBHead(0)
  ensures globalTail == CBGlobalTail(0)
  ensures forall i | 0 <= i < NUM_REPLICAS as int ::
      && i in localTails && localTails[i] == CBLocalTail(i, 0)
      && i in combiners && combiners[i] == CBCombinerToken(i, CB.CombinerIdle)
  ensures forall i | 0 <= i < LOG_SIZE as int ::
      i in alive && alive[i] == CBAliveBit(i, false)
  ensures contents == CBContents(b)
  {

    ghost var localTailsM := map i: nat | 0 <= i < NUM_REPLICAS as nat :: 0;
    ghost var aliveBitsM := map i: nat | 0 <= i < LOG_SIZE as nat :: false;
    ghost var combinersM := map i: nat | 0 <= i < NUM_REPLICAS as nat :: CB.CombinerIdle;

    ghost var m := CB.M(Some(0), Some(0), localTailsM, Some(b), aliveBitsM, combinersM);

    CB.InitImpliesInv(m);
    glinear var token := CBTokens.initialize_nonempty(b, m);

    ghost var ht := CB.M(Some(0), None, map[], None, map[], map[]);
    ghost var gtt := CB.M(None, Some(0), map[], None, map[], map[]);
    ghost var ltt := CB.M(None, None, localTailsM, None, map[], map[]);
    ghost var ct := CB.M(None, None, map[], Some(b), map[], map[]);
    ghost var at := CB.M(None, None, map[], None, aliveBitsM, map[]);
    ghost var cmt := CB.M(None, None, map[], None, map[], combinersM);

    glinear var tht, tgtt, tltt, tct, tat, tcmt := CBTokens.split6(token, ht, gtt, ltt, ct, at, cmt);

    assume tht.loc == cb_loc(); // TODO(Travis)
    head := CBHead_fold(CBHead(0), tht);
    globalTail := CBGlobalTail_fold(CBGlobalTail(0), tgtt);
    localTails := do_init_local_tails(tltt);
    contents := CBContents_fold(CBContents(b), tct);
    alive := do_init_alive(tat);
    combiners := do_init_combiners(tcmt);
  }
}
