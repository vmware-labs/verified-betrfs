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

  datatype ConcreteLogEntry = ConcreteLogEntry(op: nrifc.UpdateOp, node_id: uint64)

  glinear datatype StoredType = StoredType(
    glinear cellContents: CellContents<ConcreteLogEntry>,
    glinear logEntry: glOption<Log>
  )

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
  datatype CBAdvanceHeadState = CBAdvanceHeadState(ghost idx: nat, ghost min_tail: nat)

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

  datatype Contents = Contents(
    ghost contents: map<int, StoredType>
  )

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

  datatype CBReaderState =
    | CBReaderStarting(ghost start: nat)
    | CBReaderRange(ghost start: nat, ghost end: nat)
    | CBReaderGuard(ghost start: nat, ghost end: nat, ghost cur: nat, ghost val: StoredType)

  datatype CBCombinerState =
    | CBCombinerIdle
    | CBCombinerReading(ghost readerState: CBReaderState)
    | CBCombinerAdvancingHead(ghost idx: nat, ghost min_tail: nat)
    | CBCombinerAdvancingTail(ghost obvserve_head: nat)
    | CBCombinerAppendState(ghost cur_idx: nat, ghost tail: nat)

  datatype CBCombinerToken = CBCombinerToken(ghost nodeId: nat, ghost rs: CBCombinerState)

  glinear method init_advance_head_state(gshared first_local_tail: CBLocalTail)
  returns (glinear state': CBAdvanceHeadState)
  requires first_local_tail.nodeId == 0
  ensures state'.idx == 1
  ensures state'.min_tail == first_local_tail.tail

  glinear method step_advance_head_state(
      gshared local_tail: CBLocalTail, glinear state: CBAdvanceHeadState)
  returns (glinear state': CBAdvanceHeadState)
  requires local_tail.nodeId == state.idx
  ensures state' == CBAdvanceHeadState(state.idx + 1,
      if state.min_tail < local_tail.tail then state.min_tail else local_tail.tail)

  glinear method finish_advance_head_state(
      glinear head: CBHead, glinear state: CBAdvanceHeadState)
  returns (glinear head': CBHead)
  requires state.idx == NUM_REPLICAS as int
  ensures head' == CBHead(state.min_tail)

  glinear method init_advance_tail_state(gshared head: CBHead)
  returns (glinear state': CBAdvanceTailState)
  ensures state'.observed_head == head.head

  glinear method finish_advance_tail(glinear state: CBAdvanceTailState, glinear tail: CBGlobalTail,
      ghost new_tail: nat, gshared contents: Contents)
  returns (glinear tail': CBGlobalTail, glinear entries': map<nat, StoredType>,
      glinear append': CBAppendState)
  requires tail.tail <= new_tail <= state.observed_head + LOG_SIZE as int
  ensures tail'.tail == new_tail
  ensures forall i | tail.tail <= i < new_tail ::
      && i in entries'
      && (i - LOG_SIZE as int) in contents.contents
      && entries'[i] == contents.contents[i - LOG_SIZE as int]
  ensures append' == CBAppendState(tail.tail, new_tail)

  glinear method append_flip_bit(
      glinear state: CBAppendState, glinear bit: CBAliveBit, glinear contents: Contents,
      glinear value: StoredType)
  returns (glinear state': CBAppendState, glinear bit': CBAliveBit, glinear contents': Contents)
  requires state.cur_idx < state.tail
  requires bit.entry == state.cur_idx % LOG_SIZE as int
  ensures state' == state.(cur_idx := state.cur_idx + 1)
  ensures bit' == bit.(bit := ((state.cur_idx / LOG_SIZE as int) % 2 == 0))
  ensures contents' == contents.(contents := contents.contents[state.cur_idx := value])

  glinear method reader_start(glinear combiner: CBCombinerToken, gshared localTail: CBLocalTail)
  returns (glinear combiner': CBCombinerToken)
  requires combiner.nodeId == localTail.nodeId
  requires combiner.rs.CBCombinerIdle?
  ensures combiner' == combiner.(rs := CBCombinerReading(CBReaderStarting(localTail.tail)))

  glinear method reader_abort(glinear combiner: CBCombinerToken)
  returns (glinear combiner': CBCombinerToken)
  requires combiner.rs.CBCombinerReading? && combiner.rs.readerState.CBReaderStarting?
  ensures combiner' == combiner.(rs := CBCombinerIdle)

  glinear method reader_enter(glinear combiner: CBCombinerToken, gshared globalTail: CBGlobalTail)
  returns (glinear combiner': CBCombinerToken)
  requires combiner.rs.CBCombinerReading? && combiner.rs.readerState.CBReaderStarting?
  ensures combiner' == combiner.(rs := CBCombinerReading(CBReaderRange(combiner.rs.readerState.start, globalTail.tail)))

  glinear method reader_guard(glinear combiner: CBCombinerToken, gshared aliveBit: CBAliveBit, ghost i: nat,
      gshared contents: Contents)
  returns (glinear combiner': CBCombinerToken)
  requires combiner.rs.CBCombinerReading? && combiner.rs.readerState.CBReaderRange?
  requires combiner.rs.readerState.start <= i < combiner.rs.readerState.end
  requires i % LOG_SIZE as int == aliveBit.entry
  requires aliveBit.bit == ((i / LOG_SIZE as int) % 2 == 0)
  ensures i in contents.contents
  ensures combiner' == combiner.(rs := CBCombinerReading(CBReaderGuard(combiner.rs.readerState.start, combiner.rs.readerState.end,
      i, contents.contents[i])))

  glinear method reader_unguard(glinear combiner: CBCombinerToken)
  returns (glinear combiner': CBCombinerToken)
  requires combiner.rs.CBCombinerReading? && combiner.rs.readerState.CBReaderGuard?
  ensures combiner' == combiner.(rs := CBCombinerReading(CBReaderRange(combiner.rs.readerState.start, combiner.rs.readerState.end)))

  glinear method reader_finish(glinear combiner: CBCombinerToken, glinear localTail: CBLocalTail)
  returns (glinear combiner': CBCombinerToken, glinear localTail': CBLocalTail)
  requires combiner.nodeId == localTail.nodeId
  requires combiner.rs.CBCombinerReading? && combiner.rs.readerState.CBReaderRange?
  ensures combiner' == combiner.(rs := CBCombinerIdle)
  ensures localTail' == localTail.(tail := combiner.rs.readerState.end)

  function method reader_borrow(gshared combiner: CBCombinerToken)
    : (gshared v: StoredType)
  requires combiner.rs.CBCombinerReading? && combiner.rs.readerState.CBReaderGuard?
  ensures v == combiner.rs.readerState.val

  glinear method cyclic_buffer_init(glinear m: map<int, StoredType>)
  returns (
    glinear head: CBHead,
    glinear globalTail: CBGlobalTail,
    glinear localTails: map<nat, CBLocalTail>,
    glinear alive: map<nat, CBAliveBit>,
    glinear contents: Contents,
    glinear readers: map<nat, CBCombinerToken>
  )
  requires forall i :: -(LOG_SIZE as int) <= i < 0 <==> i in m
  ensures head == CBHead(0)
  ensures globalTail == CBGlobalTail(0)
  ensures forall i | 0 <= i < NUM_REPLICAS as int ::
      && i in localTails && localTails[i] == CBLocalTail(i, 0)
      && i in readers && readers[i] == CBCombinerToken(i, CBCombinerIdle)
  ensures forall i | 0 <= i < LOG_SIZE as int ::
      i in alive && alive[i] == CBAliveBit(i, false)
  ensures contents == Contents(m)
}
