include "../../lib/Lang/NativeTypes.s.dfy"
include "InfiniteLogTokens.i.dfy"
include "../framework/Cells.s.dfy"
include "../framework/GlinearOption.s.dfy"

module CyclicBufferTokens(nrifc: NRIfc) {
  import opened NativeTypes

  import opened IL = InfiniteLogSSM(nrifc)
  import opened ILT = InfiniteLogTokens(nrifc)
  import opened GlinearOption
  import opened Cells

  // Fixed number of replicas (in reference impl, this is variable)
  // TODO fill in reasonable constants for these
  const NUM_REPLICAS: uint64 := 4;
  const BUFFER_SIZE: uint64 := 9999;

  glinear datatype StoredType = StoredType(
    glinear cellContents: CellContents<LogEntry>,
    glinear logEntry: glOption<Log>
  )

  // TODO add 'ghost loc' to these types

  // Use 'CB' prefix to distinguish these from the corresponding state in the InfiniteLog
  // state machine.
  datatype CBHead = CBHead(head: nat)
  datatype CBLocalTail = CBLocalTail(nodeId: nat, tail: nat)
  datatype CBGlobalTail = CBGlobalTail(tail: nat)

  // The 'alive' bit flips back and forth. So sometimes 'true' means 'alive',
  // and sometimes 'false' means 'alive'.
  // entry is an index into the buffer (0 <= entry < BUFFER_SIZE)
  datatype AliveBit = AliveBit(entry: nat, bit: bool)

  // For advancing the head. We iterate idx from 0 .. NUM_REPLICAS and collect
  // the min of all tails. Then we can set head to min_tail.
  datatype AdvanceHeadState = AdvanceHeadState(idx: nat, min_tail: nat)

  // For advancing the tail and writing new log entries.
  // First read the head, then advance the tail to some value allowed by the head.
  // Then write the actual log entries.
  datatype AdvanceTailState = AdvanceTailState(observed_head: nat)
  datatype AppendState = AppendState(cur_idx: nat, tail: nat)

  // Contents stored in the log.
  //
  // `contents` maps an unbounded int to the resource protected there.
  // The user of the CyclicBuffer state machine can thus maintain an invariant
  // between the (unbounded) int and the resource.
  //
  // The way this is used is that the user, who is ready to write log-entry N,
  //    * Advances the tail, obtaining access to buffer entry N % BUFFER_SIZE
  //      which currently has entry N - BUFFER_SIZE
  //    * They overwrite that entry with log entry N
  //    * Return write-access to the CyclicBuffer protocol by setting the 'alive' bit
  //
  // Thus, for convenience, the `contents` needs to be initialized with
  // -BUFFER_SIZE, ..., -1

  datatype Contents = Contents(
    contents: map<int, StoredType>
  )

  // For reading
  // To begin reading, you can go
  //
  //      ReaderIdle --> ReaderStarting --> ReaderRange
  //
  // by reading first the localTail and the globalTail. This gives you the ability
  // to read elements from that range.
  // To actually read an element, you have to move into the guard state
  //
  //      ReaderRange --> ReaderGuard
  //
  // by checking that the 'alive' bit on that element is correct.
  // When you're done with a guard you can go back to the ReaderRange state:
  //
  //      ReaderGuard --> ReaderRange
  //
  // (This only allows a guard for a single element at once, but this is all we need
  // and makes it a bit easier to maintain a simple state.)
  // Finally when we are done we can return to the idle state
  //
  //      ReaderRange --> ReaderIdle
  //
  // by writing to the localTail.

  datatype ReaderState =
    | ReaderIdle
    | ReaderStarting(start: nat)
    | ReaderRange(start: nat, end: nat)
    | ReaderGuard(start: nat, end: nat, cur: nat, val: StoredType)

  datatype Reader = Reader(nodeId: nat, rs: ReaderState)

  glinear method init_advance_head_state(gshared first_local_tail: CBLocalTail)
  returns (glinear state': AdvanceHeadState)
  requires first_local_tail.nodeId == 0
  ensures state'.idx == 1
  ensures state'.min_tail == first_local_tail.tail

  glinear method step_advance_head_state(
      gshared local_tail: CBLocalTail, glinear state: AdvanceHeadState)
  returns (glinear state': AdvanceHeadState)
  requires local_tail.nodeId == state.idx
  ensures state' == AdvanceHeadState(state.idx + 1,
      if state.min_tail < local_tail.tail then state.min_tail else local_tail.tail)

  glinear method finish_advance_head_state(
      glinear head: CBHead, glinear state: AdvanceHeadState)
  returns (glinear head': CBHead)
  requires state.idx == NUM_REPLICAS as int
  ensures head' == CBHead(state.min_tail)

  glinear method init_advance_tail_state(gshared head: CBHead)
  returns (glinear state': AdvanceTailState)
  ensures state'.observed_head == head.head

  glinear method finish_advance_tail(glinear state: AdvanceTailState, glinear tail: CBGlobalTail,
      ghost new_tail: nat, gshared contents: Contents)
  returns (glinear tail': CBGlobalTail, glinear entries': map<nat, StoredType>,
      glinear append': AppendState)
  requires tail.tail <= new_tail <= state.observed_head + BUFFER_SIZE as int
  ensures tail'.tail == new_tail
  ensures forall i | tail.tail <= i < new_tail ::
      && i in entries'
      && (i - BUFFER_SIZE as int) in contents.contents
      && entries'[i] == contents.contents[i - BUFFER_SIZE as int]
  ensures append' == AppendState(tail.tail, new_tail)

  glinear method append_flip_bit(
      glinear state: AppendState, glinear bit: AliveBit, glinear contents: Contents,
      glinear value: StoredType)
  returns (glinear state': AppendState, glinear bit': AliveBit, glinear contents': Contents)
  requires state.cur_idx < state.tail
  requires bit.entry == state.cur_idx % BUFFER_SIZE as int
  ensures state' == state.(cur_idx := state.cur_idx + 1)
  ensures bit' == bit.(bit := ((state.cur_idx / BUFFER_SIZE as int) % 2 == 0))
  ensures contents' == contents.(contents := contents.contents[state.cur_idx := value])

  glinear method reader_start(glinear reader: Reader, gshared localTail: CBLocalTail)
  returns (glinear reader': Reader)
  requires reader.nodeId == localTail.nodeId
  requires reader.rs.ReaderIdle?
  ensures reader' == reader.(rs := ReaderStarting(localTail.tail))

  glinear method reader_enter(glinear reader: Reader, gshared globalTail: CBGlobalTail)
  returns (glinear reader': Reader)
  requires reader.rs.ReaderStarting?
  ensures reader' == reader.(rs := ReaderRange(reader.rs.start, globalTail.tail))

  glinear method reader_guard(glinear reader: Reader, gshared aliveBit: AliveBit, ghost i: nat,
      gshared contents: Contents)
  returns (glinear reader': Reader)
  requires reader.rs.ReaderRange?
  requires reader.rs.start <= i < reader.rs.end
  requires i % BUFFER_SIZE as int == aliveBit.entry
  requires aliveBit.bit == ((i / BUFFER_SIZE as int) % 2 == 0)
  ensures i in contents.contents
  ensures reader' == reader.(rs := ReaderGuard(reader.rs.start, reader.rs.end,
      i, contents.contents[i]))

  glinear method reader_unguard(glinear reader: Reader)
  returns (glinear reader': Reader)
  requires reader.rs.ReaderGuard?
  ensures reader' == reader.(rs := ReaderRange(reader.rs.start, reader.rs.end))

  glinear method reader_finish(glinear reader: Reader, glinear localTail: CBLocalTail)
  returns (glinear reader': Reader, glinear localTail': CBLocalTail)
  requires reader.nodeId == localTail.nodeId
  requires reader.rs.ReaderRange?
  ensures reader' == reader.(rs := ReaderIdle)
  ensures localTail' == localTail.(tail := reader.rs.end)
}
