include "Constants.i.dfy"
include "../../lib/Lang/NativeTypes.s.dfy"
include "InfiniteLogTokens.i.dfy"
include "../framework/Cells.s.dfy"
include "../framework/MultiRw.i.dfy"
include "../framework/GlinearOption.s.dfy"
include "../../lib/Base/Option.s.dfy"


module CyclicBufferRw(nrifc: NRIfc) refines MultiRw {
  import IL = InfiniteLogSSM(nrifc)
  import opened ILT = InfiniteLogTokens(nrifc)
  import opened GlinearOption
  import opened Cells
  import opened Options
  import opened Constants

  type Key(!new) = nat

  glinear datatype StoredType = StoredType(
    glinear cellContents: CellContents<IL.LogEntry>,
    glinear logEntry: glOption<ILT.Log>
  )

  datatype ReaderState =
    | ReaderStarting(ghost start: nat)
    | ReaderRange(ghost start: nat, ghost end: nat)
    | ReaderGuard(ghost start: nat, ghost end: nat, ghost cur: nat, ghost val: StoredType)

  datatype CombinerState =
    | CombinerIdle
    | CombinerReading(ghost readerState: ReaderState)
    | CombinerAdvancingHead(ghost idx: nat, ghost min_tail: nat)
    | CombinerAdvancingTail(ghost observed_head: nat)
    | CombinerAppending(ghost cur_idx: nat, ghost tail: nat)

  // define the nodeid type
  type NodeId = nat

  // Corresponds to: pub struct Log<'a, T>
  datatype M =
    | MInvalid
    | M(
      // Logical index into the above slice at which the log starts.
      head: Option<nat>,
      // Logical index into the above slice at which the log ends.
      // New appends go here.
      tail: Option<nat>,

      // Array consisting of the local tail of each replica registered with the log.
      // Required for garbage collection; since replicas make progress over the log
      // independently, we want to make sure that we don't garbage collect operations
      // that haven't been executed by all replicas.
      localTails: map<NodeId, nat>,

      contents: map<int, StoredType>,

      // The 'alive' bit flips back and forth. So sometimes 'true' means 'alive',
      // and sometimes 'false' means 'alive'.
      // entry is an index into the buffer (0 <= entry < BUFFER_SIZE)
      aliveBits: map</* entry: */ nat, /* bit: */ bool>,

      combinerState: map<NodeId, CombinerState>
    )

  function dot(x: M, y: M) : M
  function unit() : M

  predicate Init(s: M)
  predicate Inv(x: M)
  function I(x: M) : map<Key, StoredType>

  /*
   * ============================================================================================
   * Buffer Utilities
   * ============================================================================================
   */

  function LogicalToPhysicalIndex(logical: int) : nat
  // ensures Index(-(BUFFER_SIZE as int)) == 0
  {
    logical % (BUFFER_SIZE as int)
  }

  function LogicalToAliveBitAliveWhen(logical: int) : bool
  {
    (logical / BUFFER_SIZE as int) % 2 == 0
  }

  /*
   * ============================================================================================
   * State Guards
   * ============================================================================================
   */

  predicate LocalTailValid(m: M, nodeId: NodeId)
    requires m.M?
  {
    && nodeId in m.localTails
  }

  predicate CombierIsIdle(m: M, nodeId: NodeId)
    requires m.M?
  {
    && nodeId in m.combinerState
    && m.combinerState[nodeId] == CombinerIdle
  }

  predicate CombinerKnown(m: M, nodeId: NodeId)
    requires m.M?
  {
    && nodeId in m.combinerState
  }

  predicate CombinerIsIdle(m: M, nodeId: NodeId)
    requires m.M?
    requires CombinerKnown(m, nodeId)
  {
    && m.combinerState[nodeId].CombinerIdle?
  }

  predicate CombinerIsAdvancingHead(m: M, nodeId: NodeId)
    requires m.M?
    requires CombinerKnown(m, nodeId)
  {
    && m.combinerState[nodeId].CombinerAdvancingHead?
  }

  predicate CombinerIsAdvancingHeadAt(m: M, nodeId: NodeId, idx: nat, min_tail: nat)
    requires m.M?
    requires CombinerKnown(m, nodeId)
  {
    && m.combinerState[nodeId] == CombinerAdvancingHead(idx, min_tail)
  }

  predicate CombinerIsAdvancingTail(m: M, nodeId: NodeId)
    requires m.M?
    requires CombinerKnown(m, nodeId)
  {
    && m.combinerState[nodeId].CombinerAdvancingTail?
  }

  predicate CombinerIsAdvancingTailAt(m: M, nodeId: NodeId, observed_head: nat)
    requires m.M?
    requires CombinerKnown(m, nodeId)
  {
    && m.combinerState[nodeId] == CombinerAdvancingTail(observed_head)
  }

  predicate CombinerIsAppending(m: M, nodeId: NodeId)
    requires m.M?
    requires CombinerKnown(m, nodeId)
  {
    && m.combinerState[nodeId].CombinerAppending?
  }

  predicate CombinerIsAppendingAt(m: M, nodeId: NodeId, cur_idx: nat, tail: nat)
    requires m.M?
    requires CombinerKnown(m, nodeId)
  {
    && m.combinerState[nodeId] == CombinerAppending(cur_idx, tail)
  }

  predicate CombinerIsReaderStarting(m: M, nodeId: NodeId)
    requires m.M?
    requires CombinerKnown(m, nodeId)
  {
    && m.combinerState[nodeId].CombinerReading?
    && m.combinerState[nodeId].readerState.ReaderStarting?
  }

  predicate CombinerIsReaderStartingAt(m: M, nodeId: NodeId, start: nat)
    requires m.M?
    requires CombinerKnown(m, nodeId)
  {
    && m.combinerState[nodeId] == CombinerReading(ReaderStarting(start))
  }

  predicate CombinerIsReaderRange(m: M, nodeId: NodeId)
    requires m.M?
    requires CombinerKnown(m, nodeId)
  {
    && m.combinerState[nodeId].CombinerReading?
    && m.combinerState[nodeId].readerState.ReaderRange?
  }

  predicate CombinerIsReaderRangeAt(m: M, nodeId: NodeId, start: nat, end: nat)
    requires m.M?
    requires CombinerKnown(m, nodeId)
  {
    && m.combinerState[nodeId] == CombinerReading(ReaderRange(start, end))
  }

  predicate CombinerIsReaderGuard(m: M, nodeId: NodeId)
    requires m.M?
    requires CombinerKnown(m, nodeId)
  {
    && m.combinerState[nodeId].CombinerReading?
    && m.combinerState[nodeId].readerState.ReaderGuard?
  }

  /*
   * ============================================================================================
   * Advance Head Transitions
   * ============================================================================================
   */

  predicate InitAdvanceHead(m: M, m': M, combinerNodeId: nat)
  {
    && m.M?
    && LocalTailValid(m, 0)
    && CombinerKnown(m, combinerNodeId)
    && CombinerIsIdle(m, combinerNodeId)

    && m' == m.(combinerState := m.combinerState[combinerNodeId := CombinerAdvancingHead(
      1, m.localTails[0])])
  }

  lemma InitAdvanceHead_is_transition(m: M, m': M, combinerNodeId: nat)
  requires InitAdvanceHead(m, m', combinerNodeId)
  ensures transition(m, m')
  {
    forall p: M | Inv(dot(m, p))
    ensures Inv(dot(m', p))
      && I(dot(m, p)) == I(dot(m', p))
    {
      // you can use concurrency/spsc-queue/QueueMultiRw.i.dfy as a template
      // TODO: fill this in
      assume Inv(dot(m', p));
      assume I(dot(m, p)) == I(dot(m', p));
    }
  }

  predicate StepAdvanceHead(m: M, m': M, combinerNodeId: nat)
  {
    && m.M?
    && CombinerKnown(m, combinerNodeId)
    && CombinerIsAdvancingHead(m, combinerNodeId)
    && var combinerBefore := m.combinerState[combinerNodeId];
    && LocalTailValid(m, combinerBefore.idx)

    && m' == m.(combinerState := m.combinerState[combinerNodeId := CombinerAdvancingHead(
      combinerBefore.idx + 1,
      if combinerBefore.min_tail < m.localTails[combinerBefore.idx]
        then combinerBefore.min_tail
        else m.localTails[combinerBefore.idx])])
  }

  predicate FinishAdvanceHead(m: M, m': M, combinerNodeId: nat)
  {
    && m.M?
    && CombinerKnown(m, combinerNodeId)
    && CombinerIsAdvancingHead(m, combinerNodeId)
    && var combinerBefore := m.combinerState[combinerNodeId];
    && combinerBefore.idx == (NUM_REPLICAS as nat)

    && m' == m.(
      head := Some(combinerBefore.min_tail),
      combinerState := m.combinerState[combinerNodeId := CombinerIdle]
    )
  }

  /*
   * ============================================================================================
   * Advance Tail Transitions
   * ============================================================================================
   */

  predicate InitAdvanceTail(m: M, m': M, combinerNodeId: nat)
  {
    && m.M?
    && CombinerKnown(m, combinerNodeId)
    && CombinerIsIdle(m, combinerNodeId)
    && m.head.Some?

    && m' == m.(combinerState := m.combinerState[combinerNodeId := CombinerAdvancingTail(m.head.value)])
  }

  predicate FinishAdvanceTail(m: M, m': M, combinerNodeId: nat, new_tail: nat, withdrawn: map<nat, StoredType>) // withdraw
  {
    && m.M?
    && m.tail.Some?
    && CombinerKnown(m, combinerNodeId)
    && CombinerIsAdvancingTail(m, combinerNodeId)

    && var combinerBefore := m.combinerState[combinerNodeId];
    && m.tail.value <= new_tail <= (combinerBefore.observed_head + BUFFER_SIZE as int)

    && m' == m.(combinerState := m.combinerState[combinerNodeId := CombinerAppending(m.tail.value, new_tail)])

    && (forall i | m.tail.value <= i < new_tail ::
      && i in withdrawn
      && (i - BUFFER_SIZE as int) in m.contents
      && withdrawn[i] == m.contents[i - BUFFER_SIZE as int])
  }

  /*
   * ============================================================================================
   * Append flip bit
   * ============================================================================================
   */

  predicate AppendFlipBit(m: M, m': M, combinerNodeId: nat, deposited: StoredType) // deposit
  {
    && m.M?
    && CombinerKnown(m, combinerNodeId)
    && CombinerIsAppending(m, combinerNodeId)
    && var combinerBefore := m.combinerState[combinerNodeId];
    && combinerBefore.cur_idx in m.contents

    && LogicalToPhysicalIndex(combinerBefore.cur_idx) in m.aliveBits

    && m' == m.(
      combinerState := m.combinerState[combinerNodeId := combinerBefore.(cur_idx := combinerBefore.cur_idx + 1)],
      aliveBits := m.aliveBits[LogicalToPhysicalIndex(combinerBefore.cur_idx) := (combinerBefore.cur_idx / BUFFER_SIZE as int) % 2 == 0],
      contents := m.contents[combinerBefore.cur_idx := deposited])
  }

  /*
   * ============================================================================================
   * Reader
   * ============================================================================================
   */

  predicate ReaderDoStart(m: M, m': M, combinerNodeId: nat)
  {
    && m.M?
    && CombinerKnown(m, combinerNodeId)
    && CombinerIsIdle(m, combinerNodeId)
    && combinerNodeId in m.localTails

    && m' == m.(combinerState := m.combinerState[combinerNodeId := CombinerReading(
      ReaderStarting(m.localTails[combinerNodeId]))]
    )

  }

  predicate ReaderDoEnter(m: M, m': M, combinerNodeId: nat)
  {
    && m.M?
    && CombinerKnown(m, combinerNodeId)
    && CombinerIsReaderStarting(m, combinerNodeId)
    && m.tail.Some?
    && var combinerBefore := m.combinerState[combinerNodeId];
    && var readerBefore := m.combinerState[combinerNodeId].readerState;

    && m' == m.(combinerState := m.combinerState[combinerNodeId := CombinerReading(
      ReaderRange(readerBefore.start, m.tail.value))]
    )
  }

  predicate ReaderDoGuard(m: M, m': M, combinerNodeId: nat, i: nat)
  {
    && m.M?
    && CombinerKnown(m, combinerNodeId)
    && CombinerIsReaderRange(m, combinerNodeId)
    && var combinerBefore := m.combinerState[combinerNodeId];
    && var readerBefore := m.combinerState[combinerNodeId].readerState;

    && i in m.contents
    && readerBefore.start <= i < readerBefore.end

    && LogicalToPhysicalIndex(i) in m.aliveBits
    && m.aliveBits[LogicalToPhysicalIndex(i)] == LogicalToAliveBitAliveWhen(i)

    && m' == m.(
      combinerState := m.combinerState[combinerNodeId := CombinerReading(
        ReaderGuard(readerBefore.start, readerBefore.end, i, m.contents[i]))]
      )
  }

  predicate ReaderDoUnguard(m: M, m': M, combinerNodeId: nat)
  {
    && m.M?
    && CombinerKnown(m, combinerNodeId)
    && CombinerIsReaderGuard(m, combinerNodeId)
    && var combinerBefore := m.combinerState[combinerNodeId];
    && var readerBefore := m.combinerState[combinerNodeId].readerState;

    && m' == m.(
      combinerState := m.combinerState[combinerNodeId := CombinerReading(
        ReaderRange(readerBefore.start, readerBefore.end))]
    )
  }

  predicate ReaderFinish(m: M, m': M, combinerNodeId: nat)
  {
    && m.M?

    && CombinerKnown(m, combinerNodeId)
    && CombinerIsReaderRange(m, combinerNodeId)
    && var combinerBefore := m.combinerState[combinerNodeId];
    && var readerBefore := m.combinerState[combinerNodeId].readerState;

    && combinerNodeId in m.localTails

    && m' == m.(
      combinerState := m.combinerState[combinerNodeId := CombinerIdle],
      localTails := m.localTails[combinerNodeId := readerBefore.end]
    )
  }
}
