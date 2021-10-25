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
      ghost head: Option<nat>,
      // Logical index into the above slice at which the log ends.
      // New appends go here.
      ghost tail: Option<nat>,

      // Array consisting of the local tail of each replica registered with the log.
      // Required for garbage collection; since replicas make progress over the log
      // independently, we want to make sure that we don't garbage collect operations
      // that haven't been executed by all replicas.
      ghost localTails: map<NodeId, nat>,

      ghost contents: map<int, StoredType>,

      // The 'alive' bit flips back and forth. So sometimes 'true' means 'alive',
      // and sometimes 'false' means 'alive'.
      // entry is an index into the buffer (0 <= entry < BUFFER_SIZE)
      ghost aliveBits: map</* entry: */ nat, /* bit: */ bool>,

      ghost combinerState: map<NodeId, CombinerState>
    )

 /*
   * ============================================================================================
   * Map/Seq Utilities
   * ============================================================================================
   */

  // XXX: can we have a single one of these, and reuse that thorugh imports???

  // updates map m1 with map m2, where all values of m2 aree added to m1, and existing values updated
  // see: https://stackoverflow.com/questions/52610402/updating-a-map-with-another-map-in-dafny
  function {:opaque} map_update<K(!new), V>(m1: map<K, V>, m2: map<K, V>): map<K, V>
    ensures forall k :: k in m1 || k in m2 ==> k in map_update(m1, m2)
    ensures forall k :: k in m2 ==> map_update(m1, m2)[k] == m2[k]
    ensures forall k :: !(k in m2) && k in m1 ==> map_update(m1, m2)[k] == m1[k]
    ensures forall k :: !(k in m2) && !(k in m1) ==> !(k in map_update(m1, m2))
    ensures m1 == map[] ==> map_update(m1, m2) == m2
    ensures m2 == map[] ==> map_update(m1, m2) == m1
    ensures (m1.Keys !! m2.Keys) ==> map_update(m1, m2).Keys == m1.Keys + m2.Keys
    ensures (m1.Keys !! m2.Keys) ==> (forall k | k in m1 :: map_update(m1, m2)[k] == m1[k])
    ensures (m1.Keys !! m2.Keys) ==> (forall k | k in m2 :: map_update(m1, m2)[k] == m2[k])
  {
    map k | k in (m1.Keys + m2.Keys) :: if k in m2 then m2[k] else m1[k]
  }


  function MinLocalTail(ltails: map<NodeId, nat>) : (m : nat)
    ensures forall i | i in ltails :: m <= ltails[i]


  /*
   * ============================================================================================
   * Invariant
   * ============================================================================================
   */

  predicate Complete(x: M)
  {
    && x.M?
    && x.head.Some?
    && x.tail.Some?
    && (forall i: nat :: i < NUM_REPLICAS as nat <==> i in x.localTails)
    && (true /* contents */)
    && (forall i: nat :: i < BUFFER_SIZE as nat <==> i in x.aliveBits)
    && (forall i: nat :: i < NUM_REPLICAS as nat <==> i in x.combinerState)
  }

  predicate PointerOrdering(x: M)
    requires Complete(x)
  {
    // the head must be smaller or equal to the tail,
    && x.head.value <= x.tail.value
    // all local tails must be between thea
    && (forall i | i in x.localTails :: x.head.value <= x.localTails[i] <= x.tail.value)
  }

  predicate PointerDifferences(x:M)
    requires Complete(x) && PointerOrdering(x)
  {
    // the span of the entries between head and tail should never be larger than the buffer size
    && (x.tail.value - x.head.value < BUFFER_SIZE as nat)
    && (forall i | i in x.localTails ::  x.tail.value - x.localTails[i] < BUFFER_SIZE as nat)
  }

  predicate AliveBits(x: M)
    requires Complete(x)
  {
    // everything from the current head up to the tail is not alive.
    // forall i | i in SetOfFreeBufferEntries(x.head.value, x.tail.value) :: !EntryIsAlive(x.aliveBits, i)
    && true
  }

  predicate BufferContents(x: M)
    requires Complete(x)
  {
    // the contents of
    && true
  }


  predicate ReaderStateValid(x: M)
    requires Complete(x)
  {
    forall n | n in x.combinerState && x.combinerState[n].CombinerReading?
      :: match  x.combinerState[n].readerState {
        case ReaderStarting(start: nat) => (
          // the starting value should match the local tail
          && start == x.localTails[n]
        )
        case ReaderRange(start: nat, end: nat) => (
          // the start value may have advanced.
          // note the entry at curr
          && x.localTails[n] <= start
          && x.localTails[n] == start
          && start <= end
          && end <= x.tail.value
        )
        case ReaderGuard(start: nat, end: nat, cur: nat, val: StoredType) => (
          // we start reading at our local tail
          && x.localTails[n] <= start
          && x.localTails[n] == start
          && start <= end
          // end can't be past the tail value
          && end <= x.tail.value
          // current is between start and end
          && start <= cur <= end
          // the entry that we read must be alive
          && EntryIsAlive(x.aliveBits, cur)
          // the thing we are ready should match the log content
          // XXX: is that actually true
          && cur in x.contents && x.contents[cur] == val
        )
    }
  }

  predicate CombinerStateValid(x: M)
    requires Complete(x)
    requires PointerOrdering(x)
  {
    forall n | n in x.combinerState
      :: match x.combinerState[n] {
        case CombinerIdle => (true)        // nothing to do
        case CombinerReading(_) => (true)  // handled in ReaderState
        case CombinerAdvancingHead(idx: nat, min_tail: nat) => (
          // the index is always within the defined replicas
          && idx <= NUM_REPLICAS as nat
          // forall replicas we'e seen, min_tail is smaller than all localTails
          && (forall n | 0 <= n < idx :: min_tail <= x.localTails[n])
        )
        case CombinerAdvancingTail(observed_head: nat) => (
          // the observed head is smaller than all local tails
          && (forall n | 0 <= n < NUM_REPLICAS as nat :: observed_head <= x.localTails[n])
        )
        case CombinerAppending(cur_idx: nat, tail: nat) => (
          // the current index is between local tails and tail.
          && x.localTails[n] <= cur_idx < tail
          // the read tail is smaller or equal to the current tail.
          && tail <= x.tail.value
          // the entry we are writing mus not be alive
          && !(EntryIsAlive(x.aliveBits, cur_idx))
        )
      }
  }

  predicate Inv(x: M)
  {
    && Complete(x)
    && PointerOrdering(x)
    && PointerDifferences(x)
    && AliveBits(x)
    && BufferContents(x)
    && CombinerStateValid(x)
    && ReaderStateValid(x)
  }

  /*
   * ============================================================================================
   * Init State
   * ============================================================================================
   */

  predicate Init(s: M) {
    && s.M?
    && s.head == Some(0)
    && s.tail == Some(0)
    && (forall i: nat :: i < NUM_REPLICAS as nat <==> i in s.localTails)
    && (forall i | i in s.localTails :: s.localTails[i] == 0)
    && (forall i: nat :: i < NUM_REPLICAS as nat <==> i in s.combinerState)
    && (forall i | i in s.combinerState :: s.combinerState[i].CombinerIdle?)
    && (forall i: nat :: i < BUFFER_SIZE as nat <==> i in s.aliveBits)
    && (forall i: int :: -(BUFFER_SIZE as int) <= i < -1 <==> i in s.contents)
  }

  lemma InitImpliesInv(x: M)
  //requires Init(s)
  ensures Inv(x)
  {

  }

  /*
   * ============================================================================================
   * Interpretation Function
   * ============================================================================================
   */

  function I(x: M) : map<Key, StoredType>
  {
    // TODO: Figure out something here...
    map i | x.head.value <= i < x.tail.value && i in x.contents
      :: i := x.contents[i]
  }
  // TODO: checked out between the latest alive cell and the tail

  /*
   * ============================================================================================
   * Dot
   * ============================================================================================
   */

  function dot(x: M, y: M) : M {
    if (
      && x.M?                  && y.M?
      && !(x.head.Some?        && y.head.Some?)
      && !(x.tail.Some?        && y.tail.Some?)
      && (x.localTails.Keys    !! y.localTails.Keys)
      && (x.contents.Keys      !! y.contents.Keys)
      && (x.aliveBits.Keys     !! y.aliveBits.Keys)
      && (x.combinerState.Keys !! y.combinerState.Keys)
    )
    then
      M(
        if x.head.Some? then x.head else y.head,
        if x.tail.Some? then x.tail else y.tail,
        map_update(x.localTails, y.localTails),
        map_update(x.contents, y.contents),
        map_update(x.aliveBits, y.aliveBits),
        map_update(x.combinerState, y.combinerState)
      )
    else
      MInvalid
  }

  function unit() : M {
    M(None, None, map[], map[], map[], map[])
  }

  lemma dot_unit(x: M)
  ensures dot(x, unit()) == x
  {
    assert unit().M?;
    assert dot(unit(), unit()).M?;
    assert dot(unit(), unit()) == unit();
    assert dot(x, unit()) == x;
  }

  lemma commutative(x: M, y: M)
  ensures dot(x, y) == dot(y, x)
  {
    if dot(x, y) == MInvalid {
      assert dot(x, y) == dot(y, x);
    } else {
      assert dot(x, y) == dot(y, x);
    }
  }

  lemma associative(x: M, y: M, z: M)
  ensures dot(x, dot(y, z)) == dot(dot(x, y), z)
  {
    if dot(x, dot(y, z)) == MInvalid {
      assert dot(x, dot(y, z)) == dot(dot(x, y), z);
    } else {
      assert dot(x, dot(y, z)) == dot(dot(x, y), z);
    }
  }


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

  function SetOfBufferEntries() : set<nat>
  {
    set x | 0 <= x < BUFFER_SIZE as nat :: x
  }

  function SetOfFreeBufferEntries(logical_head: int, logital_tail: int) : set<nat>
    requires logical_head <= logital_tail
    requires ((logital_tail -logical_head) < BUFFER_SIZE as nat)
  {
    SetOfBufferEntries() - SetOfReservedBufferEntries(logical_head, logital_tail)
  }

  function SetOfReservedBufferEntries(logical_head: int, logital_tail: int) : set<nat>
    requires logical_head <= logital_tail
    requires ((logital_tail -logical_head) < BUFFER_SIZE as nat)
  {
    set x | logical_head <= x < logital_tail :: LogicalToPhysicalIndex(x)
  }


  function LogicalToAliveBitAliveWhen(logical: int) : bool
  {
    (logical / BUFFER_SIZE as int) % 2 == 0
  }

  predicate EntryIsAlive(aliveBits: map</* entry: */ nat, /* bit: */ bool>, logical: int)
  {
    && var physID := LogicalToPhysicalIndex(logical);
    && physID in aliveBits
    && aliveBits[physID] == LogicalToAliveBitAliveWhen(logical)
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
      assert Inv(dot(m', p));
      assert I(dot(m, p)) == I(dot(m', p));
    }
  }

  /* ----------------------------------------------------------------------------------------- */

  predicate StepAdvanceHead(m: M, m': M, combinerNodeId: nat)
  {
    && m.M?
    && CombinerKnown(m, combinerNodeId)
    && CombinerIsAdvancingHead(m, combinerNodeId)
    && var combinerBefore := m.combinerState[combinerNodeId];
    && LocalTailValid(m, combinerBefore.idx)

    && var new_min_tail :=  if combinerBefore.min_tail < m.localTails[combinerBefore.idx]
                            then combinerBefore.min_tail
                            else m.localTails[combinerBefore.idx];

    && m' == m.(combinerState := m.combinerState[combinerNodeId := CombinerAdvancingHead(combinerBefore.idx + 1, new_min_tail)])
  }

  lemma StepAdvanceHead_is_transition(m: M, m': M, combinerNodeId: nat)
  requires StepAdvanceHead(m, m', combinerNodeId)
  ensures transition(m, m')
  {
    forall p: M | Inv(dot(m, p))
    ensures Inv(dot(m', p))
      && I(dot(m, p)) == I(dot(m', p))
    {
      assert Inv(dot(m', p));
      assert I(dot(m, p)) == I(dot(m', p));
    }
  }

  /* ----------------------------------------------------------------------------------------- */

  predicate FinishAdvanceHead(m: M, m': M, combinerNodeId: nat)
  {
    && m.M?
    && CombinerKnown(m, combinerNodeId)
    && CombinerIsAdvancingHead(m, combinerNodeId)
    && var combinerBefore := m.combinerState[combinerNodeId];
    && combinerBefore.idx == (NUM_REPLICAS as nat)

    && m.head.Some? // need this

    && m' == m.(
      head := Some(combinerBefore.min_tail),
      combinerState := m.combinerState[combinerNodeId := CombinerIdle]
    )
  }

  lemma FinishAdvanceHead_is_transition(m: M, m': M, combinerNodeId: nat)
  requires FinishAdvanceHead(m, m', combinerNodeId)
  ensures transition(m, m')
  {
    forall p: M | Inv(dot(m, p))
    ensures Inv(dot(m', p))
      && I(dot(m, p)) == I(dot(m', p))
    {
      assume Inv(dot(m', p));
      assume I(dot(m, p)) == I(dot(m', p));
    }
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

  lemma InitAdvanceTail_is_transition(m: M, m': M, combinerNodeId: nat)
  requires InitAdvanceTail(m, m', combinerNodeId)
  ensures transition(m, m')
  {
    forall p: M | Inv(dot(m, p))
    ensures Inv(dot(m', p))
      && I(dot(m, p)) == I(dot(m', p))
    {
      // TODO: fill this in
      assert Inv(dot(m', p));
      assert I(dot(m, p)) == I(dot(m', p));
    }
  }

  /* ----------------------------------------------------------------------------------------- */

  // TODO: the withdrawn type here may be wrong
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

  // TODO: lemma FinishAdvanceTail_is_withdraw(m: M, m': M, combinerNodeId: nat, new_tail: nat, withdrawn: map<nat, StoredType>)
  // TODO: requires FinishAdvanceTail(m, m', combinerNodeId)
  // TODO: ensures withdraw(m, m', new_tail, withdrawn)
  // TODO: {
  // TODO:   forall p: M | Inv(dot(m, p))
  // TODO:   ensures Inv(dot(m', p))
  // TODO:     && ...
  // TODO:   {
  // TODO:     // TODO: fill this in
  // TODO:     assume Inv(dot(m', p));
  // TODO:   }
  // TODO: }

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

  lemma AppendFlipBit_is_deposit(m: M, m': M, combinerNodeId: nat, deposited: StoredType)
  requires AppendFlipBit(m, m', combinerNodeId, deposited)
  ensures exists key :: deposit(m, m', key, deposited)
  {
    var key := *; // TODO

    forall p: M | Inv(dot(m, p))
    ensures Inv(dot(m', p))
      && key !in I(dot(m, p))
      && I(dot(m', p)) == I(dot(m, p))[key := deposited]
    {
      // TODO: fill this in
      assert Inv(dot(m', p));
      assume key !in I(dot(m, p));
      assume I(dot(m', p)) == I(dot(m, p))[key := deposited];
    }

    assert deposit(m, m', key, deposited); // witness
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

  lemma ReaderDoStart_is_transition(m: M, m': M, combinerNodeId: nat)
  requires ReaderDoStart(m, m', combinerNodeId)
  ensures transition(m, m')
  {
    forall p: M | Inv(dot(m, p))
    ensures Inv(dot(m', p))
      && I(dot(m, p)) == I(dot(m', p))
    {
      assert Inv(dot(m', p));
      assert I(dot(m, p)) == I(dot(m', p));
    }
  }

/* ----------------------------------------------------------------------------------------- */

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

  lemma ReaderDoEnter_is_transition(m: M, m': M, combinerNodeId: nat)
  requires ReaderDoEnter(m, m', combinerNodeId)
  ensures transition(m, m')
  {
    forall p: M | Inv(dot(m, p))
    ensures Inv(dot(m', p))
      && I(dot(m, p)) == I(dot(m', p))
    {
      assert Inv(dot(m', p));
      assert I(dot(m, p)) == I(dot(m', p));
    }
  }

/* ----------------------------------------------------------------------------------------- */

  predicate ReaderDoGuard(m: M, m': M, combinerNodeId: nat, i: nat)
  {
    && m.M?
    && CombinerKnown(m, combinerNodeId)
    && CombinerIsReaderRange(m, combinerNodeId)
    && var combinerBefore := m.combinerState[combinerNodeId];
    && var readerBefore := m.combinerState[combinerNodeId].readerState;

    && i in m.contents
    && readerBefore.start <= i < readerBefore.end

    && EntryIsAlive( m.aliveBits, i)

    && m' == m.(
      combinerState := m.combinerState[combinerNodeId := CombinerReading(
        ReaderGuard(readerBefore.start, readerBefore.end, i, m.contents[i]))]
      )
  }

  lemma ReaderDoGuard_is_transition(m: M, m': M, combinerNodeId: nat, i: nat)
  requires ReaderDoGuard(m, m', combinerNodeId, i)
  ensures transition(m, m')
  {
    forall p: M | Inv(dot(m, p))
    ensures Inv(dot(m', p))
      && I(dot(m, p)) == I(dot(m', p))
    {
      assert Inv(dot(m', p));
      assert I(dot(m, p)) == I(dot(m', p));
    }
  }

  /* ----------------------------------------------------------------------------------------- */

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

  lemma ReaderDoUnguard_is_transition(m: M, m': M, combinerNodeId: nat)
  requires ReaderDoUnguard(m, m', combinerNodeId)
  ensures transition(m, m')
  {
    forall p: M | Inv(dot(m, p))
    ensures Inv(dot(m', p))
      && I(dot(m, p)) == I(dot(m', p))
    {
      assert Inv(dot(m', p));
      assert I(dot(m, p)) == I(dot(m', p));
    }
  }

  /* ----------------------------------------------------------------------------------------- */

  predicate ReaderDoFinish(m: M, m': M, combinerNodeId: nat)
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

  lemma ReaderDoFinish_is_transition(m: M, m': M, combinerNodeId: nat)
  requires ReaderDoFinish(m, m', combinerNodeId)
  ensures transition(m, m')
  {
    forall p: M | Inv(dot(m, p))
    ensures Inv(dot(m', p))
      && I(dot(m, p)) == I(dot(m', p))
    {
      assert Inv(dot(m', p));
      assert I(dot(m, p)) == I(dot(m', p));
    }
  }
}
