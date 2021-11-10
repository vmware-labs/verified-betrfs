include "Constants.i.dfy"
include "../../lib/Lang/NativeTypes.s.dfy"
include "InfiniteLogTokens.i.dfy"
include "../framework/Cells.s.dfy"
include "../framework/MultiRw.i.dfy"
include "../framework/GlinearOption.s.dfy"
include "../../lib/Base/Option.s.dfy"
include "../../lib/Base/Maps.i.dfy"


module CyclicBufferRw(nrifc: NRIfc) refines MultiRw {
  import IL = InfiniteLogSSM(nrifc)
  import opened ILT = InfiniteLogTokens(nrifc)
  import opened GlinearOption
  import opened Cells
  import opened Options
  import opened Constants
  import Maps

  type Key(!new) = nat

  glinear datatype StoredType = StoredType(
    glinear cellContents: CellContents<IL.LogEntry>,
    glinear logEntry: glOption<ILT.Log>
  )

  datatype ReaderState =
    | ReaderStarting(ghost start: nat)
    | ReaderRange(ghost start: nat, ghost end: nat, ghost cur: nat)
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
      // NOTE: the tail _does not_ monotonically advances. It's only guaranteed to be <= all the local tails.
      ghost head: Option<nat>,
      // Logical index into the above slice at which the log ends.
      // New appends go here.
      ghost tail: Option<nat>,

      // Array consisting of the local tail of each replica registered with the log.
      // Required for garbage collection; since replicas make progress over the log
      // independently, we want to make sure that we don't garbage collect operations
      // that haven't been executed by all replicas.
      ghost localTails: map<NodeId, nat>,

      ghost contents: map<int, Option<StoredType>>,

      // The 'alive' bit flips back and forth. So sometimes 'true' means 'alive',
      // and sometimes 'false' means 'alive'.
      // entry is an index into the buffer (0 <= entry < LOG_SIZE)
      ghost aliveBits: map</* entry: */ nat, /* bit: */ bool>,

      ghost combinerState: map<NodeId, CombinerState>
    )

 /*
   * ============================================================================================
   * Map/Seq Utilities
   * ============================================================================================
   */

  function min(a: nat, b: nat) : nat {
    if a < b then a
    else b
  }

  function {:induction true}  MinLocalTailRec(ltails: map<NodeId, nat>, idx: nat) : (m : nat)
    requires idx < NUM_REPLICAS as nat
    requires forall i:nat :: i < NUM_REPLICAS as nat <==> i in ltails
    ensures forall i : nat | i <= idx ::  m <= ltails[i]
    ensures exists i | 0 <= i <= idx :: ltails[i] == m
    decreases idx
  {
    if idx == 0 then
      ltails[0]
    else
      min(ltails[idx], MinLocalTailRec(ltails, idx - 1))
  }


  function MinLocalTail(ltails: map<NodeId, nat>) : (m : nat)
    requires forall i:nat :: i < NUM_REPLICAS as nat <==> i in ltails
    ensures forall i | i in ltails :: m <= ltails[i]
    ensures exists i | 0 <= i < NUM_REPLICAS as nat :: ltails[i] == m
    ensures m in ltails.Values
  {
    MinLocalTailRec(ltails, NUM_REPLICAS as nat - 1)
  }

  function max(a: nat, b: nat) : nat {
    if a > b then a
    else b
  }

  function {:induction true} MaxLocalTailRec(ltails: map<NodeId, nat>, idx: nat) : (m : nat)
    requires idx < NUM_REPLICAS as nat
    requires forall i:nat :: i < NUM_REPLICAS as nat <==> i in ltails
    ensures forall i : nat | i <= idx ::  m >= ltails[i]
    ensures exists i | 0 <= i <= idx :: ltails[i] == m
    decreases idx
  {
    if idx == 0 then
      ltails[0]
    else
      max(ltails[idx], MaxLocalTailRec(ltails, idx - 1))
  }

  function MaxLocalTail(ltails: map<NodeId, nat>) : (m : nat)
    requires forall i:nat :: i < NUM_REPLICAS as nat <==> i in ltails
    ensures forall i | i in ltails :: m >= ltails[i]
    ensures exists i | 0 <= i < NUM_REPLICAS as nat :: ltails[i] == m
    ensures m in ltails.Values
  {
    MaxLocalTailRec(ltails, NUM_REPLICAS as nat - 1)
  }

  /*
   * ============================================================================================
   * Invariant
   * ============================================================================================
   */

  predicate {:opaque} Complete(x: M)
  ensures Complete(x) ==> (
    && x.M?
    && x.head.Some?
    && x.tail.Some?
  )
  {
    && x.M?
    && x.head.Some?
    && x.tail.Some?
    && (forall i: nat :: i < NUM_REPLICAS as nat <==> i in x.localTails)
    && (forall i : int :: (x.tail.value - (LOG_SIZE as nat) <= i < x.tail.value) <==> i in x.contents)
    && (forall i: nat :: i < LOG_SIZE as nat <==> i in x.aliveBits)
    && (forall i: nat :: LogicalToPhysicalIndex(i) in x.aliveBits)
    && (forall i: nat :: i < NUM_REPLICAS as nat <==> i in x.combinerState)
  }

  predicate PointerOrdering(x: M)
    requires Complete(x)
    ensures (reveal_Complete(); PointerOrdering(x) ==> (x.head.value <= MinLocalTail(x.localTails) <= x.tail.value))
  {
    reveal_Complete();

    // the head must be smaller or equal to the tail,
    && x.head.value <= x.tail.value
    // all local tails must be between the head and the tail
    && (forall i | i in x.localTails :: x.head.value <= x.localTails[i] <= x.tail.value)
    // all local tails are between the valid buffer range
    && (forall i | i in x.localTails ::  x.tail.value - (LOG_SIZE as nat) <=  x.localTails[i] <= x.tail.value)
  }

  predicate PointerDifferences(x:M)
    requires Complete(x) && PointerOrdering(x)
  {
    // the span of the entries between local tails and tail should never be larger than the buffer size
    && (forall i | i in x.localTails ::  x.tail.value - x.localTails[i] < LOG_SIZE as nat)
  }

  predicate AliveBits(x: M)
    requires Complete(x)
    requires PointerOrdering(x)
    requires PointerDifferences(x)
  {
    // forall free buffer entries, the entry is not alive.
    && (forall i | i in SetOfFreeBufferEntries(MinLocalTail(x.localTails), x.tail.value) :: !EntryIsAlive(x.aliveBits, i))
  }

  predicate BufferContents(x: M)
    requires Complete(x)
  {
    reveal_Complete();

    forall i : int | x.tail.value - (LOG_SIZE as nat) <= i < x.tail.value ::
      (EntryIsAlive(x.aliveBits, i) || i < MinLocalTail(x.localTails)) <==> x.contents[i].Some?
  }

  predicate ReaderStateValid(x: M)
    requires Complete(x)
    requires PointerOrdering(x)
  {
    forall n | n in x.combinerState && x.combinerState[n].CombinerReading?
      :: match  x.combinerState[n].readerState {
        case ReaderStarting(start: nat) => (
          // the starting value should match the local tail
          && start == x.localTails[n]
        )
        case ReaderRange(start: nat, end: nat, cur: nat) => (
          // the start must be our local tail
          && x.localTails[n] == start
          // the start must be before the end, can be equial if ltail == gtail
          && start <= end
          // we've read the tail, but the tail may have moved
          && x.tail.value - (LOG_SIZE as nat) <= end <= x.tail.value
          // current is between start and end
          && start <= cur <= end
          // the entries up to, and including  current must be alive
          && (forall i | start <= i < cur :: EntryIsAlive(x.aliveBits, i))
          // the entries up to, and including current must have something in the log
          && (forall i | start <= i < cur :: x.contents[i].Some?)
        )
        case ReaderGuard(start: nat, end: nat, cur: nat, val: StoredType) => (
          // the start must be our local tail
          && x.localTails[n] == start
          // the start must be before the end, can be equial if ltail == gtail
          && start <= end
          // we've read the tail, but the tail may have moved
          && x.tail.value - (LOG_SIZE as nat) <= end <= x.tail.value
          // current is between start and end
          && start <= cur < end
          // the entries up to, and including  current must be alive
          && (forall i | start <= i <= cur :: EntryIsAlive(x.aliveBits, i))
          // the entries up to, and including current must have something in the log
          && (forall i | start <= i <= cur :: x.contents[i].Some?)
          // the thing we are ready should match the log content
          && x.contents[cur] == Some(val)
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
          && x.localTails[n] <= cur_idx <= tail
          // the read tail is smaller or equal to the current tail.
          && tail <= x.tail.value
          //
          // && x.tail.value - (LOG_SIZE as nat) <= cur_idx <= x.tail.value
          // all the entries we're writing must not be alive.
          && (forall i : nat | cur_idx <= i < tail :: !(EntryIsAlive(x.aliveBits, i)))
          // all the entries we're writing must not be SOme
          // && (forall i | cur_idx <= i < tail :: m.contents[i].Some?)
        )
      }
  }

  // function ReaderLogicalRange(c: CombinerState) : set<nat>
  // {
  //    match c {
  //     case CombinerIdle => {}
  //     case CombinerReading(readerState: ReaderState) => (
  //       match readerState {
  //         case ReaderStarting(_) => {}
  //         case ReaderRange(start: nat, end: nat, _) => {} // not really accessing yet
  //         case ReaderGuard(start: nat, end: nat, cur: nat , _) => (
  //           {cur} // we only access this one.
  //         )
  //       }
  //     )
  //     case CombinerAdvancingHead(idx: nat, min_tail: nat) => {}
  //     case CombinerAdvancingTail(observed_head: nat) => {}
  //     case CombinerAppending(cur_idx: nat, tail: nat) => {}
  //   }
  // }

  // function CombinerLogicalRange(c: CombinerState) : set<nat>
  // {
  //   match c {
  //     case CombinerIdle => {}
  //     case CombinerReading(readerState: ReaderState) => {}
  //     case CombinerAdvancingHead(idx: nat, min_tail: nat) => {}
  //     case CombinerAdvancingTail(observed_head: nat) => {}
  //     case CombinerAppending(cur_idx: nat, tail: nat) => (
  //       set i : nat | cur_idx <= i < tail :: i
  //     )
  //   }
  // }

  // predicate LogicalRangesNoOverlap(x: M)
  //   requires Complete(x)
  // {
  //   reveal_Complete();

  //   forall i, j | 0 <= i < NUM_REPLICAS as nat && 0 <= j < NUM_REPLICAS as nat && i != j ::
  //     && (CombinerLogicalRange(x.combinerState[i]) !! CombinerLogicalRange(x.combinerState[j]))
  //     && (CombinerLogicalRange(x.combinerState[i]) !! ReaderLogicalRange(x.combinerState[j]))
  // }

  predicate {:opaque} RangesNoOverlap(x: M)
    requires Complete(x)
  {
    assert (forall i: nat :: i < NUM_REPLICAS as nat <==> i in x.combinerState) by {
      reveal_Complete();
    }

    && (forall i, j | 0 <= i < NUM_REPLICAS as nat && 0 <= j < NUM_REPLICAS as nat && i != j
      && x.combinerState[i].CombinerAppending? && x.combinerState[j].CombinerAppending?
    :: (
      || x.combinerState[i].cur_idx >= x.combinerState[j].tail
      || x.combinerState[i].tail <= x.combinerState[j].cur_idx
    ))

    && (forall i, j | 0 <= i < NUM_REPLICAS as nat && 0 <= j < NUM_REPLICAS as nat && i != j
      && x.combinerState[i].CombinerAppending? && x.combinerState[j].CombinerReading? && x.combinerState[j].readerState.ReaderGuard?
    :: (
      || x.combinerState[i].cur_idx > x.combinerState[j].readerState.cur
      || x.combinerState[i].tail <=  x.combinerState[j].readerState.cur
    ))
  }

  predicate Inv(x: M)
  {
    && Complete(x)
    && PointerOrdering(x)
    && PointerDifferences(x)
    && RangesNoOverlap(x)
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
    && (forall i: nat :: i < LOG_SIZE as nat <==> i in s.aliveBits)
    && (forall i: int | 0 <= i < LOG_SIZE as nat :: s.aliveBits[i] == LogicalToAliveBitAliveWhen(i - LOG_SIZE as nat))
    && (forall i: int :: -(LOG_SIZE as int) <= i < 0 <==> (i in s.contents))
    && (forall i: int :: -(LOG_SIZE as int) <= i < 0 <==> (i in s.contents && s.contents[i].Some?))
  }

  lemma InitImpliesInv(x: M)
  // requires Init(x)
  ensures Inv(x)
  {
    assert Complete(x) by { reveal_Complete(); }
    assert PointerOrdering(x);
    assert PointerDifferences(x);
    assert RangesNoOverlap(x) by { reveal_RangesNoOverlap(); }
    assert AliveBits(x);
    assert BufferContents(x);
    assert CombinerStateValid(x);
    assert ReaderStateValid(x);
  }

  /*
   * ============================================================================================
   * Interpretation Function
   * ============================================================================================
   */

  function I(x: M) : map<Key, StoredType>
  {
    // Withdrawn: non-alive cells between head and tail
    map i : nat | i in x.contents.Keys && x.contents[i].Some? :: x.contents[i].value
  }

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
        Maps.MapUnionPreferB(x.localTails, y.localTails),
        Maps.MapUnionPreferB(x.contents, y.contents),
        Maps.MapUnionPreferB(x.aliveBits, y.aliveBits),
        Maps.MapUnionPreferB(x.combinerState, y.combinerState)
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
  // ensures Index(-(LOG_SIZE as int)) == 0
  {
    logical % (LOG_SIZE as int)
  }

  lemma AllInAliveBits(aliveBits: map</* entry: */ nat, /* bit: */ bool>)
    requires forall i: nat :: i < LOG_SIZE as nat <==> i in aliveBits
    ensures forall i: nat :: LogicalToPhysicalIndex(i) in aliveBits
  {

  }

  // the set of current buffer entries.
  function SetOfBufferEntries(min_ltails: int) : (r : set<int>)
    ensures forall i :: min_ltails <= i < min_ltails + (LOG_SIZE as nat) <==> i in r
  {
    set x : int | min_ltails <= x < min_ltails + (LOG_SIZE as nat)
  }

  // the set of free buffer entries
  function SetOfFreeBufferEntries(min_ltails: int, logical_tail: int) : (r : set<int>)
    requires min_ltails <= logical_tail
    requires logical_tail - (LOG_SIZE as int) <= min_ltails <= logical_tail
    requires ((logical_tail - min_ltails) < LOG_SIZE as nat)
    ensures forall i :: logical_tail <= i < min_ltails + (LOG_SIZE as nat) <==> i in r
  {
    SetOfBufferEntries(min_ltails) - SetOfActiveBufferEntries(min_ltails, logical_tail)
  }

  // the set of active buffer entries is everything between
  function SetOfActiveBufferEntries(min_ltails: int, logical_tail: int) : (r : set<int>)
    requires min_ltails <= logical_tail
    requires logical_tail - (LOG_SIZE as int) <= min_ltails <= logical_tail
    requires ((logical_tail - min_ltails) < LOG_SIZE as nat)
    ensures forall i :: min_ltails <= i < logical_tail <==> i in r
  {
    set x : int | min_ltails <= x < logical_tail :: x
  }

  lemma BufferUnion(ltails: int, tail: int)
    requires ltails <= tail
    requires tail - (LOG_SIZE as int) <= ltails <= tail
    requires ((tail - ltails) < LOG_SIZE as int)
    ensures SetOfActiveBufferEntries(ltails, tail) + SetOfFreeBufferEntries(ltails, tail) == SetOfBufferEntries(ltails)
  {

  }

  function LogicalToAliveBitAliveWhen(logical: int) : bool
  {
    ((logical / LOG_SIZE as int) % 2) == 0
  }


  predicate EntryIsAlive(aliveBits: map</* entry: */ nat, /* bit: */ bool>, logical: int)
    requires LogicalToPhysicalIndex(logical) in aliveBits
  {
    && var physID := LogicalToPhysicalIndex(logical);
    && aliveBits[physID] == LogicalToAliveBitAliveWhen(logical)
  }


  lemma EntryIsAliveWrapAround(aliveBits: map</* entry: */ nat, /* bit: */ bool>, low: nat, high: nat)
    requires forall i: nat :: i < LOG_SIZE as nat <==> i in aliveBits
    requires low <= high < low +  (LOG_SIZE as int)
    ensures forall i | low <= i < high ::
      EntryIsAlive(aliveBits, i) == !EntryIsAlive(aliveBits, i + (LOG_SIZE as int))
  {

  }

  lemma EntryIsAliveWrapAroundReformat(aliveBits: map</* entry: */ nat, /* bit: */ bool>, low: nat, high: nat)
    requires forall i: nat :: i < LOG_SIZE as nat <==> i in aliveBits
    requires low <= high < low +  (LOG_SIZE as nat)
    requires forall i : nat | low <= i < high :: !EntryIsAlive(aliveBits, i + (LOG_SIZE as nat))
    ensures forall i : nat | low + (LOG_SIZE as nat) <= i < high  + (LOG_SIZE as nat) :: !EntryIsAlive(aliveBits, i)
    {

      forall i : nat | low + (LOG_SIZE as nat) <= i < high  + (LOG_SIZE as nat)
        ensures !EntryIsAlive(aliveBits, i)
      {
        assert i >= (LOG_SIZE as nat);
        assert exists j |  low <= j < high :: j + (LOG_SIZE as nat) == i by {
          var j := i - (LOG_SIZE as nat);
          assert low <= j < high;
          assert j + (LOG_SIZE as nat) == i;
        } // TODO proof
        assert !EntryIsAlive(aliveBits, i) by { } // TODO proof
      }
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
    && m.combinerState[nodeId].cur_idx < m.combinerState[nodeId].tail
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
    && m.combinerState[nodeId].readerState.cur < m.combinerState[nodeId].readerState.end
  }

  predicate CombinerIsReaderGuard(m: M, nodeId: NodeId)
    requires m.M?
    requires CombinerKnown(m, nodeId)
  {
    && m.combinerState[nodeId].CombinerReading?
    && m.combinerState[nodeId].readerState.ReaderGuard?
  }

  predicate CombinerIsReaderRangeDone(m: M, nodeId: NodeId)
    requires m.M?
    requires CombinerKnown(m, nodeId)
  {
    && m.combinerState[nodeId].CombinerReading?
    && m.combinerState[nodeId].readerState.ReaderRange?
    && m.combinerState[nodeId].readerState.cur == m.combinerState[nodeId].readerState.end
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
      assert Inv(dot(m', p)) by {
        assert RangesNoOverlap(dot(m', p)) by {
          // TODO: reveal_RangesNoOverlap(); this reveals quantifiers that cause a timeout
          //       it likely needs more granular trigger management
        }
      }
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
      assert Inv(dot(m', p)) by {
        assert RangesNoOverlap(dot(m', p)) by {
          // TODO: reveal_RangesNoOverlap(); this reveals quantifiers that cause a timeout
          //       it likely needs more granular trigger management
        }
      }
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
      assert PointerDifferences(dot(m', p));


      assert Inv(dot(m', p)) by {
        assert RangesNoOverlap(dot(m', p)) by {
          // TODO: reveal_RangesNoOverlap(); this reveals quantifiers that cause a timeout
          //       it likely needs more granular trigger management
        }
      }
      assert I(dot(m, p)) == I(dot(m', p));
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

      assert Inv(dot(m', p)) by {
        assert RangesNoOverlap(dot(m', p)) by {
          // TODO: reveal_RangesNoOverlap(); this reveals quantifiers that cause a timeout
          //       it likely needs more granular trigger management
        }
      }
      assert I(dot(m, p)) == I(dot(m', p));
    }
  }

  /* ----------------------------------------------------------------------------------------- */

  function map_update_filter<V>(m1: map<int, V>, m2: map<int, V>, minkey: int): map<int, V>
  requires m1.Keys !! m2.Keys
  {
    map k | k in (m1.Keys + m2.Keys) && minkey <= k :: if k in m2 then m2[k] else m1[k]
  }

  predicate FinishAdvanceTail(m: M, m': M, combinerNodeId: nat, new_tail: nat, withdrawn: map<nat, StoredType>) // withdraw
  {
    && m.M?
    && m.tail.Some?
    && CombinerKnown(m, combinerNodeId)
    && CombinerIsAdvancingTail(m, combinerNodeId)

    && var combinerBefore := m.combinerState[combinerNodeId];
    && m.tail.value <= new_tail <= (combinerBefore.observed_head + LOG_SIZE as int)
    && (forall i: int | m.tail.value - LOG_SIZE as int <= i < (m.tail.value - LOG_SIZE as int) + (new_tail - m.tail.value) :: i in m.contents)
    && assert forall i: int | (m.tail.value - LOG_SIZE as int <= i < new_tail - LOG_SIZE as int) :: i in m.contents;

    && (forall i: int | m.tail.value <= i < new_tail :: i !in m.contents)

    && var new_entries := map x : int | m.tail.value <= x < new_tail :: x := None;

    && m' == m.(
      combinerState := m.combinerState[combinerNodeId := CombinerAppending(m.tail.value, new_tail)],
      contents := map_update_filter(m.contents, new_entries, (new_tail as int - LOG_SIZE as int)),
      tail := Some(new_tail)
    )

    && (forall i | m.tail.value <= i < new_tail ::
      && i in withdrawn
      && (i - LOG_SIZE as int) in m.contents
      && Some(withdrawn[i]) == m.contents[i - LOG_SIZE as int])
  }

  lemma FinishAdvanceTail_is_withdraw_many(m: M, m': M, combinerNodeId: nat, new_tail: nat, withdrawn: map<nat, StoredType>)
  requires FinishAdvanceTail(m, m', combinerNodeId, new_tail, withdrawn)
  ensures withdraw_many(m, m', withdrawn)
  {
    forall p: M | Inv(dot(m, p))
    ensures Inv(dot(m', p))
      && I(dot(m', p)).Keys !! withdrawn.Keys
      && I(dot(m, p)) == (
        map k | k in (I(dot(m', p)).Keys + withdrawn.Keys) ::
        if k in I(dot(m', p)).Keys then I(dot(m', p))[k] else withdrawn[k])
    {
      //


      var x := dot(m', p);
      assert forall i : int :: (x.tail.value - (LOG_SIZE as nat) <= i < x.tail.value) ==> i in x.contents;

      assert Complete(dot(m', p));
      // assert PointerOrdering(dot(m', p));
      // assert PointerDifferences(dot(m', p));
      // assert RangesNoOverlap(dot(m', p));
      // assert AliveBits(dot(m', p));
      // assert BufferContents(dot(m', p));
      // assert ReaderStateValid(dot(m', p));
      // assert CombinerStateValid(dot(m', p));

      assert Inv(dot(m', p));
      assert I(dot(m', p)).Keys !! withdrawn.Keys;

      assert I(dot(m, p)) == (
        map k | k in (I(dot(m', p)).Keys + withdrawn.Keys) ::
        if k in I(dot(m', p)).Keys then I(dot(m', p))[k] else withdrawn[k]);
    }
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

    // obtain the combiner state, and the key
    && var combinerBefore := m.combinerState[combinerNodeId];
    && var key := combinerBefore.cur_idx;

    // there should be an entry corresponding to the key in the log, and it should be None.
    && key in m.contents
    && m.contents[key].None?

    // the entry we're about to write is note alive,
    && LogicalToPhysicalIndex(key) in m.aliveBits
    && !EntryIsAlive(m.aliveBits, key)

    // state realation
    && m' == m.(
      // increase the current index by one
      combinerState := m.combinerState[combinerNodeId := combinerBefore.(cur_idx := key + 1)],
      // update the alive bits
      aliveBits := m.aliveBits[LogicalToPhysicalIndex(key) := LogicalToAliveBitAliveWhen(key)],
      // update the key element in the log
      contents := m.contents[key := Some(deposited)])
  }

  // seems to take about 4 minutes...
  lemma AppendFlipBit_is_deposit(m: M, m': M, combinerNodeId: nat, deposited: StoredType)
    requires AppendFlipBit(m, m', combinerNodeId, deposited)
    ensures exists key :: deposit(m, m', key, deposited)
  {
    var combinerBefore := m.combinerState[combinerNodeId];
    var key := combinerBefore.cur_idx;

    forall p: M | Inv(dot(m, p))
    ensures Inv(dot(m', p))
      && key !in I(dot(m, p))
      && I(dot(m', p)) == I(dot(m, p))[key := deposited]
    {
      assert CombinerStateValid(dot(m', p)) by {
        assert forall n | n in dot(m', p).combinerState && dot(m', p).combinerState[n].CombinerAppending? ::
         (|| dot(m', p).combinerState[n].tail <= key
          || dot(m', p).combinerState[n].cur_idx > key);

        assert forall n | n in dot(m', p).combinerState && dot(m', p).combinerState[n].CombinerAppending? ::
          (forall i | dot(m', p).combinerState[n].cur_idx <= i < dot(m', p).combinerState[n].tail ::
            (&& EntryIsAlive(dot(m', p).aliveBits, i) == EntryIsAlive(dot(m, p).aliveBits, i)
            && !EntryIsAlive(dot(m', p).aliveBits, i))
          );
      }

      assert AliveBits(dot(m', p));
      assert BufferContents(dot(m', p));

      assert Inv(dot(m', p));
      assert key !in I(dot(m, p));

      assert I(dot(m', p)) == I(dot(m, p))[key := deposited];
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
      assert Inv(dot(m', p)) by {
        assert RangesNoOverlap(dot(m', p)) by {
          // TODO: reveal_RangesNoOverlap(); this reveals quantifiers that cause a timeout
          //       it likely needs more granular trigger management
        }
      }
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
      ReaderRange(readerBefore.start, m.tail.value, readerBefore.start))]
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
      assert Inv(dot(m', p)) by {
        assert RangesNoOverlap(dot(m', p)) by {
          // TODO: reveal_RangesNoOverlap(); this reveals quantifiers that cause a timeout
          //       it likely needs more granular trigger management
        }
      }
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
    && m.contents[i].Some?
    // Question(RA): we sort of require to  process all entries before completing
    //               and updating the local tail value. right now this is done
    //               using the cur pointer, and requires linear processing of
    //               the log, not sure if this causes a problem somewhere.
    // && readerBefore.start <= i < readerBefore.end
    && readerBefore.cur == i

    && LogicalToPhysicalIndex(i) in m.aliveBits
    && EntryIsAlive(m.aliveBits, i)

    && m' == m.(
      combinerState := m.combinerState[combinerNodeId := CombinerReading(
        ReaderGuard(readerBefore.start, readerBefore.end, i, m.contents[i].value))]
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
      assert Inv(dot(m', p)) by {
        assert RangesNoOverlap(dot(m', p)) by {
          // TODO: reveal_RangesNoOverlap(); this reveals quantifiers that cause a timeout
          //       it likely needs more granular trigger management
        }
      }
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
        ReaderRange(readerBefore.start, readerBefore.end, readerBefore.cur + 1))]
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
      assert Inv(dot(m', p)) by {
        assert RangesNoOverlap(dot(m', p)) by {
          // TODO: reveal_RangesNoOverlap(); this reveals quantifiers that cause a timeout
          //       it likely needs more granular trigger management
        }
      }
      assert I(dot(m, p)) == I(dot(m', p));
    }
  }

  /* ----------------------------------------------------------------------------------------- */

  predicate ReaderDoFinish(m: M, m': M, combinerNodeId: nat)
  {
    && m.M?

    && CombinerKnown(m, combinerNodeId)
    && CombinerIsReaderRangeDone(m, combinerNodeId)
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
      if MinLocalTail(dot(m, p).localTails) == MinLocalTail(dot(m', p).localTails) {
        assert Inv(dot(m', p));
        assert I(dot(m, p)) == I(dot(m', p));
      } else {
        assert MinLocalTail(dot(m, p).localTails) < MinLocalTail(dot(m', p).localTails);
        var old_mintails := MinLocalTail(dot(m, p).localTails);
        var new_mintails := MinLocalTail(dot(m', p).localTails);

        // everything between old_mintails and new_mintails had to be alive, otherwise we
        // couldn't have processed it. Now, transform this into the !Alive for the new mintail
        assert forall i | old_mintails <= i < new_mintails :: EntryIsAlive(dot(m', p).aliveBits, i);
        EntryIsAliveWrapAround(dot(m', p).aliveBits, old_mintails , new_mintails );
        EntryIsAliveWrapAroundReformat(dot(m', p).aliveBits, old_mintails , new_mintails );

        assert Inv(dot(m', p));
        assert I(dot(m, p)) == I(dot(m', p));
      }
    }
  }
}
