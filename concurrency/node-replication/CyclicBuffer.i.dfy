include "../../lib/Lang/NativeTypes.s.dfy"
include "InfiniteLogTokens.i.dfy"
include "../framework/Cells.s.dfy"
include "../framework/GlinearOption.s.dfy"
include "Constants.i.dfy"


module CyclicBufferRw(nrifc: NRIfc) refines MultiRw {
  type Key(!new) = nat

  glinear datatype StoredType = StoredType(
    glinear cellContents: CellContents<LogEntry>,
    glinear logEntry: glOption<Log>
  )

  datatype AdvanceHeadState =
    | AdvanceHeadIdle
    | AdvHeadNextLoaded(next: NodeId)
    | AdvHeadHeadLoaded(next: NodeId, head : nat)
    | AdvHeadMinLtail(next: NodeId, head: nat, mintail: nat, idx: NodeId)

  datatype AdvanceTailState = AdvanceTailState(obvserve_head: nat)

  datatype AppendState =
    | AppendIdle
    | AppendAdvanceTail(ops: seq<nrifc.UpdateOp>, tail: nat)
    | AppendWriteLogEntry(ops: seq<nrifc.UpdateOp>, tail: nat, idx: nat)


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

      // Completed tail maintains an index <= tail that points to a
      // log entry after which there are no completed operations across
      // all replicas registered against this log.
      // TODO(RA): do we need this?
      // ctail: Option<nat>,

      // Array consisting of the local tail of each replica registered with the log.
      // Required for garbage collection; since replicas make progress over the log
      // independently, we want to make sure that we don't garbage collect operations
      // that haven't been executed by all replicas.
      ltails: map<NodeId, nat>,

      // Identifier that will be allocated to the next replica that registers with
      // this Log. Also required to correctly index into ltails above.
      next: Option<NodeId>,

      /// Array consisting of local alive masks for each registered replica. Required
      /// because replicas make independent progress over the log, so we need to
      /// track log wrap-arounds for each of them separately.
      lmasks: map<NodeId, bool>,

      /// The maximum number of entries that can be held inside the log.
      size: Option<nat>,

      /// A reference to the actual log. Nothing but a slice of entries.
      // slog: &'a [Cell<Entry<T>>],
      slog: map<int, StoredType>,


      // TODO: could we have multiple threads advancing the head, we assume so
      advanceHead: map<NodeId, AdvanceHeadState>,
      advanceTail: map<NodeId, AdvanceTailState>,
      appendState: map<NodeId, AppendState>
    )

  function dot(x: M, y: M) : M
  function unit() : M

  predicate Init(s: M)
  predicate Inv(x: M)
  function I(x: M) : map<Key, StoredType> requires Inv(x)

  /////////////////////////////////////////////////////////////////////////////
  // Functions
  /////////////////////////////////////////////////////////////////////////////

  function Index(idx: nat, size: nat) : nat {
    idx % size
  }

  /////////////////////////////////////////////////////////////////////////////
  // State Guards
  /////////////////////////////////////////////////////////////////////////////

  predicate StateValid(m: M) {
    m.M?
  }

  predicate NextFieldValid(m: M)
    requires StateValid(m)
  {
    m.next.Some?
  }

  predicate HeadFieldValid(m: M)
    requires StateValid(m)
  {
    m.head.Some?
  }

  predicate TailFieldValid(m: M)
    requires StateValid(m)
  {
    m.tail.Some?
  }

  /////////////////////////////////////////////////////////////////////////////
  // Advance Head Guards
  /////////////////////////////////////////////////////////////////////////////

  // we're in the advance head idle state
  predicate AdvHeadInIdle(m: M, nodeId: NodeId)
    requires StateValid(m)
  {
    && nodeId in m.advanceHead
    && m.advanceHead[nodeId].AdvanceHeadIdle?
  }

  predicate AdvHeadInNextLoaded(m: M, nodeId: NodeId)
    requires StateValid(m)
  {
    && nodeId in m.advanceHead
    && m.advanceHead[nodeId].AdvHeadNextLoaded?
  }

  predicate AdvHeadInReadHead(m: M, nodeId: NodeId)
    requires StateValid(m)
  {
    && nodeId in m.advanceHead
    && m.advanceHead[nodeId].AdvHeadHeadLoaded?
  }

  predicate AdvHeadInMinLTail(m: M, nodeId: NodeId)
    requires StateValid(m)
  {
    && nodeId in m.advanceHead
    && m.advanceHead[nodeId].AdvHeadMinLtail?
    && m.advanceHead[nodeId].idx < m.advanceHead[nodeId].next
  }

  predicate AdvHeadMinLtailValid(m: M, nodeId: NodeId)
    requires AdvHeadInMinLTail(m, nodeId)
  {
    && var st := m.advanceHead[nodeId];
    && st.idx in m.LocalTails
  }

  predicate AdvHeadInMinLTailDone(m: M, nodeId: NodeId)
    requires StateValid(m)
  {
    && nodeId in m.advanceHead
    && m.advanceHead[nodeId].AdvHeadMinLtail?
    && m.advanceHead[nodeId].idx == m.advanceHead[nodeId].next
  }

  /////////////////////////////////////////////////////////////////////////////
  // Append Guards
  /////////////////////////////////////////////////////////////////////////////

  predicate AppendInIdle(m: M, nodeId: NodeId)
    requires StateValid(m)
  {
    && nodeId in m.appendState
    && m.appendState[nodeId].AppendIdle?
  }

  predicate AppendInAdvanceTail(m: M, nodeId: NodeId)
    requires StateValid(m)
  {
    && nodeId in m.appendState
    && m.appendState[nodeId].AppendAdvanceTail?
  }

  predicate AppendInWriteLogEntryFlipMask(m: M, nodeId: NodeId)
    requires StateValid(m)
  {
    && nodeId in m.appendState
    && m.appendState[nodeId].AppendWriteLogEntry?
    && m.appendState[nodeId].idx < |m.appendState[nodeId].ops|
    && nodeId in m.lmasks
    && st.idx in m.slog
    && m.slog[st.idx].alive == m.lmasks[nodeId]
  }

  predicate AppendInWriteLogEntryDone(m: M, nodeId: NodeId)
    requires StateValid(m)
  {
    && nodeId in m.appendState
    && m.appendState[nodeId].AppendWriteLogEntry?
    && m.appendState[nodeId].idx == |m.appendState[nodeId].ops|
  }

  predicate AppendInWriteLogEntry(m: M, nodeId: NodeId)
    requires StateValid(m)
  {
    && nodeId in m.appendState
    && m.appendState[nodeId].AppendWriteLogEntry?
    && nodeId in m.lmasks
    && st.idx in m.slog
    && m.slog[st.idx].alive != m.lmasks[nodeId]
  }


  /////////////////////////////////////////////////////////////////////////////
  // Reading Transitions
  /////////////////////////////////////////////////////////////////////////////

  //
  //
  //
  //

  /////////////////////////////////////////////////////////////////////////////
  // Append Transitions
  /////////////////////////////////////////////////////////////////////////////

  // pub fn append<F: FnMut(T, usize)>(&self, ops: &[T], idx: usize, mut s: F)




  // { AppendIdle }
  //   let tail = self.tail.load(Ordering::Relaxed);
  // { AppendAdvanceTail(ops, tail) }
  predicate TransitionAppendAdvanceTail(m: M, m': M, nodeId: NodeId, ops: seq<nrifc.UpdateOp>) {
      && StateValid(m)
      && AppendInIdle(m, nodeId)
      && TailFieldValid(m)

      // read the tail field
      && var tail := m.tail.value;

      // construct the new state
      && var newst := AppendAdvanceTail(ops, tail);

      // the state transition
      && m' == m.(appendState := m.appendState[nodeId := newst])
  }
  // TODO, the case where we exec??? if tail > head + self.size - GC_FROM_HEAD {

  // { AppendAdvanceTail(ops, tail) }
  // self.tail.compare_exchange_weak()  // if we had another update
  // { AppendAdvanceTail(ops, tail) }
  predicate TransitionAppendWriteLogEntry(m: M, m': M, nodeId: NodeId) {
      && StateValid(m)
      && AppendAdvanceTail(m, nodeId)
      && TailFieldValid(m)

      // read the tail field
      && var tail := m.tail.value;

      // the old state
      var st := m.appendState[nodeId];

      // if the two tails are not equal, retry
      && st.tail != tail

      // construct the new state
      && var newst := AppendAdvanceTail(ops, tail);

      // the state transition
      && m' == m.(appendState := m.appendState[nodeId := newst])
  }


  // { AppendAdvanceTail(ops, tail) }
  // self.tail.compare_exchange_weak()
  // { AppendWriteLogEntry(ops, tail, idx = 0) }
  predicate TransitionAppendWriteLogEntry(m: M, m': M, nodeId: NodeId) {
      && StateValid(m)
      && AppendInAdvanceTail(m, nodeId)
      && TailFieldValid(m)

      // read the tail field
      && var tail := m.tail.value;

      // the old state
      var st := m.appendState[nodeId];

      // the two tails must be equal
      && st.tail == tail

      // read the tail field
      && var tail_new := tail + |st.ops|;

      // construct the new state
      && var newst := AppendWriteLogEntry(ops, tail, idx);

      // the state transition
      && m' == m.(appendState := m.appendState[nodeId := newst])
                .(tail := Some(tail_new))
  }

  // { AppendWriteLogEntry(ops, tail, idx) }
  //   if unsafe { (*e).alivef.load(Ordering::Relaxed) == m } { m = !m; }
  // { AppendWriteLogEntry(ops, tail, idx) }
  predicate TransitionAppendWriteLogEntryOp(m: M, m': M, nodeId: NodeId) {
      && StateValid(m)
      && AppendInWriteLogEntryFlipMask(m, nodeId)

      // the old state
      && var st := m.appendState[nodeId];

      // construct the new state
      && var newst := AppendWriteLogEntryOp(ops, tail, idx);

      // construct the new mask value
      && var newmask := !m.lmasks[nodeId];

      // the state transition
      && m' == m.(appendState := m.appendState[nodeId := newst])
                .(lmasks := m.lmasks[nodeId := newmask])
  }

  // { AppendWriteLogEntry(ops, tail, idx) }
  //   unsafe { (*e).alivef.store(m, Ordering::Release) };
  // { AppendWriteLogEntry(ops, tail, idx + 1) }
  predicate TransitionAppendWriteLogNext(m: M, m': M, nodeId: NodeId) {
      && StateValid(m)
      && AppendInWriteLogEntry(m, nodeId)

      // the old state
      && var st := m.appendState[nodeId];

      // construct the new state
      && var newst := AppendWriteLogEntryOp(ops, tail, idx + 1);

      // construct the log entry
      && var logentry := StoredType(st.ops[st.idx]);

      // the state transition
      && m' == m.(appendState := m.appendState[nodeId := newst])
                .(slog := m.slog[st.tail + st.idx := logentry])
  }

  // assert idx == |ops|
  // { AppendWriteLogEntry(ops, tail, idx + 1) }
  // { AppendIdle }
  predicate TransitionAppendWriteLogDone(m: M, m': M, nodeId: NodeId) {
      && StateValid(m)
      && AppendInWriteLogEntryDone(m, nodeId)

      // construct the new state
      && var newst := AppendIdle;

       // the state transition
      && m' == m.(appendState := m.appendState[nodeId := newst])
  }



  /////////////////////////////////////////////////////////////////////////////
  // AdvanceHead Transitions
  /////////////////////////////////////////////////////////////////////////////

  // fn advance_head<F: FnMut(T, usize)>(&self, rid: usize, mut s: &mut F);

  // { AdvHeadIdle }
  //   let r = self.next.load(Ordering::Relaxed);
  // { AdvHeadNextLoaded(next) }
  predicate TransitionAdvHeadLoadNext(m: M, m': M, nodeId: NodeId) {
    && StateValid(m)
    && AdvHeadInIdle(m, nodeId)
    && NextFieldValid(m)

    // read the next field
    && var next := m.next.value;

    // construct the new state
    && var newst := AdvHeadNextLoaded(next);

    // update the state of the advanceHead
    && m' == m.(advanceHead := m.advanceHead[ nodeId :=  newst])
  }

  // { AdvHeadNextLoaded(next) }
  //   let global_head = self.head.load(Ordering::Relaxed);
  // { AdvHeadHeadLoaded(next, head) }
  predicate TransitionAdvHeadReadHead(m: M, m': M, nodeId: NodeId) {
    && StateValid(m)
    && AdvHeadInNextLoaded(m, nodeId)
    && HeadFieldValid(m)

    // get the old state
    && var st := m.advanceHead[nodeId];

    // read the next field
    && var head := m.head.value;

    // construct the new state
    && var newst := AdvHeadNextLoaded(st.next, head);

    // update the state of the advanceHead
    && m' == m.(advanceHead := m.advanceHead[ nodeId :=  newst])
  }


  // let f = self.tail.load(Ordering::Relaxed);
  // that one seems to be no-where used??

  // { AdvHeadHeadLoaded(next, head) }
  //   let mut min_local_tail = self.ltails[0].load(Ordering::Relaxed);
  // { AdvHeadMinLtail(next, head, min_local_tail, idx = 1) }
  predicate TransitionAdvHeadMinLTail(m: M, m': M, nodeId: NodeId) {
    && StateValid(m)
    && AdvHeadInReadHead(m, nodeId)
    && 0 in m.localTails

    // get the old state
    && var st := m.advanceHead[nodeId];

    // read the first local tail
    && var ltail := m.localTails[0];

    // construct the new state
    && var newst := AdvHeadMinLtail(st.next, st.head, ltail, 1);

    // update the state of the advanceHead
    && m' == m.(advanceHead := m.advanceHead[ nodeId :=  newst])
  }


  // { AdvHeadMinLtail(next, head, min_local_tail, idx = 1)
  //   for idx in 1..r {
  //     let cur_local_tail = self.ltails[idx - 1].load(Ordering::Relaxed);
  //     if min_local_tail > cur_local_tail {
  //         min_local_tail = cur_local_tail
  //     };
  //   }
  // assert(idx == next)
  // { AdvHeadMinLtail(next, head, min_local_tail, idx = next)
  predicate TransitionAdvHeadMinLTailNext(m: M, m': M, nodeId: NodeId) {
    && StateValid(m)
    && AdvHeadInMinLTail(m, nodeId)
    && AdvHeadMinLtailValid(m, nodeId)

    // get the old state
    && var st := m.advanceHead[nodeId];

    // read the current local tail
    && var cur_local_tail := m.localTails[st.idx];

    // if the current local tail is smaller, update the value
    && var ltail := if st.mintail > cur_local_tail then cur_local_tail else st.mintail;

    // construct the new state
    && var newst := AdvHeadMinLtail(st.next, st.head, ltail, st.idx + 1);

    // update the state of the advanceHead
    && m' == m.(advanceHead := m.advanceHead[ nodeId :=  newst])
  }

  // What About the exec stuff here?
  // { AdvHeadMinLtail(next, head, min_local_tail, idx = next)
  //   self.head.store(min_local_tail, Ordering::Relaxed);
  // { AdvHeadIdle }
  predicate TransitionAdvHeadIdle(m: M, m': M, nodeId: NodeId) {
    && StateValid(m)
    && AdvHeadInMinLTailDone(m, nodeId)

    // get the old state
    && var st := m.advanceHead[nodeId];

    // the new head value
    && var new_head := st.mintail;

    // construct the new state
    && var newst := AdvHeadIdle;

    // update the state of the advanceHead
    && m' == m.(advanceHead := m.advanceHead[ nodeId :=  newst])
              .(head := Some(new_head))
  }

}
