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
    | CombinerAdvancingTail(ghost obvserve_head: nat)
    | CombinerAppendState(ghost cur_idx: nat, ghost tail: nat)

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

  function Index(logical: int) : nat
  // ensures Index(-(BUFFER_SIZE as int)) == 0
  {
    logical % (BUFFER_SIZE as int)
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

  predicate CombierIdle(m: M, nodeId: NodeId)
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

  /*
   * ============================================================================================
   * Advance Head Transitions
   * ============================================================================================
   */

  predicate InitAdvanceHead(m: M, m': M, combinerNodeId: nat)
  {
    && m.M?
    && LocalTailValid(m, 0)

    && m'.M?
    && CombinerKnown(m', combinerNodeId)
    && CombinerIsAdvancingHeadAt(m', combinerNodeId, 1, m.localTails[0])
  }

  predicate StepAdvanceHead(m: M, m': M, combinerNodeId: nat)
  {
    && m.M?
    && CombinerKnown(m, combinerNodeId)
    && CombinerIsAdvancingHead(m, combinerNodeId)
    && var combinerBefore := m.combinerState[combinerNodeId];
    && LocalTailValid(m, combinerBefore.idx)

    && m'.M?
    && CombinerKnown(m', combinerNodeId)
    && CombinerIsAdvancingHeadAt(m', combinerNodeId, combinerBefore.idx + 1,
      if combinerBefore.min_tail < m.localTails[combinerBefore.idx]
        then combinerBefore.min_tail
        else m.localTails[combinerBefore.idx])
  }

  predicate FinishAdvanceHead(m: M, m': M, combinerNodeId: nat)
  {
    && m.M?
    && CombinerKnown(m, combinerNodeId)
    && CombinerIsAdvancingHead(m, combinerNodeId)
    && var combinerBefore := m.combinerState[combinerNodeId];
    && combinerBefore.idx == (NUM_REPLICAS as nat)

    && m'.M?
    && m'.head.Some?
    && m'.head.value == combinerBefore.min_tail
  }

  /*
   * ============================================================================================
   * Advance Tail Transitions
   * ============================================================================================
   */

  // predicate InitAdvanceTail(m: M, m': M, advancerNodeId: nat)
  // {
  //   && m.M?
  //   && 
  // }

  /////////////////////////////////////////////////////////////////////////////
  // Functions
  /////////////////////////////////////////////////////////////////////////////

  // /////////////////////////////////////////////////////////////////////////////
  // // Advance Head Guards
  // /////////////////////////////////////////////////////////////////////////////

  // // we're in the advance head idle state
  // predicate AdvHeadInIdle(m: M, nodeId: NodeId)
  //   requires StateValid(m)
  // {
  //   && nodeId in m.advanceHead
  //   && m.advanceHead[nodeId].AdvanceHeadIdle?
  // }

  // predicate AdvHeadInNextLoaded(m: M, nodeId: NodeId)
  //   requires StateValid(m)
  // {
  //   && nodeId in m.advanceHead
  //   && m.advanceHead[nodeId].AdvHeadNextLoaded?
  // }

  // predicate AdvHeadInReadHead(m: M, nodeId: NodeId)
  //   requires StateValid(m)
  // {
  //   && nodeId in m.advanceHead
  //   && m.advanceHead[nodeId].AdvHeadHeadLoaded?
  // }

  // predicate AdvHeadInMinLTail(m: M, nodeId: NodeId)
  //   requires StateValid(m)
  // {
  //   && nodeId in m.advanceHead
  //   && m.advanceHead[nodeId].AdvHeadMinLtail?
  //   && m.advanceHead[nodeId].idx < m.advanceHead[nodeId].next
  // }

  // predicate AdvHeadMinLtailValid(m: M, nodeId: NodeId)
  //   requires AdvHeadInMinLTail(m, nodeId)
  // {
  //   && var st := m.advanceHead[nodeId];
  //   && st.idx in m.LocalTails
  // }

  // predicate AdvHeadInMinLTailDone(m: M, nodeId: NodeId)
  //   requires StateValid(m)
  // {
  //   && nodeId in m.advanceHead
  //   && m.advanceHead[nodeId].AdvHeadMinLtail?
  //   && m.advanceHead[nodeId].idx == m.advanceHead[nodeId].next
  // }

  // /////////////////////////////////////////////////////////////////////////////
  // // Append Guards
  // /////////////////////////////////////////////////////////////////////////////

  // predicate AppendInIdle(m: M, nodeId: NodeId)
  //   requires StateValid(m)
  // {
  //   && nodeId in m.appendState
  //   && m.appendState[nodeId].AppendIdle?
  // }

  // predicate AppendInAdvanceTail(m: M, nodeId: NodeId)
  //   requires StateValid(m)
  // {
  //   && nodeId in m.appendState
  //   && m.appendState[nodeId].AppendAdvanceTail?
  // }

  // predicate AppendInWriteLogEntryFlipMask(m: M, nodeId: NodeId)
  //   requires StateValid(m)
  // {
  //   && nodeId in m.appendState
  //   && m.appendState[nodeId].AppendWriteLogEntry?
  //   && m.appendState[nodeId].idx < |m.appendState[nodeId].ops|
  //   && nodeId in m.lmasks
  //   && st.idx in m.slog
  //   && m.slog[st.idx].alive == m.lmasks[nodeId]
  // }

  // predicate AppendInWriteLogEntryDone(m: M, nodeId: NodeId)
  //   requires StateValid(m)
  // {
  //   && nodeId in m.appendState
  //   && m.appendState[nodeId].AppendWriteLogEntry?
  //   && m.appendState[nodeId].idx == |m.appendState[nodeId].ops|
  // }

  // predicate AppendInWriteLogEntry(m: M, nodeId: NodeId)
  //   requires StateValid(m)
  // {
  //   && nodeId in m.appendState
  //   && m.appendState[nodeId].AppendWriteLogEntry?
  //   && nodeId in m.lmasks
  //   && st.idx in m.slog
  //   && m.slog[st.idx].alive != m.lmasks[nodeId]
  // }


  // /////////////////////////////////////////////////////////////////////////////
  // // Reader Guards
  // /////////////////////////////////////////////////////////////////////////////

  // predicate ReaderInIdle(m: M, nodeId: NodeId)
  //   requires StateValid(m)
  // {
  //   && nodeId in m.readerState
  //   && m.readerState[nodeId].ReaderIdle?
  // }

  // predicate ReaderInLoadTail(m: M, nodeId: NodeId)
  //   requires StateValid(m)
  // {
  //   && nodeId in m.readerState
  //   && m.readerState[nodeId].ReaderLoadTail?
  // }

  // predicate ReaderInReadEntries(m: M, nodeId: NodeId)
  //   requires StateValid(m)
  // {
  //   && nodeId in m.readerState
  //   && m.readerState[nodeId].ReaderReadEntries?
  //   && m.readerState[nodeId].ltail != m.readerState[nodeId].gtail
  // }

  // predicate ReaderInReadEntriesDone(m: M, nodeId: NodeId)
  //   requires StateValid(m)
  // {
  //   && nodeId in m.readerState
  //   && nodeId in m.localTails
  //   && m.readerState[nodeId].ReaderReadEntries?
  //   && m.readerState[nodeId].ltail == m.readerState[nodeId].gtail
  //   && m.readerState[nodeId].ltail != m.localTails[nodeId]
  // }

  // predicate ReaderInReadEntriesDoneNoUpdate(m: M, nodeId: NodeId)
  //   requires StateValid(m)
  // {
  //   && nodeId in m.readerState
  //   && nodeId in m.localTails
  //   && m.readerState[nodeId].ReaderReadEntries?
  //   && m.readerState[nodeId].ltail == m.readerState[nodeId].gtail
  //   && m.readerState[nodeId].ltail == m.localTails[nodeId]
  // }

  // /////////////////////////////////////////////////////////////////////////////
  // // Reading Transitions
  // /////////////////////////////////////////////////////////////////////////////

  // // { ReaderIdle }
  // //   let ltail = self.ltails[idx - 1].load(Ordering::Relaxed);
  // // { ReaderLoadTail(ltail) }
  // predicate TransitionReaderLoadTail(m: M, m': M, nodeId: NodeId)
  // {
  //   && StateValid(m)
  //   && ReaderInIdle(m, nodeId)

  //   // get the local tail
  //   && var ltail := m.localTails[nodeId];

  //   // construct the new state
  //   && var new_st := ReaderLoadTail(ltail);

  //   // the state transition
  //   && m' == m.(readerState := m.readerState[ nodeId := new_st ])
  // }


  // // { ReaderLoadTail(ltail) }
  // //   let gtail = self.tail.load(Ordering::Relaxed);
  // // { ReaderReadEntries(ltail, gtail) }
  // predicate TransitionReaderReadEntries(m: M, m': M, nodeId: NodeId)
  // {
  //   && StateValid(m)
  //   && ReaderInLoadTail(m, nodeId)

  //   // the old state
  //   && var st := m.readerState[nodeId];

  //   // get the local tail
  //   && var gtail := m.tail.value;

  //   // construct the new state
  //   && var new_st := ReaderReadEntries(ltail, gtail);

  //   // the state transition
  //   && m' == m.(readerState := m.readerState[ nodeId := new_st ])
  // }

  // // { ReaderReadEntries(ltail, gtail) }
  // // { (*e).alivef.load(Ordering::Acquire) == self.lmasks[idx - 1].get() }
  // //   d((*e).operation.as_ref().unwrap().clone(), (*e).replica)
  // //   if self.index(i) == self.size - 1 { self.lmasks[idx - 1].set(!self.lmasks[idx - 1].get()); }
  // // { ReaderReadEntries(ltail + 1, gtail)  }
  // predicate TransitionReaderReadEntry(m: M, m': M, nodeId: NodeId)
  // {
  //   && StateValid(m)
  //   && ReaderInReadEntries(m, nodeId)

  //   // the old state
  //   && var st := m.readerState[nodeId];

  //   && var entry := m.slog[st.ltail];
  //   // TODO: do something

  //   // update the new lmask if needed
  //   && var m := m.lmasks[nodeId];
  //   && var new_mask := if Index(st.ltail, m.size) == m.size - 1 then !m else m;

  //   // construct the new state
  //   && var new_st := ReaderReadEntries(st.ltail + 1, st.gtail);

  //   // the state transition
  //   && m' == m.(readerState := m.readerState[ nodeId := new_st ])
  //             .(lmasks := m.lmasks[nodeId := new_mask])

  // }


  // // { ReaderReadEntries(ltail, gtail)}
  // // { gtail == ltail } && { m.localTails[nodeId] == ltail }
  // //   if ltail == gtail { return; }
  // // { ReaderIdle }
  // predicate TransitionReaderIdleNoUpdates(m: M, m': M, nodeId: NodeId)
  // {
  //   && StateValid(m)
  //   && ReaderInReadEntriesDoneNoUpdate(m, nodeId)

  //   // construct the new state
  //   && var new_st := ReaderIdle;

  //   // the state transition
  //   && m' == m.(readerState := m.readerState[ nodeId := new_st ])
  // }



  // // { ReaderReadEntries(ltail, gtail)}
  // // { gtail == ltail } && { m.localTails[nodeId] != ltail }
  // //    self.ltails[idx - 1].store(gtail, Ordering::Relaxed);
  // // { ReaderIdle }
  // redicate ReaderInReadEntriesDone(m: M, m': M, nodeId: NodeId)
  // {
  //   && StateValid(m)
  //   && ReaderInReadEntries(m, nodeId)

  //   // the old state
  //   && var st := m.readerState[nodeId];

  //   // get the local tail
  //   && var gtail := m.tail.value;

  //   // construct the new state
  //   && var new_st := ReaderIdle;

  //   // the new ltail si the gtail
  //   && var new_ltail := st.gtail;

  //   // the state transition
  //   && m' == m.(readerState := m.readerState[ nodeId := new_st ])
  //             .(ltails := m.ltails[nodeId := new_ltail])
  // }



  // /////////////////////////////////////////////////////////////////////////////
  // // Append Transitions
  // /////////////////////////////////////////////////////////////////////////////

  // // pub fn append<F: FnMut(T, usize)>(&self, ops: &[T], idx: usize, mut s: F)


  // // { AppendIdle }
  // //   let tail = self.tail.load(Ordering::Relaxed);
  // // { AppendAdvanceTail(ops, tail) }
  // predicate TransitionAppendAdvanceTail(m: M, m': M, nodeId: NodeId, ops: seq<nrifc.UpdateOp>) {
  //     && StateValid(m)
  //     && AppendInIdle(m, nodeId)
  //     && TailFieldValid(m)

  //     // read the tail field
  //     && var tail := m.tail.value;

  //     // construct the new state
  //     && var newst := AppendAdvanceTail(ops, tail);

  //     // the state transition
  //     && m' == m.(appendState := m.appendState[nodeId := newst])
  // }
  // // TODO, the case where we exec??? if tail > head + self.size - GC_FROM_HEAD {

  // // { AppendAdvanceTail(ops, tail) }
  // // self.tail.compare_exchange_weak()  // if we had another update
  // // { AppendAdvanceTail(ops, tail) }
  // predicate TransitionAppendWriteLogEntry(m: M, m': M, nodeId: NodeId) {
  //     && StateValid(m)
  //     && AppendAdvanceTail(m, nodeId)
  //     && TailFieldValid(m)

  //     // read the tail field
  //     && var tail := m.tail.value;

  //     // the old state
  //     var st := m.appendState[nodeId];

  //     // if the two tails are not equal, retry
  //     && st.tail != tail

  //     // construct the new state
  //     && var newst := AppendAdvanceTail(ops, tail);

  //     // the state transition
  //     && m' == m.(appendState := m.appendState[nodeId := newst])
  // }


  // // { AppendAdvanceTail(ops, tail) }
  // // self.tail.compare_exchange_weak()
  // // { AppendWriteLogEntry(ops, tail, idx = 0) }
  // predicate TransitionAppendWriteLogEntry(m: M, m': M, nodeId: NodeId) {
  //     && StateValid(m)
  //     && AppendInAdvanceTail(m, nodeId)
  //     && TailFieldValid(m)

  //     // read the tail field
  //     && var tail := m.tail.value;

  //     // the old state
  //     var st := m.appendState[nodeId];

  //     // the two tails must be equal
  //     && st.tail == tail

  //     // read the tail field
  //     && var tail_new := tail + |st.ops|;

  //     // construct the new state
  //     && var newst := AppendWriteLogEntry(ops, tail, idx);

  //     // the state transition
  //     && m' == m.(appendState := m.appendState[nodeId := newst])
  //               .(tail := Some(tail_new))
  // }

  // // { AppendWriteLogEntry(ops, tail, idx) }
  // //   if unsafe { (*e).alivef.load(Ordering::Relaxed) == m } { m = !m; }
  // // { AppendWriteLogEntry(ops, tail, idx) }
  // predicate TransitionAppendWriteLogEntryOp(m: M, m': M, nodeId: NodeId) {
  //     && StateValid(m)
  //     && AppendInWriteLogEntryFlipMask(m, nodeId)

  //     // the old state
  //     && var st := m.appendState[nodeId];

  //     // construct the new state
  //     && var newst := AppendWriteLogEntryOp(ops, tail, idx);

  //     // construct the new mask value
  //     && var newmask := !m.lmasks[nodeId];

  //     // the state transition
  //     && m' == m.(appendState := m.appendState[nodeId := newst])
  //               .(lmasks := m.lmasks[nodeId := newmask])
  // }

  // // { AppendWriteLogEntry(ops, tail, idx) }
  // //   unsafe { (*e).alivef.store(m, Ordering::Release) };
  // // { AppendWriteLogEntry(ops, tail, idx + 1) }
  // predicate TransitionAppendWriteLogNext(m: M, m': M, nodeId: NodeId) {
  //     && StateValid(m)
  //     && AppendInWriteLogEntry(m, nodeId)

  //     // the old state
  //     && var st := m.appendState[nodeId];

  //     // construct the new state
  //     && var newst := AppendWriteLogEntryOp(ops, tail, idx + 1);

  //     // construct the log entry
  //     && var logentry := StoredType(st.ops[st.idx]);

  //     // the state transition
  //     && m' == m.(appendState := m.appendState[nodeId := newst])
  //               .(slog := m.slog[st.tail + st.idx := logentry])
  // }

  // // assert idx == |ops|
  // // { AppendWriteLogEntry(ops, tail, idx + 1) }
  // // { AppendIdle }
  // predicate TransitionAppendWriteLogDone(m: M, m': M, nodeId: NodeId) {
  //     && StateValid(m)
  //     && AppendInWriteLogEntryDone(m, nodeId)

  //     // construct the new state
  //     && var newst := AppendIdle;

  //      // the state transition
  //     && m' == m.(appendState := m.appendState[nodeId := newst])
  // }



  // /////////////////////////////////////////////////////////////////////////////
  // // AdvanceHead Transitions
  // /////////////////////////////////////////////////////////////////////////////

  // // fn advance_head<F: FnMut(T, usize)>(&self, rid: usize, mut s: &mut F);

  // // { AdvHeadIdle }
  // //   let r = self.next.load(Ordering::Relaxed);
  // // { AdvHeadNextLoaded(next) }
  // predicate TransitionAdvHeadLoadNext(m: M, m': M, nodeId: NodeId) {
  //   && StateValid(m)
  //   && AdvHeadInIdle(m, nodeId)
  //   && NextFieldValid(m)

  //   // read the next field
  //   && var next := m.next.value;

  //   // construct the new state
  //   && var newst := AdvHeadNextLoaded(next);

  //   // update the state of the advanceHead
  //   && m' == m.(advanceHead := m.advanceHead[ nodeId :=  newst])
  // }

  // // { AdvHeadNextLoaded(next) }
  // //   let global_head = self.head.load(Ordering::Relaxed);
  // // { AdvHeadHeadLoaded(next, head) }
  // predicate TransitionAdvHeadReadHead(m: M, m': M, nodeId: NodeId) {
  //   && StateValid(m)
  //   && AdvHeadInNextLoaded(m, nodeId)
  //   && HeadFieldValid(m)

  //   // get the old state
  //   && var st := m.advanceHead[nodeId];

  //   // read the next field
  //   && var head := m.head.value;

  //   // construct the new state
  //   && var newst := AdvHeadNextLoaded(st.next, head);

  //   // update the state of the advanceHead
  //   && m' == m.(advanceHead := m.advanceHead[ nodeId :=  newst])
  // }


  // // let f = self.tail.load(Ordering::Relaxed);
  // // that one seems to be no-where used??

  // // { AdvHeadHeadLoaded(next, head) }
  // //   let mut min_local_tail = self.ltails[0].load(Ordering::Relaxed);
  // // { AdvHeadMinLtail(next, head, min_local_tail, idx = 1) }
  // predicate TransitionAdvHeadMinLTail(m: M, m': M, nodeId: NodeId) {
  //   && StateValid(m)
  //   && AdvHeadInReadHead(m, nodeId)
  //   && 0 in m.localTails

  //   // get the old state
  //   && var st := m.advanceHead[nodeId];

  //   // read the first local tail
  //   && var ltail := m.localTails[0];

  //   // construct the new state
  //   && var newst := AdvHeadMinLtail(st.next, st.head, ltail, 1);

  //   // update the state of the advanceHead
  //   && m' == m.(advanceHead := m.advanceHead[ nodeId :=  newst])
  // }


  // // { AdvHeadMinLtail(next, head, min_local_tail, idx = 1)
  // //   for idx in 1..r {
  // //     let cur_local_tail = self.ltails[idx - 1].load(Ordering::Relaxed);
  // //     if min_local_tail > cur_local_tail {
  // //         min_local_tail = cur_local_tail
  // //     };
  // //   }
  // // assert(idx == next)
  // // { AdvHeadMinLtail(next, head, min_local_tail, idx = next)
  // predicate TransitionAdvHeadMinLTailNext(m: M, m': M, nodeId: NodeId) {
  //   && StateValid(m)
  //   && AdvHeadInMinLTail(m, nodeId)
  //   && AdvHeadMinLtailValid(m, nodeId)

  //   // get the old state
  //   && var st := m.advanceHead[nodeId];

  //   // read the current local tail
  //   && var cur_local_tail := m.localTails[st.idx];

  //   // if the current local tail is smaller, update the value
  //   && var ltail := if st.mintail > cur_local_tail then cur_local_tail else st.mintail;

  //   // construct the new state
  //   && var newst := AdvHeadMinLtail(st.next, st.head, ltail, st.idx + 1);

  //   // update the state of the advanceHead
  //   && m' == m.(advanceHead := m.advanceHead[ nodeId :=  newst])
  // }

  // // What About the exec stuff here?
  // // { AdvHeadMinLtail(next, head, min_local_tail, idx = next)
  // //   self.head.store(min_local_tail, Ordering::Relaxed);
  // // { AdvHeadIdle }
  // predicate TransitionAdvHeadIdle(m: M, m': M, nodeId: NodeId) {
  //   && StateValid(m)
  //   && AdvHeadInMinLTailDone(m, nodeId)

  //   // get the old state
  //   && var st := m.advanceHead[nodeId];

  //   // the new head value
  //   && var new_head := st.mintail;

  //   // construct the new state
  //   && var newst := AdvHeadIdle;

  //   // update the state of the advanceHead
  //   && m' == m.(advanceHead := m.advanceHead[ nodeId :=  newst])
  //             .(head := Some(new_head))
  // }

}
