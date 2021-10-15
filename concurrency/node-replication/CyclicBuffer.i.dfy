include "../../lib/Lang/NativeTypes.s.dfy"
include "InfiniteLogTokens.i.dfy"
include "../framework/Cells.s.dfy"
include "../framework/GlinearOption.s.dfy"
include "Constants.i.dfy"

module CyclicBufferRw(nrifc:  refines MultiRw {
  type Key(!new) = nat
  glinear datatype StoredType = StoredType(
    glinear cellContents: CellContents<LogEntry>,
    glinear logEntry: glOption<Log>
  )

  datatype AdvanceHeadState = AdvanceHeadState(idx: nat, min_tail: nat)
  datatype AdvanceTailState = AdvanceTailState(obvserve_head: nat)
  datatype AppendState = AppendState(cur_idx: nat, tail: nat)

  datatype M =
    | MInvalid
    | M(
      head: Option<nat>,
      globalTail: Option<nat>,
      localTails: map<nat, nat>,
      contents: map<int, StoredType>,
      // TODO: could we have multiple threads advancing the head, we assume so
      advanceHead: map<nat, AdvanceHeadState>,
      advanceTail: map<nat, AdvanceTailState>,
      appendState: map<nat, AppendState>,
    )

  function dot(x: M, y: M) : M
  function unit() : M

  predicate Init(s: M)
  predicate Inv(x: M) 
  function I(x: M) : map<Key, StoredType> requires Inv(x)
}
