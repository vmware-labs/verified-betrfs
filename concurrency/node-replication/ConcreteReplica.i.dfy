include "NRSpec.s.dfy"
include "../../lib/Lang/NativeTypes.s.dfy"

module CounterIfc refines NRIfc {
  import opened NativeTypes

  type NRState = uint64
  datatype UpdateOp = IncrementOp
  datatype ReadonlyOp = ReadOp
  type ReturnType = uint64

  function init_state() : NRState { 0 }
  function update(s: NRState, op: UpdateOp) : UpdateResult {
    if s == 0xffff_ffff_ffff_ffff then
      UpdateResult(0, s)
    else
      UpdateResult(s + 1, s)
  }
  function read(s: NRState, op: ReadonlyOp) : ReturnType { s }

  // Implementation stuff:

  linear datatype DataStructureType = Counter(u: uint64)

  function I(ds: DataStructureType) : NRState
  {
    ds.u
  }

  method initialize()
  returns (linear s: DataStructureType)
  ensures I(s) == init_state()
  {
    s := Counter(0);
  }

  method do_update(linear s: DataStructureType, op: UpdateOp)
  returns (linear s': DataStructureType, ret: ReturnType)
  ensures UpdateResult(I(s'), ret) == update(I(s), op)
  {
    linear var Counter(t) := s;
    s' := Counter(if t == 0xffff_ffff_ffff_ffff then 0 else t + 1);
    ret := t;
  }

  method do_readonly(shared s: DataStructureType, op: ReadonlyOp)
  returns (ret: ReturnType)
  ensures ret == read(I(s), op)
  {
    ret := s.u;
  }
}
