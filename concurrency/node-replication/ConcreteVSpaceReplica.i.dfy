include "NRSpec.s.dfy"
include "VSpace.s.dfy"
include "../../lib/Lang/NativeTypes.s.dfy"

module VSpaceIfc refines NRIfc {
  import opened NativeTypes
  import opened VSpaceStruct

  type NRState = uint64
  datatype UpdateOp = AdjustOp
  datatype ReadonlyOp = ReadOp
  type ReturnType = uint64

  function init_state() : NRState { 0 }
  function update(s: NRState, op: UpdateOp) : UpdateResult {
    UpdateResult(0, 0)
  }
  function read(s: NRState, op: ReadonlyOp) : ReturnType { 0 }

  // Implementation stuff:
  linear datatype DataStructureType = VSpaceWrapper(inner: VSpacePtr)

  function I(ds: DataStructureType) : NRState { 0 }

  method initialize()
  returns (linear s: DataStructureType)
  ensures I(s) == init_state()
  {
    var inner := createVSpace();
    s := VSpaceWrapper(inner);
  }

  method do_update(linear s: DataStructureType, op: UpdateOp)
  returns (linear s': DataStructureType, ret: ReturnType)
  ensures UpdateResult(I(s'), ret) == update(I(s), op)
  {
    linear var VSpaceWrapper(inner) := s;
    ret := inner.mapGenericWrapped(0x0, 0x0, 0x1000);
    s' := VSpaceWrapper(inner);
  }

  method do_readonly(shared s: DataStructureType, op: ReadonlyOp)
  returns (ret: ReturnType)
  ensures ret == read(I(s), op)
  {
    ret := s.inner.resolveWrapped(0x0);
  }
}
