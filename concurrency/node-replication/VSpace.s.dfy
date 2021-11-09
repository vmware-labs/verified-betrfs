include "../../lib/Lang/NativeTypes.s.dfy"


module {:extern ""} VSpaceStruct {
    import opened NativeTypes
    function method {:extern} createVSpace() : VSpacePtr

    type {:extern "struct"} VSpacePtr(!new) {
        function method {:extern} mapGenericWrapped(va: uint64, pa: uint64, len: uint64) : uint64
        function method {:extern} resolveWrapped(va: uint64) : uint64
    }
}