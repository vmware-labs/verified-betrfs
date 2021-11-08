include "../../lib/Lang/NativeTypes.s.dfy"


module {:extern ""} VSpaceStruct {
    import opened NativeTypes
    function method {:extern} create_vspace() : VSpacePtr

    type {:extern "struct"} VSpacePtr(!new) {
        function method {:extern} map_generic_wrapped(va: uint64, pa: uint64, len: uint64) : uint64
        function method {:extern} resolve_wrapper(va: uint64) : uint64
    }
}