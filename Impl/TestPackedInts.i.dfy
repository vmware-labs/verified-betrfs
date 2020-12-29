include "../lib/Lang/System/PackedInts.s.dfy"

module TestPackedInts {

    import opened NativePackedByte
    import opened NativeTypes

    method test()
    {
        var packed : seq<byte> := [1];
        var i := NativePackedByte.Unpack(packed, 0);
        print("test");
    }
}