include "../lib/Lang/System/PackedInts.s.dfy"
include "../lib/Lang/LinearSequence.s.dfy"

module TestPackedInts {

  import opened NativePackedByte
  import opened NativeTypes
  import opened LinearSequence_s

  method Test(name:string, b:bool) 
  requires b;
  {
    if b {
        print name, ": This is expected\n";
    } else {
        print name, ": This is *** UNEXPECTED *** !!!!\n";
    }
  }

  method TestNativePackedByte()
  {
    var packed : seq<byte> := [1, 2, 3];
    var i := Unpack(packed, 0);
    // print "test", i;

    linear var s := seq_alloc<byte>(10, 41);
    Pack_into_ByteSeq(5, inout s, 0);

    Test("Test result of set", seq_get(s, 0) == 5);
    Test("Test result of set", seq_get(s, 1) == 41);

    var _ := seq_free(s);
  }
}