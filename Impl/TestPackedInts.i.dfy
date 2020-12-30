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
      print name, ": expected\n";
    } else {
      print name, ": *** UNEXPECTED *** !!!!\n";
    }
  }

  method TestNativePackedByte()
  {
    TestUnpack();
    TestPack_into_ByteSeq();
    TestUnpack_Seq();
  }

  method TestUnpack()
  {
    var packed : seq<byte> := [1, 2, 3];
    var v := Unpack(packed, 0);
    Test("index 0", v == 1);
    v := Unpack(packed, 2);
    Test("index 1", v == 2);
  }

  method TestPack_into_ByteSeq()
  {
    linear var s := seq_alloc<byte>(10, 41);
    Pack_into_ByteSeq(5, inout s, 0);
    Pack_into_ByteSeq(255, inout s, 2);

    Test("index 0", seq_get(s, 0) == 5);
    Test("index 1", seq_get(s, 1) == 41);
    Test("index 2", seq_get(s, 2) == 255);

    var _ := seq_free(s);
  }

  method TestUnpack_Seq()
  {
    var packed : seq<byte> := [1, 2, 3];
    var unpacked: seq<uint8> := Unpack_Seq(packed, 1, 2);
    Test("index 0", unpacked[0] == 2);
    Test("index 1", unpacked[1] == 3);

    Test("index 0", packed[0] == 1);
    Test("index 1", packed[1] == 2);
  }
}