include "../lib/Lang/System/PackedInts.s.dfy"
include "../lib/Lang/LinearSequence.s.dfy"


module TestPackedInts {

  module CheckUtils {
    method Check(name:string, b:bool) 
    // requires b;
    {
      if b {
        print name, ": expected\n";
      } else {
        print name, ": *** UNEXPECTED *** !!!!\n";
      }
    }
  }

  method TestPackedInts()
  {
    TestNativePackedByte.Test_All();
    TestNativePackedUint32.Test_All();
  }

  module TestNativePackedByte {
    import opened NativePackedByte
    import opened NativeTypes
    import opened LinearSequence_s
    import opened CheckUtils

    method Test_All()
    {
      Test_Unpack();
      Test_Pack_into_ByteSeq();
      Test_Unpack_Seq();
      Test_Pack_Seq_into_ByteSeq();
    }

    method Test_Unpack()
    {
      var packed : seq<byte> := [1, 2, 3];
      var v := Unpack(packed, 0);
      Check("index 0", v == 1);
      v := Unpack(packed, 2);
      Check("index 1", v == 3);
    }

    method Test_Pack_into_ByteSeq()
    {
      linear var s := seq_alloc<byte>(10, 41);
      Pack_into_ByteSeq(5, inout s, 0);
      Pack_into_ByteSeq(255, inout s, 2);

      Check("index 0", seq_get(s, 0) == 5);
      Check("index 1", seq_get(s, 1) == 41);
      Check("index 2", seq_get(s, 2) == 255);

      var _ := seq_free(s);
    }

    method Test_Unpack_Seq()
    {
      var packed : seq<byte> := [1, 2, 3];
      var unpacked: seq<uint8> := Unpack_Seq(packed, 1, 2);

      Check("index 0", packed[0] == 1);
      Check("index 1", packed[1] == 2);

      Check("index 0", unpacked[0] == 2);
      Check("index 1", unpacked[1] == 3);
    }

    method Test_Pack_Seq_into_ByteSeq()
    {
      var value :seq<byte> := [22, 33, 24];
      linear var packed := seq_alloc<byte>(10, 41);
      Pack_Seq_into_ByteSeq(value, inout packed, 4);

      Check("index 0", seq_get(packed, 0) == 41);
      Check("index 4", seq_get(packed, 4) == 22);

      var _ := seq_free(packed);
    }
  }

  module TestNativePackedUint32 {
    import opened NativePackedByte
    import opened NativeTypes
    import opened LinearSequence_s
    import opened CheckUtils

    method Test_All()
    {
      Test_Singles();
      // Test_Sequence();
      // Test_Unpack_Seq();
      // Test_Pack_Seq_into_ByteSeq();
    }

    method Test_Singles() {
      linear var s := seq_alloc<byte>(16, 0x41);
      Pack_into_ByteSeq(5, inout s, 0);
      Pack_into_ByteSeq(255, inout s, 4);
      Pack_into_ByteSeq(0xdeadbeef, inout s, 12);

      var packed := seq_unleash(s);

      var v := Unpack(packed, 0);
      Check("index 0", v == 5);

      v := Unpack(packed, 4);
      Check("index 4", v == 255);

      v := Unpack(packed, 8);
      Check("index 8", v == 0x41414141);

      v := Unpack(packed, 12);
      Check("index 12", v == 0xdeadbeef);
    }
  }
}