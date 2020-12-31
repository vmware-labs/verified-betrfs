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
    TestNativePackedUint64.Test_All();
  }

  module TestNativePackedByte
  {
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

  module TestNativePackedUint32
  {
    import opened NativePackedUint32
    import opened NativeTypes
    import opened LinearSequence_s
    import opened CheckUtils

    method Test_All()
    {
      Test_Singles();
      Test_Sequence();
    }

    method Test_Singles()
    {
      linear var s := seq_alloc<byte>(16, 0x41);
      Pack_into_ByteSeq(5, inout s, 0);
      Pack_into_ByteSeq(1255, inout s, 4);
      Pack_into_ByteSeq(0xdeadbeef, inout s, 12);

      var packed := seq_unleash(s);

      var v: uint32 := Unpack(packed, 0);
      Check("index 0", v == 5);

      v := Unpack(packed, 4);
      Check("index 4", v == 1255);

      v := Unpack(packed, 8);
      Check("index 8", v == 0x41414141);

      v := Unpack(packed, 12);
      Check("index 12", v == 0xdeadbeef);
    }

    method Test_Sequence()
    {
      var value :seq<uint32> := [0xb3462e8f, 0x19afee3e, 0x0eb75d9d, 0x56563847];
      linear var packed := seq_alloc<byte>(24, 0x41);
      Pack_Seq_into_ByteSeq(value, inout packed, 4);

      var s := seq_unleash(packed);

      var unpacked: seq<uint32> := Unpack_Seq(s, 4, 2);

      Check("check 1", unpacked[0] == 0xb3462e8f);
      Check("check 2", unpacked[1] == 0x19afee3e);

      unpacked := Unpack_Seq(s, 0, 6);
      Check("check 3", unpacked[0] == 0x41414141);
      Check("check 4", unpacked[1] == 0xb3462e8f);
      Check("check 5", unpacked[2] == 0x19afee3e);
      Check("check 6", unpacked[3] == 0x0eb75d9d);
      Check("check 7", unpacked[4] == 0x56563847);
      Check("check 8", unpacked[5] == 0x41414141);
    }
  }

  module TestNativePackedUint64
  {
    import opened NativePackedUint64
    import opened NativeTypes
    import opened LinearSequence_s
    import opened CheckUtils

    method Test_All()
    {
      Test_Singles();
      Test_Sequence();
    }

    method Test_Singles()
    {
      linear var s := seq_alloc<byte>(32, 0x41);
      Pack_into_ByteSeq(5, inout s, 0);
      Pack_into_ByteSeq(1255, inout s, 8);
      Pack_into_ByteSeq(0x81d842e94716b5c1, inout s, 16);
      var packed := seq_unleash(s);

      var v: uint64 := Unpack(packed, 0);
      Check("index 0", v == 5);

      v := Unpack(packed, 8);
      Check("index 4", v == 1255);

      v := Unpack(packed, 16);
      Check("index 8", v == 0x81d842e94716b5c1);

      v := Unpack(packed, 24);
      Check("index 12", v == 0x4141414141414141);
    }

    method Test_Sequence()
    {
      var value :seq<uint64> := [0x158d8f0982db3937, 0x5610c275aad07b42, 0x7bbbc477ba88a6e1, 0xfcdaee7554619925];
      linear var packed := seq_alloc<byte>(72, 0x41);
      Pack_Seq_into_ByteSeq(value, inout packed, 8);

      var s := seq_unleash(packed);

      var unpacked: seq<uint64> := Unpack_Seq(s, 16, 2);

      Check("check 1", unpacked[0] == 0x5610c275aad07b42);
      Check("check 2", unpacked[1] == 0x7bbbc477ba88a6e1);

      unpacked := Unpack_Seq(s, 0, 4);
      Check("check 3", unpacked[0] == 0x4141414141414141);
      Check("check 4", unpacked[1] == 0x158d8f0982db3937);
      Check("check 5", unpacked[2] == 0x5610c275aad07b42);
      Check("check 6", unpacked[3] == 0x7bbbc477ba88a6e1);
    }
  }
}