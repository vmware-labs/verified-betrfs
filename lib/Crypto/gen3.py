def all256():
  N = 256
  for z in range(256, 1, -1):
    if z == 256:
      print("""
          assert A"""+str(z)+""": crcA == iterated_intrinsic(data, pA as int, old_crcA, """+str(z)+""", 256);
          assert B"""+str(z)+""": crcB == iterated_intrinsic(data, pB as int, 0,        """+str(z)+""", 256);
          assert C"""+str(z)+""": crcC == iterated_intrinsic(data, pC as int, 0,        """+str(z)+""", 256);
  """)
    else:
      print("""
          assert """+("{:split_here}" if (z%8 == 1) else "") + """ A"""+str(z)+""": crcA == iterated_intrinsic(data, pA as int, old_crcA, """+str(z)+""", 256) by { reveal A"""+str(z+1)+"""; }
          assert B"""+str(z)+""": crcB == iterated_intrinsic(data, pB as int, 0,        """+str(z)+""", 256) by { reveal B"""+str(z+1)+"""; }
          assert C"""+str(z)+""": crcC == iterated_intrinsic(data, pC as int, 0,        """+str(z)+""", 256) by { reveal C"""+str(z+1)+"""; }
  """)

    print("""
          a := Unpack_LittleEndian_Uint64(data, pA - """ + str(8*z) + """ as uint64);
          crcA := intrinsic_mm_crc32_u64(crcA, a);
          b := Unpack_LittleEndian_Uint64(data, pB - """ + str(8*z) + """ as uint64);
          crcB := intrinsic_mm_crc32_u64(crcB, b);
          c := Unpack_LittleEndian_Uint64(data, pC - """ + str(8*z) + """ as uint64);
          crcC := intrinsic_mm_crc32_u64(crcC, c);
  """)

  print("""
          assert crcA == iterated_intrinsic(data, pA as int, old_crcA, """+str(1)+""", 256);
          assert crcB == iterated_intrinsic(data, pB as int, 0,        """+str(1)+""", 256);
          assert crcC == iterated_intrinsic(data, pC as int, 0,        """+str(1)+""", 256);
  """)

def do_subroutine(b, a):
  print("  method {:fuel mm_crc32_u64,0} subroutine_from_" + str(b) + "_to_" + str(a) + "(data: seq<byte>, pA: uint64, pB: uint64, pC: uint64, crcA: uint64, crcB: uint64, crcC: uint64, ghost old_crcA: uint64)")
  print("""  returns (crcA' : uint64, crcB' : uint64, crcC' : uint64)
  requires 0 <= crcA < 0x1_0000_0000
  requires 0 <= crcB < 0x1_0000_0000
  requires 0 <= crcC < 0x1_0000_0000
  requires 256*8 <= pA
  requires pA as int <= pB as int <= pC as int <= |data| < 0x1_0000_0000_0000_0000
  requires crcA == iterated_intrinsic(data, pA as int, old_crcA, """+str(b)+""", 256)
  requires crcB == iterated_intrinsic(data, pB as int, 0, """+str(b)+""", 256)
  requires crcC == iterated_intrinsic(data, pC as int, 0, """+str(b)+""", 256)
  ensures 0 <= crcA < 0x1_0000_0000
  ensures 0 <= crcB < 0x1_0000_0000
  ensures 0 <= crcC < 0x1_0000_0000
  ensures crcA' == iterated_intrinsic(data, pA as int, old_crcA, """+str(a)+""", 256)
  ensures crcB' == iterated_intrinsic(data, pB as int, 0, """+str(a)+""", 256)
  ensures crcC' == iterated_intrinsic(data, pC as int, 0, """+str(a)+""", 256)
  {
    var a, b, c;
    crcA' := crcA;
    crcB' := crcB;
    crcC' := crcC;""")
  for z in range(b, a, -1):
    print("""
    a := Unpack_LittleEndian_Uint64(data, pA - """ + str(8*z) + """ as uint64);
    crcA' := intrinsic_mm_crc32_u64(crcA', a);
    b := Unpack_LittleEndian_Uint64(data, pB - """ + str(8*z) + """ as uint64);
    crcB' := intrinsic_mm_crc32_u64(crcB', b);
    c := Unpack_LittleEndian_Uint64(data, pC - """ + str(8*z) + """ as uint64);
    crcC' := intrinsic_mm_crc32_u64(crcC', c);""")
    if z != a + 1:
      print("""
    assert crcA' == iterated_intrinsic(data, pA as int, old_crcA, """+str(z-1)+""", 256);
    assert crcB' == iterated_intrinsic(data, pB as int, 0,        """+str(z-1)+""", 256);
    assert crcC' == iterated_intrinsic(data, pC as int, 0,        """+str(z-1)+""", 256);""")
  print("  }")

def do_full():
  b = 256
  a = 1
  print("  method {:fuel mm_crc32_u64,0} subroutine_from_" + str(b) + "_to_" + str(a) + "(data: seq<byte>, pA: uint64, pB: uint64, pC: uint64, crcA: uint64, crcB: uint64, crcC: uint64, ghost old_crcA: uint64)")
  print("""  returns (crcA' : uint64, crcB' : uint64, crcC' : uint64)
  requires 0 <= crcA < 0x1_0000_0000
  requires 0 <= crcB < 0x1_0000_0000
  requires 0 <= crcC < 0x1_0000_0000
  requires 256*8 <= pA
  requires pA as int <= pB as int <= pC as int <= |data| < 0x1_0000_0000_0000_0000
  requires crcA == iterated_intrinsic(data, pA as int, old_crcA, """+str(b)+""", 256)
  requires crcB == iterated_intrinsic(data, pB as int, 0, """+str(b)+""", 256)
  requires crcC == iterated_intrinsic(data, pC as int, 0, """+str(b)+""", 256)
  ensures 0 <= crcA < 0x1_0000_0000
  ensures 0 <= crcB < 0x1_0000_0000
  ensures 0 <= crcC < 0x1_0000_0000
  ensures crcA' == iterated_intrinsic(data, pA as int, old_crcA, """+str(a)+""", 256)
  ensures crcB' == iterated_intrinsic(data, pB as int, 0, """+str(a)+""", 256)
  ensures crcC' == iterated_intrinsic(data, pC as int, 0, """+str(a)+""", 256)
  {
    crcA' := crcA;
    crcB' := crcB;
    crcC' := crcC;""")

  for chunk in range(15, -1, -1):
    a = chunk*16
    b = a + 16
    if chunk == 0:
      a = 1
    print("    crcA', crcB', crcC' := subroutine_from_"+str(b)+"_to_"+str(a)+"(data, pA, pB, pC, crcA', crcB', crcC', old_crcA);")
  print("  }")

for chunk in range(0, 16):
  a = chunk*16
  b = a + 16
  if chunk == 0:
    a = 1

  do_subroutine(b, a)

do_full()
