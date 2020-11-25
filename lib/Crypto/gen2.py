import sys

def bits64(d):
  s = "[\n"
  for i in range(64):
    s += "true" if (d>>i)&1 else "false"
    if i != 63:
      s += ","
    if i % 8 == 7:
      s += "\n"
    else:
      s += " "
  s += "]"
  return s

#print(bits64(0x00000001493c7d27))

#for i in range(1, 32):
#  print("(x / "+str(2**i)+") % 2,")

def prove(v, i):
  if i == 0:
    return "    assert bits_of_int("+str(v) + ", "+str(i)+") == [];"
  else:
    return ("    assert bits_of_int("+str(v) + ", "+str(i)+") == ["+bool_list(v,0,i)+"] by {\n"
        + prove(v//2, i-1) + "\n"
        + "    assert bits_of_int("+str(v) + ", "+str(i)+") == ["+("true" if v&1 else "false")+"]+bits_of_int("+str(v//2)+", "+str(i-1)+");\n"
    +"    }")

def bit_unrolling_lemma_32(v):
  h = '0x%08x' % v
  return """
  lemma unroll_bits_of_int_32_"""+h+"""()
  ensures bits_of_int("""+h+""", 32) == ["""+bool_list(v,0,32)+"""]
  {
  }
"""

#def prove(v, i):
#  l = ["var a := bits_of_int("+str(v) + ", "+str(i)+");"]
#  for i in range(0, 64):
#    l.append("assert a["+str(i)+"] == "+("true" if v&1 else "false")+";")
#    v = v >> 1
#  return "\n".join(l)

def bool_list(val, i, j):
  s = []
  for k in range(i, j):
    s.append("true" if (val>>k)&1 else "false")
  return ", ".join(s)

def bool_list_s(val, i, j):
  s = []
  for k in range(i, j):
    s.append("[true]" if (val>>k)&1 else "[false]")
  return "+".join(s)

def bool_list_rev(val, i, j):
  s = []
  for k in range(i, j):
    s.append("true" if (val>>k)&1 else "false")
  return ", ".join(s[::-1])

lut = [
    0x00000001493c7d27, 0x493c7d27ba4fc28e, 0xf20c0dfeddc0152b, 0xba4fc28e9e4addf8,
    0x3da6d0cb39d3b296, 0xddc0152b0715ce53, 0x1c291d0447db8317, 0x9e4addf80d3b6092,
    0x740eef02c96cfdc0, 0x39d3b296878a92a7, 0x083a6eecdaece73e, 0x0715ce53ab7aff2a,
    0xc49f4f672162d385, 0x47db831783348832, 0x2ad91c30299847d5, 0x0d3b6092b9e02b86,
    0x6992cea218b33a4e, 0xc96cfdc0b6dd949b, 0x7e90804878d9ccb7, 0x878a92a7bac2fd7b,
    0x1b3d8f29a60ce07b, 0xdaece73ece7f39f4, 0xf1d0f55e61d82e56, 0xab7aff2ad270f1a2,
    0xa87ab8a8c619809d, 0x2162d3852b3cac5d, 0x8462d80065863b64, 0x833488321b03397f,
    0x71d111a8ebb883bd, 0x299847d5b3e32c28, 0xffd852c6064f7f26, 0xb9e02b86dd7e3b0c,
    0xdcb17aa4f285651c, 0x18b33a4e10746f3c, 0xf37c5aeec7a68855, 0xb6dd949b271d9844,
    0x6051d5a28e766a0c, 0x78d9ccb793a5f730, 0x18b0d4ff6cb08e5c, 0xbac2fd7b6b749fb2,
    0x21f3d99c1393e203, 0xa60ce07bcec3662e, 0x8f15801496c515bb, 0xce7f39f4e6fc4e6a,
    0xa00457f78227bb8a, 0x61d82e56b0cd4768, 0x8d6d2c4339c7ff35, 0xd270f1a2d7a4825c,
    0x00ac29cf0ab3844b, 0xc619809d0167d312, 0xe9adf796f6076544, 0x2b3cac5d26f6a60a,
    0x96638b34a741c1bf, 0x65863b6498d8d9cb, 0xe0e9f35149c3cc9c, 0x1b03397f68bce87a,
    0x9af01f2d57a3d037, 0xebb883bd6956fc3b, 0x2cff42cf42d98888, 0xb3e32c283771e98f,
    0x88f25a3ab42ae3d9, 0x064f7f262178513a, 0x4e36f0b0e0ac139e, 0xdd7e3b0c170076fa,
    0xbd6f81f8444dd413, 0xf285651c6f345e45, 0x91c9bd4b41d17b64, 0x10746f3cff0dba97,
    0x885f087ba2b73df1, 0xc7a68855f872e54c, 0x4c1449321e41e9fc, 0x271d984486d8e4d2,
    0x52148f02651bd98b, 0x8e766a0c5bb8f1bc, 0xa3c6f37aa90fd27a, 0x93a5f730b3af077a,
    0xd7c0557f4984d782, 0x6cb08e5cca6ef3ac, 0x63ded06a234e0b26, 0x6b749fb2dd66cbbb,
    0x4d56973c4597456a, 0x1393e203e9e28eb4, 0x9669c9df7b3ff57a, 0xcec3662ec9c8b782,
    0xe417f38a3f70cc6f, 0x96c515bb93e106a4, 0x4b9e0f7162ec6c6d, 0xe6fc4e6ad813b325,
    0xd104b8fc0df04680, 0x8227bb8a2342001e, 0x5b3977300a2a8d7e, 0xb0cd47686d9a4957,
    0xe78eb416e8b6368b, 0x39c7ff35d2c3ed1a, 0x61ff0e01995a5724, 0xd7a4825c9ef68d35,
    0x8d96551c0c139b31, 0x0ab3844bf2271e60, 0x0bf80dd20b0bf8ca, 0x0167d3122664fd8b,
    0x8821abeded64812d, 0xf607654402ee03b2, 0x6a45d2b28604ae0f, 0x26f6a60a363bd6b3,
    0xd8d26619135c83fd, 0xa741c1bf5fabe670, 0xde87806c35ec3279, 0x98d8d9cb00bcf5f6,
    0x143387548ae00689, 0x49c3cc9c17f27698, 0x5bd2011f58ca5f00, 0x68bce87aaa7c7ad5,
    0xdd07448eb5cfca28, 0x57a3d037ded288f8, 0xdde8f5b959f229bc, 0x6956fc3b6d390dec,
    0xa3e3e02c37170390, 0x42d988886353c1cc, 0xd73c7beac4584f5c, 0x3771e98ff48642e9,
    0x80ff0093531377e2, 0xb42ae3d9dd35bc8d, 0x8fe4c34db25b29f2, 0x2178513a9a5ede41,
    0xdf99fc11a563905d, 0xe0ac139e45cddf4e, 0x6c23e841acfa3103, 0x170076faa51b6135,
    0xfe314258dfd94fb2, 0x444dd41380f2886b, 0x0d8373a067969a6a, 0x6f345e45021ac5ef,
    0x19e3635ee8310afa, 0x41d17b6475451b04, 0x29f268b48e1450f7, 0xff0dba97cbbe4ee1,
    0x1dc0632a3a83de21, 0xa2b73df1e0cdcf86, 0x1614f396453c1679, 0xf872e54cdefba41c,
    0x9e2993d3613eee91, 0x1e41e9fcddaf5114, 0x6bebd73c1f1dd124, 0x86d8e4d2bedc6ba1,
    0x63ae91e6eca08ffe, 0x651bd98b3ae30875, 0xf8c9da7a0cd1526a, 0x5bb8f1bcb1630f04,
    0x945a19c1ff47317b, 0xa90fd27ad6c3a807, 0xee8213b79a7781e0, 0xb3af077a63d097e9,
    0x93781dc71d31175f, 0x4984d78294eb256e, 0xccc4a1b913184649, 0xca6ef3ac4be7fd90,
    0xa2c2d9717d5c1d64, 0x234e0b2680ba859a, 0x1cad44526eeed1c9, 0xdd66cbbb22c3799f,
    0x74922601d8ecc578, 0x4597456ab3a6da94, 0xc55f7eabcaf933fe, 0xe9e28eb450bfaade,
    0xa19623292e7d11a7, 0x7b3ff57a7d14748f, 0x2d37074932d8041c, 0xc9c8b782889774e1,
    0x397d84a16cc8a0ff, 0x3f70cc6f5aa1f3cf, 0x791132708a074012, 0x93e106a433bc58b3,
    0xbc8178039f2b002a, 0x62ec6c6dbd0bb25f, 0x88eb3c0760bf0a6a, 0xd813b3258515c07f,
    0x6e4cb6303be3c09b, 0x0df04680d8440525, 0x71971d5c682d085d, 0x2342001e465a4eee,
    0xf33b8bc628b5de82, 0x0a2a8d7e077d54e0, 0x9fb3bbc02e5f3c8c, 0x6d9a4957c00df280,
    0x6ef22b23d0a37f43, 0xe8b6368ba52f58ec, 0xce2df76800712e86, 0xd2c3ed1ad6748e82,
    0xe53a4fc747972100, 0x995a572451aeef66, 0xbe60a91a71900712, 0x9ef68d35359674f7,
    0x1dfa0a15647fbd15, 0x0c139b311baaa809, 0x8ec52396469aef86, 0xf2271e6086d42d06,
    0x0e766b114aba1470, 0x0b0bf8ca1c2cce0a, 0x475846a4aa0cd2d3, 0x2664fd8bf8448640,
    0xb2a3dfa6ac4fcdec, 0xed64812de81cf154, 0xdc1a160cc2c7385c, 0x02ee03b295ffd7dc,
    0x79afdf1c91de6176, 0x8604ae0f84ee89ac, 0x07ac6e46533e308d, 0x363bd6b35f0e0438,
    0x15f85253604d6e09, 0x135c83fdaeb3e622, 0x1bec24dd4263eb04, 0x5fabe67050c2cb16,
    0x4c36cd5b6667afe7, 0x35ec32791a6889b8, 0xe0a22e29de42c92a, 0x00bcf5f67f47463d,
    0x7c2b6ed9b82b6080, 0x8ae00689828d550b, 0x06ff88fddca2b4da, 0x17f276984ac726eb,
    0xf7317cf0529295e6, 0x58ca5f005e9f28eb, 0x61b6e40b40c14fff, 0xaa7c7ad596a1f19b,
    0xde8a97f8997157e1, 0xb5cfca28b0ed8196, 0x88f61445097e41e6, 0xded288f84ce8bfe5,
    0xd4520e9ee36841ad, 0x59f229bcd1a9427c, 0x0c592bd593f3319c, 0x6d390decb58ac6fe,
    0x38edfaf3e3809241, 0x37170390f22fd3e2, 0x72cbfcdb83c2df88, 0x6353c1ccd6b1825a,
    0x348331a54e4ff232, 0xc4584f5c6664d9c1, 0xc3977c19836b5a6e, 0xf48642e923d5e7e5,
    0xdafaea7c65065343, 0x531377e21495d20d, 0x73db4c04a29c82eb, 0xdd35bc8df370b37f,
    0x72675ce8ea6dd7dc, 0xb25b29f2e9415bce, 0x3ec2ff8396309b0f, 0x9a5ede41c776b648,
    0xe8c7a017c22c52c5, 0xa563905dcecfcd43, 0xcf4bfaefd8311ee7, 0x45cddf4e24e6fe8f,
    0x6bde1ac7d0c6d7c9, 0xacfa310345aa5d4a, 0xae1175c2cf067065, 0xa51b613582f89c77,
    0x0
  ]

def entry_lemma_old(i):
  val = lut[i]

  i = i + 1

  return """
  lemma lut_entry_"""+str(i-1)+"""()
  ensures bits_of_int(lut["""+str(i-1)+"""] as int, 64)
      == pow_mod_crc("""+str(128*i)+""") + pow_mod_crc("""+str(64*i)+""")
  {
    var a0 := ["""+bool_list(val, 0, 8)+"""];
    var a1 := ["""+bool_list(val, 8, 16)+"""];
    var a2 := ["""+bool_list(val, 16, 24)+"""];
    var a3 := ["""+bool_list(val, 24, 32)+"""];
    var a4 := ["""+bool_list(val, 32, 40)+"""];
    var a5 := ["""+bool_list(val, 40, 48)+"""];
    var a6 := ["""+bool_list(val, 48, 56)+"""];
    var a7 := ["""+bool_list(val, 56, 64)+"""];
    calc {
      bits_of_int(lut["""+str(i-1)+"""] as int, 64);
      bits_of_int("""+str(val)+""", 64);
      a0 + bits_of_int("""+str(val>>8)+""", 56);
      {
        assert bits_of_int("""+str(val>>8)+""", 56)
            == a1 + bits_of_int("""+str(val>>16)+""", 48);
      }
      a0 + a1 + bits_of_int("""+str(val>>16)+""", 48);
      {
        assert bits_of_int("""+str(val>>16)+""", 48)
            == a2 + bits_of_int("""+str(val>>24)+""", 40);
      }
      a0 + a1 + a2 + bits_of_int("""+str(val>>24)+""", 40);
      {
        assert bits_of_int("""+str(val>>24)+""", 40)
            == a3 + bits_of_int("""+str(val>>32)+""", 32);
      }
      a0 + a1 + a2 + a3 + bits_of_int("""+str(val>>32)+""", 32);
      {
        assert bits_of_int("""+str(val>>32)+""", 32)
            == a4 + bits_of_int("""+str(val>>40)+""", 24);
      }
      a0 + a1 + a2 + a3 + a4 + bits_of_int("""+str(val>>40)+""", 24);
      {
        assert bits_of_int("""+str(val>>40)+""", 24)
            == a5 + bits_of_int("""+str(val>>48)+""", 16);
      }
      a0 + a1 + a2 + a3 + a4 + a5 + bits_of_int("""+str(val>>48)+""", 16);
      {
        assert bits_of_int("""+str(val>>48)+""", 16)
            == a6 + bits_of_int("""+str(val>>56)+""", 8);
      }
      a0 + a1 + a2 + a3 + a4 + a5 + a6 + bits_of_int("""+str(val>>56)+""", 8);
      {
        assert bits_of_int("""+str(val>>56)+""", 8)
            == a7;
      }
      a0 + a1 + a2 + a3 + a4 + a5 + a6 + a7;
      ["""+bool_list(val,0,32)+"""]+["""+bool_list(val,32,64)+"""];
      {
        calc {
          ["""+bool_list(val,0,32)+"""];
          {
            pow_"""+str(128*i-33)+"""();
            of_pow("""+str(128*i)+""", """+bool_list_rev(val,0, 32)+""");
          }
          pow_mod_crc("""+str(128*i)+""");
        }
        calc {
          ["""+bool_list(val,32,64)+"""];
          {
            pow_"""+str(64*i-33)+"""();
            of_pow("""+str(64*i)+""", """+bool_list_rev(val,32, 64)+""");
          }
          pow_mod_crc("""+str(64*i)+""");
        }
      }
      pow_mod_crc("""+str(128*i)+""") + pow_mod_crc("""+str(64*i)+""");
    }
  }

"""

def entry_lemma(i):
  val = lut[i]

  i = i + 1

  def step_lines():
    lines = []
    v = val
    for j in range(64,1,-1):
      lines.append("assert bits_of_int("+str(v)+", "+str(j)+") == ["+("true" if v&1 else "false")+"] + bits_of_int("+str(v//2)+", "+str(j-1)+");")
      v = v // 2
    lines.append("assert bits_of_int(0, 0) == [];")
    return lines

  return """
  lemma lut_entry_"""+str(i-1)+"""()
  ensures bits_of_int(lut["""+str(i-1)+"""] as int, 64)
      == pow_mod_crc("""+str(128*i)+""") + pow_mod_crc("""+str(64*i)+""")
  {
    calc {
      bits_of_int(lut["""+str(i-1)+"""] as int, 64);
      bits_of_int("""+str(val)+""", 64);
      {
        lemma_bits_of_int_64_split("""+str(val)+""");
      }
      bits_of_int("""+str(val&0xffffffff)+""", 32) + bits_of_int("""+str(val>>32)+""", 32);
      {
        unroll_bits_of_int_32_"""+str('0x%08x' % (val&0xffffffff))+"""();
        unroll_bits_of_int_32_"""+str('0x%08x' % (val>>32))+"""();
      }
      ["""+bool_list(val,0,32)+"""]+["""+bool_list(val,32,64)+"""];
      {
        calc {
          ["""+bool_list(val,0,32)+"""];
          {
            pow_"""+str(128*i-33)+"""();
            of_pow("""+str(128*i)+""", """+bool_list_rev(val,0, 32)+""");
          }
          pow_mod_crc("""+str(128*i)+""");
        }
        calc {
          ["""+bool_list(val,32,64)+"""];
          {
            pow_"""+str(64*i-33)+"""();
            of_pow("""+str(64*i)+""", """+bool_list_rev(val,32, 64)+""");
          }
          pow_mod_crc("""+str(64*i)+""");
        }
      }
      pow_mod_crc("""+str(128*i)+""") + pow_mod_crc("""+str(64*i)+""");
    }
  }

"""



def unrolling_lemmas():
  print("""include "Bits.s.dfy"

module CRC32LutBitUnrolling {
  import opened NativeTypes
  import opened Bits_s

""")

  s = set()
  for l in lut:
    if l != 0:
      s.add(l >> 32)
      s.add(l & 0xffffffff)
  for l in s:
    print(bit_unrolling_lemma_32(l))

  print("\n}")

def main():
  print("""include "../Lang/NativeTypes.s.dfy"
include "F2_X.s.dfy"
include "CRC32LutPowers.i.dfy"
include "CRC32LutLemma.i.dfy"
include "CRC32LutBitUnrolling.i.dfy"

module CRC32_C_Lut {
  export Spec provides lut, lut_entries, NativeTypes, Bits_s, F2_X_s, CRC32_C_Lut_Lemma
  export extends Spec

  import opened NativeTypes
  import opened F2_X_s
  import opened Bits_s
  import opened CRC32_C_Lut_Powers
  import opened CRC32_C_Lut_Lemma
  import opened CRC32LutBitUnrolling

  const lut0: seq<uint64> := [
    0x00000001493c7d27, 0x493c7d27ba4fc28e, 0xf20c0dfeddc0152b, 0xba4fc28e9e4addf8,
    0x3da6d0cb39d3b296, 0xddc0152b0715ce53, 0x1c291d0447db8317, 0x9e4addf80d3b6092,
    0x740eef02c96cfdc0, 0x39d3b296878a92a7, 0x083a6eecdaece73e, 0x0715ce53ab7aff2a,
    0xc49f4f672162d385, 0x47db831783348832, 0x2ad91c30299847d5, 0x0d3b6092b9e02b86,
    0x6992cea218b33a4e, 0xc96cfdc0b6dd949b, 0x7e90804878d9ccb7, 0x878a92a7bac2fd7b,
    0x1b3d8f29a60ce07b, 0xdaece73ece7f39f4, 0xf1d0f55e61d82e56, 0xab7aff2ad270f1a2,
    0xa87ab8a8c619809d, 0x2162d3852b3cac5d, 0x8462d80065863b64, 0x833488321b03397f,
    0x71d111a8ebb883bd, 0x299847d5b3e32c28, 0xffd852c6064f7f26, 0xb9e02b86dd7e3b0c
  ]
  const lut1: seq<uint64> := [
    0xdcb17aa4f285651c, 0x18b33a4e10746f3c, 0xf37c5aeec7a68855, 0xb6dd949b271d9844,
    0x6051d5a28e766a0c, 0x78d9ccb793a5f730, 0x18b0d4ff6cb08e5c, 0xbac2fd7b6b749fb2,
    0x21f3d99c1393e203, 0xa60ce07bcec3662e, 0x8f15801496c515bb, 0xce7f39f4e6fc4e6a,
    0xa00457f78227bb8a, 0x61d82e56b0cd4768, 0x8d6d2c4339c7ff35, 0xd270f1a2d7a4825c,
    0x00ac29cf0ab3844b, 0xc619809d0167d312, 0xe9adf796f6076544, 0x2b3cac5d26f6a60a,
    0x96638b34a741c1bf, 0x65863b6498d8d9cb, 0xe0e9f35149c3cc9c, 0x1b03397f68bce87a,
    0x9af01f2d57a3d037, 0xebb883bd6956fc3b, 0x2cff42cf42d98888, 0xb3e32c283771e98f,
    0x88f25a3ab42ae3d9, 0x064f7f262178513a, 0x4e36f0b0e0ac139e, 0xdd7e3b0c170076fa
  ]
  const lut2: seq<uint64> := [
    0xbd6f81f8444dd413, 0xf285651c6f345e45, 0x91c9bd4b41d17b64, 0x10746f3cff0dba97,
    0x885f087ba2b73df1, 0xc7a68855f872e54c, 0x4c1449321e41e9fc, 0x271d984486d8e4d2,
    0x52148f02651bd98b, 0x8e766a0c5bb8f1bc, 0xa3c6f37aa90fd27a, 0x93a5f730b3af077a,
    0xd7c0557f4984d782, 0x6cb08e5cca6ef3ac, 0x63ded06a234e0b26, 0x6b749fb2dd66cbbb,
    0x4d56973c4597456a, 0x1393e203e9e28eb4, 0x9669c9df7b3ff57a, 0xcec3662ec9c8b782,
    0xe417f38a3f70cc6f, 0x96c515bb93e106a4, 0x4b9e0f7162ec6c6d, 0xe6fc4e6ad813b325,
    0xd104b8fc0df04680, 0x8227bb8a2342001e, 0x5b3977300a2a8d7e, 0xb0cd47686d9a4957,
    0xe78eb416e8b6368b, 0x39c7ff35d2c3ed1a, 0x61ff0e01995a5724, 0xd7a4825c9ef68d35
  ]
  const lut3: seq<uint64> := [
    0x8d96551c0c139b31, 0x0ab3844bf2271e60, 0x0bf80dd20b0bf8ca, 0x0167d3122664fd8b,
    0x8821abeded64812d, 0xf607654402ee03b2, 0x6a45d2b28604ae0f, 0x26f6a60a363bd6b3,
    0xd8d26619135c83fd, 0xa741c1bf5fabe670, 0xde87806c35ec3279, 0x98d8d9cb00bcf5f6,
    0x143387548ae00689, 0x49c3cc9c17f27698, 0x5bd2011f58ca5f00, 0x68bce87aaa7c7ad5,
    0xdd07448eb5cfca28, 0x57a3d037ded288f8, 0xdde8f5b959f229bc, 0x6956fc3b6d390dec,
    0xa3e3e02c37170390, 0x42d988886353c1cc, 0xd73c7beac4584f5c, 0x3771e98ff48642e9,
    0x80ff0093531377e2, 0xb42ae3d9dd35bc8d, 0x8fe4c34db25b29f2, 0x2178513a9a5ede41,
    0xdf99fc11a563905d, 0xe0ac139e45cddf4e, 0x6c23e841acfa3103, 0x170076faa51b6135
  ]
  const lut4: seq<uint64> := [
    0xfe314258dfd94fb2, 0x444dd41380f2886b, 0x0d8373a067969a6a, 0x6f345e45021ac5ef,
    0x19e3635ee8310afa, 0x41d17b6475451b04, 0x29f268b48e1450f7, 0xff0dba97cbbe4ee1,
    0x1dc0632a3a83de21, 0xa2b73df1e0cdcf86, 0x1614f396453c1679, 0xf872e54cdefba41c,
    0x9e2993d3613eee91, 0x1e41e9fcddaf5114, 0x6bebd73c1f1dd124, 0x86d8e4d2bedc6ba1,
    0x63ae91e6eca08ffe, 0x651bd98b3ae30875, 0xf8c9da7a0cd1526a, 0x5bb8f1bcb1630f04,
    0x945a19c1ff47317b, 0xa90fd27ad6c3a807, 0xee8213b79a7781e0, 0xb3af077a63d097e9,
    0x93781dc71d31175f, 0x4984d78294eb256e, 0xccc4a1b913184649, 0xca6ef3ac4be7fd90,
    0xa2c2d9717d5c1d64, 0x234e0b2680ba859a, 0x1cad44526eeed1c9, 0xdd66cbbb22c3799f
  ]
  const lut5: seq<uint64> := [
    0x74922601d8ecc578, 0x4597456ab3a6da94, 0xc55f7eabcaf933fe, 0xe9e28eb450bfaade,
    0xa19623292e7d11a7, 0x7b3ff57a7d14748f, 0x2d37074932d8041c, 0xc9c8b782889774e1,
    0x397d84a16cc8a0ff, 0x3f70cc6f5aa1f3cf, 0x791132708a074012, 0x93e106a433bc58b3,
    0xbc8178039f2b002a, 0x62ec6c6dbd0bb25f, 0x88eb3c0760bf0a6a, 0xd813b3258515c07f,
    0x6e4cb6303be3c09b, 0x0df04680d8440525, 0x71971d5c682d085d, 0x2342001e465a4eee,
    0xf33b8bc628b5de82, 0x0a2a8d7e077d54e0, 0x9fb3bbc02e5f3c8c, 0x6d9a4957c00df280,
    0x6ef22b23d0a37f43, 0xe8b6368ba52f58ec, 0xce2df76800712e86, 0xd2c3ed1ad6748e82,
    0xe53a4fc747972100, 0x995a572451aeef66, 0xbe60a91a71900712, 0x9ef68d35359674f7
  ]
  const lut6: seq<uint64> := [
    0x1dfa0a15647fbd15, 0x0c139b311baaa809, 0x8ec52396469aef86, 0xf2271e6086d42d06,
    0x0e766b114aba1470, 0x0b0bf8ca1c2cce0a, 0x475846a4aa0cd2d3, 0x2664fd8bf8448640,
    0xb2a3dfa6ac4fcdec, 0xed64812de81cf154, 0xdc1a160cc2c7385c, 0x02ee03b295ffd7dc,
    0x79afdf1c91de6176, 0x8604ae0f84ee89ac, 0x07ac6e46533e308d, 0x363bd6b35f0e0438,
    0x15f85253604d6e09, 0x135c83fdaeb3e622, 0x1bec24dd4263eb04, 0x5fabe67050c2cb16,
    0x4c36cd5b6667afe7, 0x35ec32791a6889b8, 0xe0a22e29de42c92a, 0x00bcf5f67f47463d,
    0x7c2b6ed9b82b6080, 0x8ae00689828d550b, 0x06ff88fddca2b4da, 0x17f276984ac726eb,
    0xf7317cf0529295e6, 0x58ca5f005e9f28eb, 0x61b6e40b40c14fff, 0xaa7c7ad596a1f19b
  ]
  const lut7: seq<uint64> := [
    0xde8a97f8997157e1, 0xb5cfca28b0ed8196, 0x88f61445097e41e6, 0xded288f84ce8bfe5,
    0xd4520e9ee36841ad, 0x59f229bcd1a9427c, 0x0c592bd593f3319c, 0x6d390decb58ac6fe,
    0x38edfaf3e3809241, 0x37170390f22fd3e2, 0x72cbfcdb83c2df88, 0x6353c1ccd6b1825a,
    0x348331a54e4ff232, 0xc4584f5c6664d9c1, 0xc3977c19836b5a6e, 0xf48642e923d5e7e5,
    0xdafaea7c65065343, 0x531377e21495d20d, 0x73db4c04a29c82eb, 0xdd35bc8df370b37f,
    0x72675ce8ea6dd7dc, 0xb25b29f2e9415bce, 0x3ec2ff8396309b0f, 0x9a5ede41c776b648,
    0xe8c7a017c22c52c5, 0xa563905dcecfcd43, 0xcf4bfaefd8311ee7, 0x45cddf4e24e6fe8f,
    0x6bde1ac7d0c6d7c9, 0xacfa310345aa5d4a, 0xae1175c2cf067065, 0xa51b613582f89c77,
    0x0
  ]

  const lut: seq<uint64> := lut0 + lut1 + lut2 + lut3 + lut4 + lut5 + lut6 + lut7

""")

  for i in range(256):
    print(entry_lemma(i))

  print("""  lemma {:fuel bits_of_int,0} {:fuel pow_mod_crc,0} lut_entries(n: nat)
  requires 1 <= n <= 256
  ensures |lut| == 257
  ensures bits_of_int(lut[n-1] as int, 64) == pow_mod_crc(2*64*n) + pow_mod_crc(64*n)
  {""")

  for i in range(1,256+1):
    if i == 1:
      print("    if n == " + str(i) + " { lut_entry_" + str(i-1) + "(); }")
    else:
      print("    else if n == " + str(i) + " { lut_entry_" + str(i-1) + "(); }")
    
  print("""  }\n}""")

if sys.argv[1] == "main":
  main()
elif sys.argv[1] == "unrolling":
  unrolling_lemmas()
else:
  assert False
