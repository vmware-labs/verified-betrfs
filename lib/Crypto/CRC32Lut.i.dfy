include "../Lang/NativeTypes.s.dfy"
include "../Lang/System/F2_X.s.dfy"
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



  lemma lut_entry_0()
  ensures bits_of_int(lut[0] as int, 64)
      == pow_mod_crc(128) + pow_mod_crc(64)
  {
    calc {
      bits_of_int(lut[0] as int, 64);
      bits_of_int(5523668263, 64);
      {
        lemma_bits_of_int_64_split(5523668263);
      }
      bits_of_int(1228700967, 32) + bits_of_int(1, 32);
      {
        unroll_bits_of_int_32_0x493c7d27();
        unroll_bits_of_int_32_0x00000001();
      }
      [true, true, true, false, false, true, false, false, true, false, true, true, true, true, true, false, false, false, true, true, true, true, false, false, true, false, false, true, false, false, true, false]+[true, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false];
      {
        calc {
          [true, true, true, false, false, true, false, false, true, false, true, true, true, true, true, false, false, false, true, true, true, true, false, false, true, false, false, true, false, false, true, false];
          {
            pow_95();
            of_pow(128, false, true, false, false, true, false, false, true, false, false, true, true, true, true, false, false, false, true, true, true, true, true, false, true, false, false, true, false, false, true, true, true);
          }
          pow_mod_crc(128);
        }
        calc {
          [true, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false];
          {
            pow_31();
            of_pow(64, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, true);
          }
          pow_mod_crc(64);
        }
      }
      pow_mod_crc(128) + pow_mod_crc(64);
    }
  }



  lemma lut_entry_1()
  ensures bits_of_int(lut[1] as int, 64)
      == pow_mod_crc(256) + pow_mod_crc(128)
  {
    calc {
      bits_of_int(lut[1] as int, 64);
      bits_of_int(5277230472954364558, 64);
      {
        lemma_bits_of_int_64_split(5277230472954364558);
      }
      bits_of_int(3125789326, 32) + bits_of_int(1228700967, 32);
      {
        unroll_bits_of_int_32_0xba4fc28e();
        unroll_bits_of_int_32_0x493c7d27();
      }
      [false, true, true, true, false, false, false, true, false, true, false, false, false, false, true, true, true, true, true, true, false, false, true, false, false, true, false, true, true, true, false, true]+[true, true, true, false, false, true, false, false, true, false, true, true, true, true, true, false, false, false, true, true, true, true, false, false, true, false, false, true, false, false, true, false];
      {
        calc {
          [false, true, true, true, false, false, false, true, false, true, false, false, false, false, true, true, true, true, true, true, false, false, true, false, false, true, false, true, true, true, false, true];
          {
            pow_223();
            of_pow(256, true, false, true, true, true, false, true, false, false, true, false, false, true, true, true, true, true, true, false, false, false, false, true, false, true, false, false, false, true, true, true, false);
          }
          pow_mod_crc(256);
        }
        calc {
          [true, true, true, false, false, true, false, false, true, false, true, true, true, true, true, false, false, false, true, true, true, true, false, false, true, false, false, true, false, false, true, false];
          {
            pow_95();
            of_pow(128, false, true, false, false, true, false, false, true, false, false, true, true, true, true, false, false, false, true, true, true, true, true, false, true, false, false, true, false, false, true, true, true);
          }
          pow_mod_crc(128);
        }
      }
      pow_mod_crc(256) + pow_mod_crc(128);
    }
  }



  lemma lut_entry_2()
  ensures bits_of_int(lut[2] as int, 64)
      == pow_mod_crc(384) + pow_mod_crc(192)
  {
    calc {
      bits_of_int(lut[2] as int, 64);
      bits_of_int(17441330845192295723, 64);
      {
        lemma_bits_of_int_64_split(17441330845192295723);
      }
      bits_of_int(3720353067, 32) + bits_of_int(4060876286, 32);
      {
        unroll_bits_of_int_32_0xddc0152b();
        unroll_bits_of_int_32_0xf20c0dfe();
      }
      [true, true, false, true, false, true, false, false, true, false, true, false, true, false, false, false, false, false, false, false, false, false, true, true, true, false, true, true, true, false, true, true]+[false, true, true, true, true, true, true, true, true, false, true, true, false, false, false, false, false, false, true, true, false, false, false, false, false, true, false, false, true, true, true, true];
      {
        calc {
          [true, true, false, true, false, true, false, false, true, false, true, false, true, false, false, false, false, false, false, false, false, false, true, true, true, false, true, true, true, false, true, true];
          {
            pow_351();
            of_pow(384, true, true, false, true, true, true, false, true, true, true, false, false, false, false, false, false, false, false, false, true, false, true, false, true, false, false, true, false, true, false, true, true);
          }
          pow_mod_crc(384);
        }
        calc {
          [false, true, true, true, true, true, true, true, true, false, true, true, false, false, false, false, false, false, true, true, false, false, false, false, false, true, false, false, true, true, true, true];
          {
            pow_159();
            of_pow(192, true, true, true, true, false, false, true, false, false, false, false, false, true, true, false, false, false, false, false, false, true, true, false, true, true, true, true, true, true, true, true, false);
          }
          pow_mod_crc(192);
        }
      }
      pow_mod_crc(384) + pow_mod_crc(192);
    }
  }



  lemma lut_entry_3()
  ensures bits_of_int(lut[3] as int, 64)
      == pow_mod_crc(512) + pow_mod_crc(256)
  {
    calc {
      bits_of_int(lut[3] as int, 64);
      bits_of_int(13425162932011589112, 64);
      {
        lemma_bits_of_int_64_split(13425162932011589112);
      }
      bits_of_int(2655706616, 32) + bits_of_int(3125789326, 32);
      {
        unroll_bits_of_int_32_0x9e4addf8();
        unroll_bits_of_int_32_0xba4fc28e();
      }
      [false, false, false, true, true, true, true, true, true, false, true, true, true, false, true, true, false, true, false, true, false, false, true, false, false, true, true, true, true, false, false, true]+[false, true, true, true, false, false, false, true, false, true, false, false, false, false, true, true, true, true, true, true, false, false, true, false, false, true, false, true, true, true, false, true];
      {
        calc {
          [false, false, false, true, true, true, true, true, true, false, true, true, true, false, true, true, false, true, false, true, false, false, true, false, false, true, true, true, true, false, false, true];
          {
            pow_479();
            of_pow(512, true, false, false, true, true, true, true, false, false, true, false, false, true, false, true, false, true, true, false, true, true, true, false, true, true, true, true, true, true, false, false, false);
          }
          pow_mod_crc(512);
        }
        calc {
          [false, true, true, true, false, false, false, true, false, true, false, false, false, false, true, true, true, true, true, true, false, false, true, false, false, true, false, true, true, true, false, true];
          {
            pow_223();
            of_pow(256, true, false, true, true, true, false, true, false, false, true, false, false, true, true, true, true, true, true, false, false, false, false, true, false, true, false, false, false, true, true, true, false);
          }
          pow_mod_crc(256);
        }
      }
      pow_mod_crc(512) + pow_mod_crc(256);
    }
  }



  lemma lut_entry_4()
  ensures bits_of_int(lut[4] as int, 64)
      == pow_mod_crc(640) + pow_mod_crc(320)
  {
    calc {
      bits_of_int(lut[4] as int, 64);
      bits_of_int(4442467653714686614, 64);
      {
        lemma_bits_of_int_64_split(4442467653714686614);
      }
      bits_of_int(970175126, 32) + bits_of_int(1034342603, 32);
      {
        unroll_bits_of_int_32_0x39d3b296();
        unroll_bits_of_int_32_0x3da6d0cb();
      }
      [false, true, true, false, true, false, false, true, false, true, false, false, true, true, false, true, true, true, false, false, true, false, true, true, true, false, false, true, true, true, false, false]+[true, true, false, true, false, false, true, true, false, false, false, false, true, false, true, true, false, true, true, false, false, true, false, true, true, false, true, true, true, true, false, false];
      {
        calc {
          [false, true, true, false, true, false, false, true, false, true, false, false, true, true, false, true, true, true, false, false, true, false, true, true, true, false, false, true, true, true, false, false];
          {
            pow_607();
            of_pow(640, false, false, true, true, true, false, false, true, true, true, false, true, false, false, true, true, true, false, true, true, false, false, true, false, true, false, false, true, false, true, true, false);
          }
          pow_mod_crc(640);
        }
        calc {
          [true, true, false, true, false, false, true, true, false, false, false, false, true, false, true, true, false, true, true, false, false, true, false, true, true, false, true, true, true, true, false, false];
          {
            pow_287();
            of_pow(320, false, false, true, true, true, true, false, true, true, false, true, false, false, true, true, false, true, true, false, true, false, false, false, false, true, true, false, false, true, false, true, true);
          }
          pow_mod_crc(320);
        }
      }
      pow_mod_crc(640) + pow_mod_crc(320);
    }
  }



  lemma lut_entry_5()
  ensures bits_of_int(lut[5] as int, 64)
      == pow_mod_crc(768) + pow_mod_crc(384)
  {
    calc {
      bits_of_int(lut[5] as int, 64);
      bits_of_int(15978794752457166419, 64);
      {
        lemma_bits_of_int_64_split(15978794752457166419);
      }
      bits_of_int(118869587, 32) + bits_of_int(3720353067, 32);
      {
        unroll_bits_of_int_32_0x0715ce53();
        unroll_bits_of_int_32_0xddc0152b();
      }
      [true, true, false, false, true, false, true, false, false, true, true, true, false, false, true, true, true, false, true, false, true, false, false, false, true, true, true, false, false, false, false, false]+[true, true, false, true, false, true, false, false, true, false, true, false, true, false, false, false, false, false, false, false, false, false, true, true, true, false, true, true, true, false, true, true];
      {
        calc {
          [true, true, false, false, true, false, true, false, false, true, true, true, false, false, true, true, true, false, true, false, true, false, false, false, true, true, true, false, false, false, false, false];
          {
            pow_735();
            of_pow(768, false, false, false, false, false, true, true, true, false, false, false, true, false, true, false, true, true, true, false, false, true, true, true, false, false, true, false, true, false, false, true, true);
          }
          pow_mod_crc(768);
        }
        calc {
          [true, true, false, true, false, true, false, false, true, false, true, false, true, false, false, false, false, false, false, false, false, false, true, true, true, false, true, true, true, false, true, true];
          {
            pow_351();
            of_pow(384, true, true, false, true, true, true, false, true, true, true, false, false, false, false, false, false, false, false, false, true, false, true, false, true, false, false, true, false, true, false, true, true);
          }
          pow_mod_crc(384);
        }
      }
      pow_mod_crc(768) + pow_mod_crc(384);
    }
  }



  lemma lut_entry_6()
  ensures bits_of_int(lut[6] as int, 64)
      == pow_mod_crc(896) + pow_mod_crc(448)
  {
    calc {
      bits_of_int(lut[6] as int, 64);
      bits_of_int(2029185011329762071, 64);
      {
        lemma_bits_of_int_64_split(2029185011329762071);
      }
      bits_of_int(1205568279, 32) + bits_of_int(472456452, 32);
      {
        unroll_bits_of_int_32_0x47db8317();
        unroll_bits_of_int_32_0x1c291d04();
      }
      [true, true, true, false, true, false, false, false, true, true, false, false, false, false, false, true, true, true, false, true, true, false, true, true, true, true, true, false, false, false, true, false]+[false, false, true, false, false, false, false, false, true, false, true, true, true, false, false, false, true, false, false, true, false, true, false, false, false, false, true, true, true, false, false, false];
      {
        calc {
          [true, true, true, false, true, false, false, false, true, true, false, false, false, false, false, true, true, true, false, true, true, false, true, true, true, true, true, false, false, false, true, false];
          {
            pow_863();
            of_pow(896, false, true, false, false, false, true, true, true, true, true, false, true, true, false, true, true, true, false, false, false, false, false, true, true, false, false, false, true, false, true, true, true);
          }
          pow_mod_crc(896);
        }
        calc {
          [false, false, true, false, false, false, false, false, true, false, true, true, true, false, false, false, true, false, false, true, false, true, false, false, false, false, true, true, true, false, false, false];
          {
            pow_415();
            of_pow(448, false, false, false, true, true, true, false, false, false, false, true, false, true, false, false, true, false, false, false, true, true, true, false, true, false, false, false, false, false, true, false, false);
          }
          pow_mod_crc(448);
        }
      }
      pow_mod_crc(896) + pow_mod_crc(448);
    }
  }



  lemma lut_entry_7()
  ensures bits_of_int(lut[7] as int, 64)
      == pow_mod_crc(1024) + pow_mod_crc(512)
  {
    calc {
      bits_of_int(lut[7] as int, 64);
      bits_of_int(11406173063712825490, 64);
      {
        lemma_bits_of_int_64_split(11406173063712825490);
      }
      bits_of_int(221995154, 32) + bits_of_int(2655706616, 32);
      {
        unroll_bits_of_int_32_0x0d3b6092();
        unroll_bits_of_int_32_0x9e4addf8();
      }
      [false, true, false, false, true, false, false, true, false, false, false, false, false, true, true, false, true, true, false, true, true, true, false, false, true, false, true, true, false, false, false, false]+[false, false, false, true, true, true, true, true, true, false, true, true, true, false, true, true, false, true, false, true, false, false, true, false, false, true, true, true, true, false, false, true];
      {
        calc {
          [false, true, false, false, true, false, false, true, false, false, false, false, false, true, true, false, true, true, false, true, true, true, false, false, true, false, true, true, false, false, false, false];
          {
            pow_991();
            of_pow(1024, false, false, false, false, true, true, false, true, false, false, true, true, true, false, true, true, false, true, true, false, false, false, false, false, true, false, false, true, false, false, true, false);
          }
          pow_mod_crc(1024);
        }
        calc {
          [false, false, false, true, true, true, true, true, true, false, true, true, true, false, true, true, false, true, false, true, false, false, true, false, false, true, true, true, true, false, false, true];
          {
            pow_479();
            of_pow(512, true, false, false, true, true, true, true, false, false, true, false, false, true, false, true, false, true, true, false, true, true, true, false, true, true, true, true, true, true, false, false, false);
          }
          pow_mod_crc(512);
        }
      }
      pow_mod_crc(1024) + pow_mod_crc(512);
    }
  }



  lemma lut_entry_8()
  ensures bits_of_int(lut[8] as int, 64)
      == pow_mod_crc(1152) + pow_mod_crc(576)
  {
    calc {
      bits_of_int(lut[8] as int, 64);
      bits_of_int(8362884353321926080, 64);
      {
        lemma_bits_of_int_64_split(8362884353321926080);
      }
      bits_of_int(3379363264, 32) + bits_of_int(1947135746, 32);
      {
        unroll_bits_of_int_32_0xc96cfdc0();
        unroll_bits_of_int_32_0x740eef02();
      }
      [false, false, false, false, false, false, true, true, true, false, true, true, true, true, true, true, false, false, true, true, false, true, true, false, true, false, false, true, false, false, true, true]+[false, true, false, false, false, false, false, false, true, true, true, true, false, true, true, true, false, true, true, true, false, false, false, false, false, false, true, false, true, true, true, false];
      {
        calc {
          [false, false, false, false, false, false, true, true, true, false, true, true, true, true, true, true, false, false, true, true, false, true, true, false, true, false, false, true, false, false, true, true];
          {
            pow_1119();
            of_pow(1152, true, true, false, false, true, false, false, true, false, true, true, false, true, true, false, false, true, true, true, true, true, true, false, true, true, true, false, false, false, false, false, false);
          }
          pow_mod_crc(1152);
        }
        calc {
          [false, true, false, false, false, false, false, false, true, true, true, true, false, true, true, true, false, true, true, true, false, false, false, false, false, false, true, false, true, true, true, false];
          {
            pow_543();
            of_pow(576, false, true, true, true, false, true, false, false, false, false, false, false, true, true, true, false, true, true, true, false, true, true, true, true, false, false, false, false, false, false, true, false);
          }
          pow_mod_crc(576);
        }
      }
      pow_mod_crc(1152) + pow_mod_crc(576);
    }
  }



  lemma lut_entry_9()
  ensures bits_of_int(lut[9] as int, 64)
      == pow_mod_crc(1280) + pow_mod_crc(640)
  {
    calc {
      bits_of_int(lut[9] as int, 64);
      bits_of_int(4166870439836684967, 64);
      {
        lemma_bits_of_int_64_split(4166870439836684967);
      }
      bits_of_int(2274005671, 32) + bits_of_int(970175126, 32);
      {
        unroll_bits_of_int_32_0x878a92a7();
        unroll_bits_of_int_32_0x39d3b296();
      }
      [true, true, true, false, false, true, false, true, false, true, false, false, true, false, false, true, false, true, false, true, false, false, false, true, true, true, true, false, false, false, false, true]+[false, true, true, false, true, false, false, true, false, true, false, false, true, true, false, true, true, true, false, false, true, false, true, true, true, false, false, true, true, true, false, false];
      {
        calc {
          [true, true, true, false, false, true, false, true, false, true, false, false, true, false, false, true, false, true, false, true, false, false, false, true, true, true, true, false, false, false, false, true];
          {
            pow_1247();
            of_pow(1280, true, false, false, false, false, true, true, true, true, false, false, false, true, false, true, false, true, false, false, true, false, false, true, false, true, false, true, false, false, true, true, true);
          }
          pow_mod_crc(1280);
        }
        calc {
          [false, true, true, false, true, false, false, true, false, true, false, false, true, true, false, true, true, true, false, false, true, false, true, true, true, false, false, true, true, true, false, false];
          {
            pow_607();
            of_pow(640, false, false, true, true, true, false, false, true, true, true, false, true, false, false, true, true, true, false, true, true, false, false, true, false, true, false, false, true, false, true, true, false);
          }
          pow_mod_crc(640);
        }
      }
      pow_mod_crc(1280) + pow_mod_crc(640);
    }
  }



  lemma lut_entry_10()
  ensures bits_of_int(lut[10] as int, 64)
      == pow_mod_crc(1408) + pow_mod_crc(704)
  {
    calc {
      bits_of_int(lut[10] as int, 64);
      bits_of_int(592908264516937534, 64);
      {
        lemma_bits_of_int_64_split(592908264516937534);
      }
      bits_of_int(3672958782, 32) + bits_of_int(138047212, 32);
      {
        unroll_bits_of_int_32_0xdaece73e();
        unroll_bits_of_int_32_0x083a6eec();
      }
      [false, true, true, true, true, true, false, false, true, true, true, false, false, true, true, true, false, false, true, true, false, true, true, true, false, true, false, true, true, false, true, true]+[false, false, true, true, false, true, true, true, false, true, true, true, false, true, true, false, false, true, false, true, true, true, false, false, false, false, false, true, false, false, false, false];
      {
        calc {
          [false, true, true, true, true, true, false, false, true, true, true, false, false, true, true, true, false, false, true, true, false, true, true, true, false, true, false, true, true, false, true, true];
          {
            pow_1375();
            of_pow(1408, true, true, false, true, true, false, true, false, true, true, true, false, true, true, false, false, true, true, true, false, false, true, true, true, false, false, true, true, true, true, true, false);
          }
          pow_mod_crc(1408);
        }
        calc {
          [false, false, true, true, false, true, true, true, false, true, true, true, false, true, true, false, false, true, false, true, true, true, false, false, false, false, false, true, false, false, false, false];
          {
            pow_671();
            of_pow(704, false, false, false, false, true, false, false, false, false, false, true, true, true, false, true, false, false, true, true, false, true, true, true, false, true, true, true, false, true, true, false, false);
          }
          pow_mod_crc(704);
        }
      }
      pow_mod_crc(1408) + pow_mod_crc(704);
    }
  }



  lemma lut_entry_11()
  ensures bits_of_int(lut[11] as int, 64)
      == pow_mod_crc(1536) + pow_mod_crc(768)
  {
    calc {
      bits_of_int(lut[11] as int, 64);
      bits_of_int(510540991530991402, 64);
      {
        lemma_bits_of_int_64_split(510540991530991402);
      }
      bits_of_int(2876964650, 32) + bits_of_int(118869587, 32);
      {
        unroll_bits_of_int_32_0xab7aff2a();
        unroll_bits_of_int_32_0x0715ce53();
      }
      [false, true, false, true, false, true, false, false, true, true, true, true, true, true, true, true, false, true, false, true, true, true, true, false, true, true, false, true, false, true, false, true]+[true, true, false, false, true, false, true, false, false, true, true, true, false, false, true, true, true, false, true, false, true, false, false, false, true, true, true, false, false, false, false, false];
      {
        calc {
          [false, true, false, true, false, true, false, false, true, true, true, true, true, true, true, true, false, true, false, true, true, true, true, false, true, true, false, true, false, true, false, true];
          {
            pow_1503();
            of_pow(1536, true, false, true, false, true, false, true, true, false, true, true, true, true, false, true, false, true, true, true, true, true, true, true, true, false, false, true, false, true, false, true, false);
          }
          pow_mod_crc(1536);
        }
        calc {
          [true, true, false, false, true, false, true, false, false, true, true, true, false, false, true, true, true, false, true, false, true, false, false, false, true, true, true, false, false, false, false, false];
          {
            pow_735();
            of_pow(768, false, false, false, false, false, true, true, true, false, false, false, true, false, true, false, true, true, true, false, false, true, true, true, false, false, true, false, true, false, false, true, true);
          }
          pow_mod_crc(768);
        }
      }
      pow_mod_crc(1536) + pow_mod_crc(768);
    }
  }



  lemma lut_entry_12()
  ensures bits_of_int(lut[12] as int, 64)
      == pow_mod_crc(1664) + pow_mod_crc(832)
  {
    calc {
      bits_of_int(lut[12] as int, 64);
      bits_of_int(14168130257091220357, 64);
      {
        lemma_bits_of_int_64_split(14168130257091220357);
      }
      bits_of_int(560124805, 32) + bits_of_int(3298774887, 32);
      {
        unroll_bits_of_int_32_0x2162d385();
        unroll_bits_of_int_32_0xc49f4f67();
      }
      [true, false, true, false, false, false, false, true, true, true, false, false, true, false, true, true, false, true, false, false, false, true, true, false, true, false, false, false, false, true, false, false]+[true, true, true, false, false, true, true, false, true, true, true, true, false, false, true, false, true, true, true, true, true, false, false, true, false, false, true, false, false, false, true, true];
      {
        calc {
          [true, false, true, false, false, false, false, true, true, true, false, false, true, false, true, true, false, true, false, false, false, true, true, false, true, false, false, false, false, true, false, false];
          {
            pow_1631();
            of_pow(1664, false, false, true, false, false, false, false, true, false, true, true, false, false, false, true, false, true, true, false, true, false, false, true, true, true, false, false, false, false, true, false, true);
          }
          pow_mod_crc(1664);
        }
        calc {
          [true, true, true, false, false, true, true, false, true, true, true, true, false, false, true, false, true, true, true, true, true, false, false, true, false, false, true, false, false, false, true, true];
          {
            pow_799();
            of_pow(832, true, true, false, false, false, true, false, false, true, false, false, true, true, true, true, true, false, true, false, false, true, true, true, true, false, true, true, false, false, true, true, true);
          }
          pow_mod_crc(832);
        }
      }
      pow_mod_crc(1664) + pow_mod_crc(832);
    }
  }



  lemma lut_entry_13()
  ensures bits_of_int(lut[13] as int, 64)
      == pow_mod_crc(1792) + pow_mod_crc(896)
  {
    calc {
      bits_of_int(lut[13] as int, 64);
      bits_of_int(5177876333601261618, 64);
      {
        lemma_bits_of_int_64_split(5177876333601261618);
      }
      bits_of_int(2201258034, 32) + bits_of_int(1205568279, 32);
      {
        unroll_bits_of_int_32_0x83348832();
        unroll_bits_of_int_32_0x47db8317();
      }
      [false, true, false, false, true, true, false, false, false, false, false, true, false, false, false, true, false, false, true, false, true, true, false, false, true, true, false, false, false, false, false, true]+[true, true, true, false, true, false, false, false, true, true, false, false, false, false, false, true, true, true, false, true, true, false, true, true, true, true, true, false, false, false, true, false];
      {
        calc {
          [false, true, false, false, true, true, false, false, false, false, false, true, false, false, false, true, false, false, true, false, true, true, false, false, true, true, false, false, false, false, false, true];
          {
            pow_1759();
            of_pow(1792, true, false, false, false, false, false, true, true, false, false, true, true, false, true, false, false, true, false, false, false, true, false, false, false, false, false, true, true, false, false, true, false);
          }
          pow_mod_crc(1792);
        }
        calc {
          [true, true, true, false, true, false, false, false, true, true, false, false, false, false, false, true, true, true, false, true, true, false, true, true, true, true, true, false, false, false, true, false];
          {
            pow_863();
            of_pow(896, false, true, false, false, false, true, true, true, true, true, false, true, true, false, true, true, true, false, false, false, false, false, true, true, false, false, false, true, false, true, true, true);
          }
          pow_mod_crc(896);
        }
      }
      pow_mod_crc(1792) + pow_mod_crc(896);
    }
  }



  lemma lut_entry_14()
  ensures bits_of_int(lut[14] as int, 64)
      == pow_mod_crc(1920) + pow_mod_crc(960)
  {
    calc {
      bits_of_int(lut[14] as int, 64);
      bits_of_int(3087530012721039317, 64);
      {
        lemma_bits_of_int_64_split(3087530012721039317);
      }
      bits_of_int(697845717, 32) + bits_of_int(718871600, 32);
      {
        unroll_bits_of_int_32_0x299847d5();
        unroll_bits_of_int_32_0x2ad91c30();
      }
      [true, false, true, false, true, false, true, true, true, true, true, false, false, false, true, false, false, false, false, true, true, false, false, true, true, false, false, true, false, true, false, false]+[false, false, false, false, true, true, false, false, false, false, true, true, true, false, false, false, true, false, false, true, true, false, true, true, false, true, false, true, false, true, false, false];
      {
        calc {
          [true, false, true, false, true, false, true, true, true, true, true, false, false, false, true, false, false, false, false, true, true, false, false, true, true, false, false, true, false, true, false, false];
          {
            pow_1887();
            of_pow(1920, false, false, true, false, true, false, false, true, true, false, false, true, true, false, false, false, false, true, false, false, false, true, true, true, true, true, false, true, false, true, false, true);
          }
          pow_mod_crc(1920);
        }
        calc {
          [false, false, false, false, true, true, false, false, false, false, true, true, true, false, false, false, true, false, false, true, true, false, true, true, false, true, false, true, false, true, false, false];
          {
            pow_927();
            of_pow(960, false, false, true, false, true, false, true, false, true, true, false, true, true, false, false, true, false, false, false, true, true, true, false, false, false, false, true, true, false, false, false, false);
          }
          pow_mod_crc(960);
        }
      }
      pow_mod_crc(1920) + pow_mod_crc(960);
    }
  }



  lemma lut_entry_15()
  ensures bits_of_int(lut[15] as int, 64)
      == pow_mod_crc(2048) + pow_mod_crc(1024)
  {
    calc {
      bits_of_int(lut[15] as int, 64);
      bits_of_int(953461929418959750, 64);
      {
        lemma_bits_of_int_64_split(953461929418959750);
      }
      bits_of_int(3118476166, 32) + bits_of_int(221995154, 32);
      {
        unroll_bits_of_int_32_0xb9e02b86();
        unroll_bits_of_int_32_0x0d3b6092();
      }
      [false, true, true, false, false, false, false, true, true, true, false, true, false, true, false, false, false, false, false, false, false, true, true, true, true, false, false, true, true, true, false, true]+[false, true, false, false, true, false, false, true, false, false, false, false, false, true, true, false, true, true, false, true, true, true, false, false, true, false, true, true, false, false, false, false];
      {
        calc {
          [false, true, true, false, false, false, false, true, true, true, false, true, false, true, false, false, false, false, false, false, false, true, true, true, true, false, false, true, true, true, false, true];
          {
            pow_2015();
            of_pow(2048, true, false, true, true, true, false, false, true, true, true, true, false, false, false, false, false, false, false, true, false, true, false, true, true, true, false, false, false, false, true, true, false);
          }
          pow_mod_crc(2048);
        }
        calc {
          [false, true, false, false, true, false, false, true, false, false, false, false, false, true, true, false, true, true, false, true, true, true, false, false, true, false, true, true, false, false, false, false];
          {
            pow_991();
            of_pow(1024, false, false, false, false, true, true, false, true, false, false, true, true, true, false, true, true, false, true, true, false, false, false, false, false, true, false, false, true, false, false, true, false);
          }
          pow_mod_crc(1024);
        }
      }
      pow_mod_crc(2048) + pow_mod_crc(1024);
    }
  }



  lemma lut_entry_16()
  ensures bits_of_int(lut[16] as int, 64)
      == pow_mod_crc(2176) + pow_mod_crc(1088)
  {
    calc {
      bits_of_int(lut[16] as int, 64);
      bits_of_int(7607369916176611918, 64);
      {
        lemma_bits_of_int_64_split(7607369916176611918);
      }
      bits_of_int(414399054, 32) + bits_of_int(1771228834, 32);
      {
        unroll_bits_of_int_32_0x18b33a4e();
        unroll_bits_of_int_32_0x6992cea2();
      }
      [false, true, true, true, false, false, true, false, false, true, false, true, true, true, false, false, true, true, false, false, true, true, false, true, false, false, false, true, true, false, false, false]+[false, true, false, false, false, true, false, true, false, true, true, true, false, false, true, true, false, true, false, false, true, false, false, true, true, false, false, true, false, true, true, false];
      {
        calc {
          [false, true, true, true, false, false, true, false, false, true, false, true, true, true, false, false, true, true, false, false, true, true, false, true, false, false, false, true, true, false, false, false];
          {
            pow_2143();
            of_pow(2176, false, false, false, true, true, false, false, false, true, false, true, true, false, false, true, true, false, false, true, true, true, false, true, false, false, true, false, false, true, true, true, false);
          }
          pow_mod_crc(2176);
        }
        calc {
          [false, true, false, false, false, true, false, true, false, true, true, true, false, false, true, true, false, true, false, false, true, false, false, true, true, false, false, true, false, true, true, false];
          {
            pow_1055();
            of_pow(1088, false, true, true, false, true, false, false, true, true, false, false, true, false, false, true, false, true, true, false, false, true, true, true, false, true, false, true, false, false, false, true, false);
          }
          pow_mod_crc(1088);
        }
      }
      pow_mod_crc(2176) + pow_mod_crc(1088);
    }
  }



  lemma lut_entry_17()
  ensures bits_of_int(lut[17] as int, 64)
      == pow_mod_crc(2304) + pow_mod_crc(1152)
  {
    calc {
      bits_of_int(lut[17] as int, 64);
      bits_of_int(14514254703251788955, 64);
      {
        lemma_bits_of_int_64_split(14514254703251788955);
      }
      bits_of_int(3067974811, 32) + bits_of_int(3379363264, 32);
      {
        unroll_bits_of_int_32_0xb6dd949b();
        unroll_bits_of_int_32_0xc96cfdc0();
      }
      [true, true, false, true, true, false, false, true, false, false, true, false, true, false, false, true, true, false, true, true, true, false, true, true, false, true, true, false, true, true, false, true]+[false, false, false, false, false, false, true, true, true, false, true, true, true, true, true, true, false, false, true, true, false, true, true, false, true, false, false, true, false, false, true, true];
      {
        calc {
          [true, true, false, true, true, false, false, true, false, false, true, false, true, false, false, true, true, false, true, true, true, false, true, true, false, true, true, false, true, true, false, true];
          {
            pow_2271();
            of_pow(2304, true, false, true, true, false, true, true, false, true, true, false, true, true, true, false, true, true, false, false, true, false, true, false, false, true, false, false, true, true, false, true, true);
          }
          pow_mod_crc(2304);
        }
        calc {
          [false, false, false, false, false, false, true, true, true, false, true, true, true, true, true, true, false, false, true, true, false, true, true, false, true, false, false, true, false, false, true, true];
          {
            pow_1119();
            of_pow(1152, true, true, false, false, true, false, false, true, false, true, true, false, true, true, false, false, true, true, true, true, true, true, false, true, true, true, false, false, false, false, false, false);
          }
          pow_mod_crc(1152);
        }
      }
      pow_mod_crc(2304) + pow_mod_crc(1152);
    }
  }



  lemma lut_entry_18()
  ensures bits_of_int(lut[18] as int, 64)
      == pow_mod_crc(2432) + pow_mod_crc(1216)
  {
    calc {
      bits_of_int(lut[18] as int, 64);
      bits_of_int(9119930294178794679, 64);
      {
        lemma_bits_of_int_64_split(9119930294178794679);
      }
      bits_of_int(2027539639, 32) + bits_of_int(2123399240, 32);
      {
        unroll_bits_of_int_32_0x78d9ccb7();
        unroll_bits_of_int_32_0x7e908048();
      }
      [true, true, true, false, true, true, false, true, false, false, true, true, false, false, true, true, true, false, false, true, true, false, true, true, false, false, false, true, true, true, true, false]+[false, false, false, true, false, false, true, false, false, false, false, false, false, false, false, true, false, false, false, false, true, false, false, true, false, true, true, true, true, true, true, false];
      {
        calc {
          [true, true, true, false, true, true, false, true, false, false, true, true, false, false, true, true, true, false, false, true, true, false, true, true, false, false, false, true, true, true, true, false];
          {
            pow_2399();
            of_pow(2432, false, true, true, true, true, false, false, false, true, true, false, true, true, false, false, true, true, true, false, false, true, true, false, false, true, false, true, true, false, true, true, true);
          }
          pow_mod_crc(2432);
        }
        calc {
          [false, false, false, true, false, false, true, false, false, false, false, false, false, false, false, true, false, false, false, false, true, false, false, true, false, true, true, true, true, true, true, false];
          {
            pow_1183();
            of_pow(1216, false, true, true, true, true, true, true, false, true, false, false, true, false, false, false, false, true, false, false, false, false, false, false, false, false, true, false, false, true, false, false, false);
          }
          pow_mod_crc(1216);
        }
      }
      pow_mod_crc(2432) + pow_mod_crc(1216);
    }
  }



  lemma lut_entry_19()
  ensures bits_of_int(lut[19] as int, 64)
      == pow_mod_crc(2560) + pow_mod_crc(1280)
  {
    calc {
      bits_of_int(lut[19] as int, 64);
      bits_of_int(9766779990996876667, 64);
      {
        lemma_bits_of_int_64_split(9766779990996876667);
      }
      bits_of_int(3133341051, 32) + bits_of_int(2274005671, 32);
      {
        unroll_bits_of_int_32_0xbac2fd7b();
        unroll_bits_of_int_32_0x878a92a7();
      }
      [true, true, false, true, true, true, true, false, true, false, true, true, true, true, true, true, false, true, false, false, false, false, true, true, false, true, false, true, true, true, false, true]+[true, true, true, false, false, true, false, true, false, true, false, false, true, false, false, true, false, true, false, true, false, false, false, true, true, true, true, false, false, false, false, true];
      {
        calc {
          [true, true, false, true, true, true, true, false, true, false, true, true, true, true, true, true, false, true, false, false, false, false, true, true, false, true, false, true, true, true, false, true];
          {
            pow_2527();
            of_pow(2560, true, false, true, true, true, false, true, false, true, true, false, false, false, false, true, false, true, true, true, true, true, true, false, true, false, true, true, true, true, false, true, true);
          }
          pow_mod_crc(2560);
        }
        calc {
          [true, true, true, false, false, true, false, true, false, true, false, false, true, false, false, true, false, true, false, true, false, false, false, true, true, true, true, false, false, false, false, true];
          {
            pow_1247();
            of_pow(1280, true, false, false, false, false, true, true, true, true, false, false, false, true, false, true, false, true, false, false, true, false, false, true, false, true, false, true, false, false, true, true, true);
          }
          pow_mod_crc(1280);
        }
      }
      pow_mod_crc(2560) + pow_mod_crc(1280);
    }
  }



  lemma lut_entry_20()
  ensures bits_of_int(lut[20] as int, 64)
      == pow_mod_crc(2688) + pow_mod_crc(1344)
  {
    calc {
      bits_of_int(lut[20] as int, 64);
      bits_of_int(1962882421645697147, 64);
      {
        lemma_bits_of_int_64_split(1962882421645697147);
      }
      bits_of_int(2785861755, 32) + bits_of_int(457019177, 32);
      {
        unroll_bits_of_int_32_0xa60ce07b();
        unroll_bits_of_int_32_0x1b3d8f29();
      }
      [true, true, false, true, true, true, true, false, false, false, false, false, false, true, true, true, false, false, true, true, false, false, false, false, false, true, true, false, false, true, false, true]+[true, false, false, true, false, true, false, false, true, true, true, true, false, false, false, true, true, false, true, true, true, true, false, false, true, true, false, true, true, false, false, false];
      {
        calc {
          [true, true, false, true, true, true, true, false, false, false, false, false, false, true, true, true, false, false, true, true, false, false, false, false, false, true, true, false, false, true, false, true];
          {
            pow_2655();
            of_pow(2688, true, false, true, false, false, true, true, false, false, false, false, false, true, true, false, false, true, true, true, false, false, false, false, false, false, true, true, true, true, false, true, true);
          }
          pow_mod_crc(2688);
        }
        calc {
          [true, false, false, true, false, true, false, false, true, true, true, true, false, false, false, true, true, false, true, true, true, true, false, false, true, true, false, true, true, false, false, false];
          {
            pow_1311();
            of_pow(1344, false, false, false, true, true, false, true, true, false, false, true, true, true, true, false, true, true, false, false, false, true, true, true, true, false, false, true, false, true, false, false, true);
          }
          pow_mod_crc(1344);
        }
      }
      pow_mod_crc(2688) + pow_mod_crc(1344);
    }
  }



  lemma lut_entry_21()
  ensures bits_of_int(lut[21] as int, 64)
      == pow_mod_crc(2816) + pow_mod_crc(1408)
  {
    calc {
      bits_of_int(lut[21] as int, 64);
      bits_of_int(15775237851710437876, 64);
      {
        lemma_bits_of_int_64_split(15775237851710437876);
      }
      bits_of_int(3464444404, 32) + bits_of_int(3672958782, 32);
      {
        unroll_bits_of_int_32_0xce7f39f4();
        unroll_bits_of_int_32_0xdaece73e();
      }
      [false, false, true, false, true, true, true, true, true, false, false, true, true, true, false, false, true, true, true, true, true, true, true, false, false, true, true, true, false, false, true, true]+[false, true, true, true, true, true, false, false, true, true, true, false, false, true, true, true, false, false, true, true, false, true, true, true, false, true, false, true, true, false, true, true];
      {
        calc {
          [false, false, true, false, true, true, true, true, true, false, false, true, true, true, false, false, true, true, true, true, true, true, true, false, false, true, true, true, false, false, true, true];
          {
            pow_2783();
            of_pow(2816, true, true, false, false, true, true, true, false, false, true, true, true, true, true, true, true, false, false, true, true, true, false, false, true, true, true, true, true, false, true, false, false);
          }
          pow_mod_crc(2816);
        }
        calc {
          [false, true, true, true, true, true, false, false, true, true, true, false, false, true, true, true, false, false, true, true, false, true, true, true, false, true, false, true, true, false, true, true];
          {
            pow_1375();
            of_pow(1408, true, true, false, true, true, false, true, false, true, true, true, false, true, true, false, false, true, true, true, false, false, true, true, true, false, false, true, true, true, true, true, false);
          }
          pow_mod_crc(1408);
        }
      }
      pow_mod_crc(2816) + pow_mod_crc(1408);
    }
  }



  lemma lut_entry_22()
  ensures bits_of_int(lut[22] as int, 64)
      == pow_mod_crc(2944) + pow_mod_crc(1472)
  {
    calc {
      bits_of_int(lut[22] as int, 64);
      bits_of_int(17424696744013737558, 64);
      {
        lemma_bits_of_int_64_split(17424696744013737558);
      }
      bits_of_int(1641557590, 32) + bits_of_int(4057003358, 32);
      {
        unroll_bits_of_int_32_0x61d82e56();
        unroll_bits_of_int_32_0xf1d0f55e();
      }
      [false, true, true, false, true, false, true, false, false, true, true, true, false, true, false, false, false, false, false, true, true, false, true, true, true, false, false, false, false, true, true, false]+[false, true, true, true, true, false, true, false, true, false, true, false, true, true, true, true, false, false, false, false, true, false, true, true, true, false, false, false, true, true, true, true];
      {
        calc {
          [false, true, true, false, true, false, true, false, false, true, true, true, false, true, false, false, false, false, false, true, true, false, true, true, true, false, false, false, false, true, true, false];
          {
            pow_2911();
            of_pow(2944, false, true, true, false, false, false, false, true, true, true, false, true, true, false, false, false, false, false, true, false, true, true, true, false, false, true, false, true, false, true, true, false);
          }
          pow_mod_crc(2944);
        }
        calc {
          [false, true, true, true, true, false, true, false, true, false, true, false, true, true, true, true, false, false, false, false, true, false, true, true, true, false, false, false, true, true, true, true];
          {
            pow_1439();
            of_pow(1472, true, true, true, true, false, false, false, true, true, true, false, true, false, false, false, false, true, true, true, true, false, true, false, true, false, true, false, true, true, true, true, false);
          }
          pow_mod_crc(1472);
        }
      }
      pow_mod_crc(2944) + pow_mod_crc(1472);
    }
  }



  lemma lut_entry_23()
  ensures bits_of_int(lut[23] as int, 64)
      == pow_mod_crc(3072) + pow_mod_crc(1536)
  {
    calc {
      bits_of_int(lut[23] as int, 64);
      bits_of_int(12356469087028703650, 64);
      {
        lemma_bits_of_int_64_split(12356469087028703650);
      }
      bits_of_int(3530617250, 32) + bits_of_int(2876964650, 32);
      {
        unroll_bits_of_int_32_0xd270f1a2();
        unroll_bits_of_int_32_0xab7aff2a();
      }
      [false, true, false, false, false, true, false, true, true, false, false, false, true, true, true, true, false, false, false, false, true, true, true, false, false, true, false, false, true, false, true, true]+[false, true, false, true, false, true, false, false, true, true, true, true, true, true, true, true, false, true, false, true, true, true, true, false, true, true, false, true, false, true, false, true];
      {
        calc {
          [false, true, false, false, false, true, false, true, true, false, false, false, true, true, true, true, false, false, false, false, true, true, true, false, false, true, false, false, true, false, true, true];
          {
            pow_3039();
            of_pow(3072, true, true, false, true, false, false, true, false, false, true, true, true, false, false, false, false, true, true, true, true, false, false, false, true, true, false, true, false, false, false, true, false);
          }
          pow_mod_crc(3072);
        }
        calc {
          [false, true, false, true, false, true, false, false, true, true, true, true, true, true, true, true, false, true, false, true, true, true, true, false, true, true, false, true, false, true, false, true];
          {
            pow_1503();
            of_pow(1536, true, false, true, false, true, false, true, true, false, true, true, true, true, false, true, false, true, true, true, true, true, true, true, true, false, false, true, false, true, false, true, false);
          }
          pow_mod_crc(1536);
        }
      }
      pow_mod_crc(3072) + pow_mod_crc(1536);
    }
  }



  lemma lut_entry_24()
  ensures bits_of_int(lut[24] as int, 64)
      == pow_mod_crc(3200) + pow_mod_crc(1600)
  {
    calc {
      bits_of_int(lut[24] as int, 64);
      bits_of_int(12140218780548169885, 64);
      {
        lemma_bits_of_int_64_split(12140218780548169885);
      }
      bits_of_int(3323560093, 32) + bits_of_int(2826614952, 32);
      {
        unroll_bits_of_int_32_0xc619809d();
        unroll_bits_of_int_32_0xa87ab8a8();
      }
      [true, false, true, true, true, false, false, true, false, false, false, false, false, false, false, true, true, false, false, true, true, false, false, false, false, true, true, false, false, false, true, true]+[false, false, false, true, false, true, false, true, false, false, false, true, true, true, false, true, false, true, false, true, true, true, true, false, false, false, false, true, false, true, false, true];
      {
        calc {
          [true, false, true, true, true, false, false, true, false, false, false, false, false, false, false, true, true, false, false, true, true, false, false, false, false, true, true, false, false, false, true, true];
          {
            pow_3167();
            of_pow(3200, true, true, false, false, false, true, true, false, false, false, false, true, true, false, false, true, true, false, false, false, false, false, false, false, true, false, false, true, true, true, false, true);
          }
          pow_mod_crc(3200);
        }
        calc {
          [false, false, false, true, false, true, false, true, false, false, false, true, true, true, false, true, false, true, false, true, true, true, true, false, false, false, false, true, false, true, false, true];
          {
            pow_1567();
            of_pow(1600, true, false, true, false, true, false, false, false, false, true, true, true, true, false, true, false, true, false, true, true, true, false, false, false, true, false, true, false, true, false, false, false);
          }
          pow_mod_crc(1600);
        }
      }
      pow_mod_crc(3200) + pow_mod_crc(1600);
    }
  }



  lemma lut_entry_25()
  ensures bits_of_int(lut[25] as int, 64)
      == pow_mod_crc(3328) + pow_mod_crc(1664)
  {
    calc {
      bits_of_int(lut[25] as int, 64);
      bits_of_int(2405717719878773853, 64);
      {
        lemma_bits_of_int_64_split(2405717719878773853);
      }
      bits_of_int(725396573, 32) + bits_of_int(560124805, 32);
      {
        unroll_bits_of_int_32_0x2b3cac5d();
        unroll_bits_of_int_32_0x2162d385();
      }
      [true, false, true, true, true, false, true, false, false, false, true, true, false, true, false, true, false, false, true, true, true, true, false, false, true, true, false, true, false, true, false, false]+[true, false, true, false, false, false, false, true, true, true, false, false, true, false, true, true, false, true, false, false, false, true, true, false, true, false, false, false, false, true, false, false];
      {
        calc {
          [true, false, true, true, true, false, true, false, false, false, true, true, false, true, false, true, false, false, true, true, true, true, false, false, true, true, false, true, false, true, false, false];
          {
            pow_3295();
            of_pow(3328, false, false, true, false, true, false, true, true, false, false, true, true, true, true, false, false, true, false, true, false, true, true, false, false, false, true, false, true, true, true, false, true);
          }
          pow_mod_crc(3328);
        }
        calc {
          [true, false, true, false, false, false, false, true, true, true, false, false, true, false, true, true, false, true, false, false, false, true, true, false, true, false, false, false, false, true, false, false];
          {
            pow_1631();
            of_pow(1664, false, false, true, false, false, false, false, true, false, true, true, false, false, false, true, false, true, true, false, true, false, false, true, true, true, false, false, false, false, true, false, true);
          }
          pow_mod_crc(1664);
        }
      }
      pow_mod_crc(3328) + pow_mod_crc(1664);
    }
  }



  lemma lut_entry_26()
  ensures bits_of_int(lut[26] as int, 64)
      == pow_mod_crc(3456) + pow_mod_crc(1728)
  {
    calc {
      bits_of_int(lut[26] as int, 64);
      bits_of_int(9539424456939027300, 64);
      {
        lemma_bits_of_int_64_split(9539424456939027300);
      }
      bits_of_int(1703295844, 32) + bits_of_int(2221070336, 32);
      {
        unroll_bits_of_int_32_0x65863b64();
        unroll_bits_of_int_32_0x8462d800();
      }
      [false, false, true, false, false, true, true, false, true, true, false, true, true, true, false, false, false, true, true, false, false, false, false, true, true, false, true, false, false, true, true, false]+[false, false, false, false, false, false, false, false, false, false, false, true, true, false, true, true, false, true, false, false, false, true, true, false, false, false, true, false, false, false, false, true];
      {
        calc {
          [false, false, true, false, false, true, true, false, true, true, false, true, true, true, false, false, false, true, true, false, false, false, false, true, true, false, true, false, false, true, true, false];
          {
            pow_3423();
            of_pow(3456, false, true, true, false, false, true, false, true, true, false, false, false, false, true, true, false, false, false, true, true, true, false, true, true, false, true, true, false, false, true, false, false);
          }
          pow_mod_crc(3456);
        }
        calc {
          [false, false, false, false, false, false, false, false, false, false, false, true, true, false, true, true, false, true, false, false, false, true, true, false, false, false, true, false, false, false, false, true];
          {
            pow_1695();
            of_pow(1728, true, false, false, false, false, true, false, false, false, true, true, false, false, false, true, false, true, true, false, true, true, false, false, false, false, false, false, false, false, false, false, false);
          }
          pow_mod_crc(1728);
        }
      }
      pow_mod_crc(3456) + pow_mod_crc(1728);
    }
  }



  lemma lut_entry_27()
  ensures bits_of_int(lut[27] as int, 64)
      == pow_mod_crc(3584) + pow_mod_crc(1792)
  {
    calc {
      bits_of_int(lut[27] as int, 64);
      bits_of_int(9454331266540452223, 64);
      {
        lemma_bits_of_int_64_split(9454331266540452223);
      }
      bits_of_int(453196159, 32) + bits_of_int(2201258034, 32);
      {
        unroll_bits_of_int_32_0x1b03397f();
        unroll_bits_of_int_32_0x83348832();
      }
      [true, true, true, true, true, true, true, false, true, false, false, true, true, true, false, false, true, true, false, false, false, false, false, false, true, true, false, true, true, false, false, false]+[false, true, false, false, true, true, false, false, false, false, false, true, false, false, false, true, false, false, true, false, true, true, false, false, true, true, false, false, false, false, false, true];
      {
        calc {
          [true, true, true, true, true, true, true, false, true, false, false, true, true, true, false, false, true, true, false, false, false, false, false, false, true, true, false, true, true, false, false, false];
          {
            pow_3551();
            of_pow(3584, false, false, false, true, true, false, true, true, false, false, false, false, false, false, true, true, false, false, true, true, true, false, false, true, false, true, true, true, true, true, true, true);
          }
          pow_mod_crc(3584);
        }
        calc {
          [false, true, false, false, true, true, false, false, false, false, false, true, false, false, false, true, false, false, true, false, true, true, false, false, true, true, false, false, false, false, false, true];
          {
            pow_1759();
            of_pow(1792, true, false, false, false, false, false, true, true, false, false, true, true, false, true, false, false, true, false, false, false, true, false, false, false, false, false, true, true, false, false, true, false);
          }
          pow_mod_crc(1792);
        }
      }
      pow_mod_crc(3584) + pow_mod_crc(1792);
    }
  }



  lemma lut_entry_28()
  ensures bits_of_int(lut[28] as int, 64)
      == pow_mod_crc(3712) + pow_mod_crc(1856)
  {
    calc {
      bits_of_int(lut[28] as int, 64);
      bits_of_int(8201355813625299901, 64);
      {
        lemma_bits_of_int_64_split(8201355813625299901);
      }
      bits_of_int(3954738109, 32) + bits_of_int(1909526952, 32);
      {
        unroll_bits_of_int_32_0xebb883bd();
        unroll_bits_of_int_32_0x71d111a8();
      }
      [true, false, true, true, true, true, false, true, true, true, false, false, false, false, false, true, false, false, false, true, true, true, false, true, true, true, false, true, false, true, true, true]+[false, false, false, true, false, true, false, true, true, false, false, false, true, false, false, false, true, false, false, false, true, false, true, true, true, false, false, false, true, true, true, false];
      {
        calc {
          [true, false, true, true, true, true, false, true, true, true, false, false, false, false, false, true, false, false, false, true, true, true, false, true, true, true, false, true, false, true, true, true];
          {
            pow_3679();
            of_pow(3712, true, true, true, false, true, false, true, true, true, false, true, true, true, false, false, false, true, false, false, false, false, false, true, true, true, false, true, true, true, true, false, true);
          }
          pow_mod_crc(3712);
        }
        calc {
          [false, false, false, true, false, true, false, true, true, false, false, false, true, false, false, false, true, false, false, false, true, false, true, true, true, false, false, false, true, true, true, false];
          {
            pow_1823();
            of_pow(1856, false, true, true, true, false, false, false, true, true, true, false, true, false, false, false, true, false, false, false, true, false, false, false, true, true, false, true, false, true, false, false, false);
          }
          pow_mod_crc(1856);
        }
      }
      pow_mod_crc(3712) + pow_mod_crc(1856);
    }
  }



  lemma lut_entry_29()
  ensures bits_of_int(lut[29] as int, 64)
      == pow_mod_crc(3840) + pow_mod_crc(1920)
  {
    calc {
      bits_of_int(lut[29] as int, 64);
      bits_of_int(2997224535186680872, 64);
      {
        lemma_bits_of_int_64_split(2997224535186680872);
      }
      bits_of_int(3018009640, 32) + bits_of_int(697845717, 32);
      {
        unroll_bits_of_int_32_0xb3e32c28();
        unroll_bits_of_int_32_0x299847d5();
      }
      [false, false, false, true, false, true, false, false, false, false, true, true, false, true, false, false, true, true, false, false, false, true, true, true, true, true, false, false, true, true, false, true]+[true, false, true, false, true, false, true, true, true, true, true, false, false, false, true, false, false, false, false, true, true, false, false, true, true, false, false, true, false, true, false, false];
      {
        calc {
          [false, false, false, true, false, true, false, false, false, false, true, true, false, true, false, false, true, true, false, false, false, true, true, true, true, true, false, false, true, true, false, true];
          {
            pow_3807();
            of_pow(3840, true, false, true, true, false, false, true, true, true, true, true, false, false, false, true, true, false, false, true, false, true, true, false, false, false, false, true, false, true, false, false, false);
          }
          pow_mod_crc(3840);
        }
        calc {
          [true, false, true, false, true, false, true, true, true, true, true, false, false, false, true, false, false, false, false, true, true, false, false, true, true, false, false, true, false, true, false, false];
          {
            pow_1887();
            of_pow(1920, false, false, true, false, true, false, false, true, true, false, false, true, true, false, false, false, false, true, false, false, false, true, true, true, true, true, false, true, false, true, false, true);
          }
          pow_mod_crc(1920);
        }
      }
      pow_mod_crc(3840) + pow_mod_crc(1920);
    }
  }



  lemma lut_entry_30()
  ensures bits_of_int(lut[30] as int, 64)
      == pow_mod_crc(3968) + pow_mod_crc(1984)
  {
    calc {
      bits_of_int(lut[30] as int, 64);
      bits_of_int(18435576085104000806, 64);
      {
        lemma_bits_of_int_64_split(18435576085104000806);
      }
      bits_of_int(105873190, 32) + bits_of_int(4292367046, 32);
      {
        unroll_bits_of_int_32_0x064f7f26();
        unroll_bits_of_int_32_0xffd852c6();
      }
      [false, true, true, false, false, true, false, false, true, true, true, true, true, true, true, false, true, true, true, true, false, false, true, false, false, true, true, false, false, false, false, false]+[false, true, true, false, false, false, true, true, false, true, false, false, true, false, true, false, false, false, false, true, true, false, true, true, true, true, true, true, true, true, true, true];
      {
        calc {
          [false, true, true, false, false, true, false, false, true, true, true, true, true, true, true, false, true, true, true, true, false, false, true, false, false, true, true, false, false, false, false, false];
          {
            pow_3935();
            of_pow(3968, false, false, false, false, false, true, true, false, false, true, false, false, true, true, true, true, false, true, true, true, true, true, true, true, false, false, true, false, false, true, true, false);
          }
          pow_mod_crc(3968);
        }
        calc {
          [false, true, true, false, false, false, true, true, false, true, false, false, true, false, true, false, false, false, false, true, true, false, true, true, true, true, true, true, true, true, true, true];
          {
            pow_1951();
            of_pow(1984, true, true, true, true, true, true, true, true, true, true, false, true, true, false, false, false, false, true, false, true, false, false, true, false, true, true, false, false, false, true, true, false);
          }
          pow_mod_crc(1984);
        }
      }
      pow_mod_crc(3968) + pow_mod_crc(1984);
    }
  }



  lemma lut_entry_31()
  ensures bits_of_int(lut[31] as int, 64)
      == pow_mod_crc(4096) + pow_mod_crc(2048)
  {
    calc {
      bits_of_int(lut[31] as int, 64);
      bits_of_int(13393753150041504524, 64);
      {
        lemma_bits_of_int_64_split(13393753150041504524);
      }
      bits_of_int(3716037388, 32) + bits_of_int(3118476166, 32);
      {
        unroll_bits_of_int_32_0xdd7e3b0c();
        unroll_bits_of_int_32_0xb9e02b86();
      }
      [false, false, true, true, false, false, false, false, true, true, false, true, true, true, false, false, false, true, true, true, true, true, true, false, true, false, true, true, true, false, true, true]+[false, true, true, false, false, false, false, true, true, true, false, true, false, true, false, false, false, false, false, false, false, true, true, true, true, false, false, true, true, true, false, true];
      {
        calc {
          [false, false, true, true, false, false, false, false, true, true, false, true, true, true, false, false, false, true, true, true, true, true, true, false, true, false, true, true, true, false, true, true];
          {
            pow_4063();
            of_pow(4096, true, true, false, true, true, true, false, true, false, true, true, true, true, true, true, false, false, false, true, true, true, false, true, true, false, false, false, false, true, true, false, false);
          }
          pow_mod_crc(4096);
        }
        calc {
          [false, true, true, false, false, false, false, true, true, true, false, true, false, true, false, false, false, false, false, false, false, true, true, true, true, false, false, true, true, true, false, true];
          {
            pow_2015();
            of_pow(2048, true, false, true, true, true, false, false, true, true, true, true, false, false, false, false, false, false, false, true, false, true, false, true, true, true, false, false, false, false, true, true, false);
          }
          pow_mod_crc(2048);
        }
      }
      pow_mod_crc(4096) + pow_mod_crc(2048);
    }
  }



  lemma lut_entry_32()
  ensures bits_of_int(lut[32] as int, 64)
      == pow_mod_crc(4224) + pow_mod_crc(2112)
  {
    calc {
      bits_of_int(lut[32] as int, 64);
      bits_of_int(15902626608083985692, 64);
      {
        lemma_bits_of_int_64_split(15902626608083985692);
      }
      bits_of_int(4068828444, 32) + bits_of_int(3702618788, 32);
      {
        unroll_bits_of_int_32_0xf285651c();
        unroll_bits_of_int_32_0xdcb17aa4();
      }
      [false, false, true, true, true, false, false, false, true, false, true, false, false, true, true, false, true, false, true, false, false, false, false, true, false, true, false, false, true, true, true, true]+[false, false, true, false, false, true, false, true, false, true, false, true, true, true, true, false, true, false, false, false, true, true, false, true, false, false, true, true, true, false, true, true];
      {
        calc {
          [false, false, true, true, true, false, false, false, true, false, true, false, false, true, true, false, true, false, true, false, false, false, false, true, false, true, false, false, true, true, true, true];
          {
            pow_4191();
            of_pow(4224, true, true, true, true, false, false, true, false, true, false, false, false, false, true, false, true, false, true, true, false, false, true, false, true, false, false, false, true, true, true, false, false);
          }
          pow_mod_crc(4224);
        }
        calc {
          [false, false, true, false, false, true, false, true, false, true, false, true, true, true, true, false, true, false, false, false, true, true, false, true, false, false, true, true, true, false, true, true];
          {
            pow_2079();
            of_pow(2112, true, true, false, true, true, true, false, false, true, false, true, true, false, false, false, true, false, true, true, true, true, false, true, false, true, false, true, false, false, true, false, false);
          }
          pow_mod_crc(2112);
        }
      }
      pow_mod_crc(4224) + pow_mod_crc(2112);
    }
  }



  lemma lut_entry_33()
  ensures bits_of_int(lut[33] as int, 64)
      == pow_mod_crc(4352) + pow_mod_crc(2176)
  {
    calc {
      bits_of_int(lut[33] as int, 64);
      bits_of_int(1779830384699404092, 64);
      {
        lemma_bits_of_int_64_split(1779830384699404092);
      }
      bits_of_int(276066108, 32) + bits_of_int(414399054, 32);
      {
        unroll_bits_of_int_32_0x10746f3c();
        unroll_bits_of_int_32_0x18b33a4e();
      }
      [false, false, true, true, true, true, false, false, true, true, true, true, false, true, true, false, false, false, true, false, true, true, true, false, false, false, false, false, true, false, false, false]+[false, true, true, true, false, false, true, false, false, true, false, true, true, true, false, false, true, true, false, false, true, true, false, true, false, false, false, true, true, false, false, false];
      {
        calc {
          [false, false, true, true, true, true, false, false, true, true, true, true, false, true, true, false, false, false, true, false, true, true, true, false, false, false, false, false, true, false, false, false];
          {
            pow_4319();
            of_pow(4352, false, false, false, true, false, false, false, false, false, true, true, true, false, true, false, false, false, true, true, false, true, true, true, true, false, false, true, true, true, true, false, false);
          }
          pow_mod_crc(4352);
        }
        calc {
          [false, true, true, true, false, false, true, false, false, true, false, true, true, true, false, false, true, true, false, false, true, true, false, true, false, false, false, true, true, false, false, false];
          {
            pow_2143();
            of_pow(2176, false, false, false, true, true, false, false, false, true, false, true, true, false, false, true, true, false, false, true, true, true, false, true, false, false, true, false, false, true, true, true, false);
          }
          pow_mod_crc(2176);
        }
      }
      pow_mod_crc(4352) + pow_mod_crc(2176);
    }
  }



  lemma lut_entry_34()
  ensures bits_of_int(lut[34] as int, 64)
      == pow_mod_crc(4480) + pow_mod_crc(2240)
  {
    calc {
      bits_of_int(lut[34] as int, 64);
      bits_of_int(17544998229926905941, 64);
      {
        lemma_bits_of_int_64_split(17544998229926905941);
      }
      bits_of_int(3349579861, 32) + bits_of_int(4085013230, 32);
      {
        unroll_bits_of_int_32_0xc7a68855();
        unroll_bits_of_int_32_0xf37c5aee();
      }
      [true, false, true, false, true, false, true, false, false, false, false, true, false, false, false, true, false, true, true, false, false, true, false, true, true, true, true, false, false, false, true, true]+[false, true, true, true, false, true, true, true, false, true, false, true, true, false, true, false, false, false, true, true, true, true, true, false, true, true, false, false, true, true, true, true];
      {
        calc {
          [true, false, true, false, true, false, true, false, false, false, false, true, false, false, false, true, false, true, true, false, false, true, false, true, true, true, true, false, false, false, true, true];
          {
            pow_4447();
            of_pow(4480, true, true, false, false, false, true, true, true, true, false, true, false, false, true, true, false, true, false, false, false, true, false, false, false, false, true, false, true, false, true, false, true);
          }
          pow_mod_crc(4480);
        }
        calc {
          [false, true, true, true, false, true, true, true, false, true, false, true, true, false, true, false, false, false, true, true, true, true, true, false, true, true, false, false, true, true, true, true];
          {
            pow_2207();
            of_pow(2240, true, true, true, true, false, false, true, true, false, true, true, true, true, true, false, false, false, true, false, true, true, false, true, false, true, true, true, false, true, true, true, false);
          }
          pow_mod_crc(2240);
        }
      }
      pow_mod_crc(4480) + pow_mod_crc(2240);
    }
  }



  lemma lut_entry_35()
  ensures bits_of_int(lut[35] as int, 64)
      == pow_mod_crc(4608) + pow_mod_crc(2304)
  {
    calc {
      bits_of_int(lut[35] as int, 64);
      bits_of_int(13176851478853032004, 64);
      {
        lemma_bits_of_int_64_split(13176851478853032004);
      }
      bits_of_int(656250948, 32) + bits_of_int(3067974811, 32);
      {
        unroll_bits_of_int_32_0x271d9844();
        unroll_bits_of_int_32_0xb6dd949b();
      }
      [false, false, true, false, false, false, true, false, false, false, false, true, true, false, false, true, true, false, true, true, true, false, false, false, true, true, true, false, false, true, false, false]+[true, true, false, true, true, false, false, true, false, false, true, false, true, false, false, true, true, false, true, true, true, false, true, true, false, true, true, false, true, true, false, true];
      {
        calc {
          [false, false, true, false, false, false, true, false, false, false, false, true, true, false, false, true, true, false, true, true, true, false, false, false, true, true, true, false, false, true, false, false];
          {
            pow_4575();
            of_pow(4608, false, false, true, false, false, true, true, true, false, false, false, true, true, true, false, true, true, false, false, true, true, false, false, false, false, true, false, false, false, true, false, false);
          }
          pow_mod_crc(4608);
        }
        calc {
          [true, true, false, true, true, false, false, true, false, false, true, false, true, false, false, true, true, false, true, true, true, false, true, true, false, true, true, false, true, true, false, true];
          {
            pow_2271();
            of_pow(2304, true, false, true, true, false, true, true, false, true, true, false, true, true, true, false, true, true, false, false, true, false, true, false, false, true, false, false, true, true, false, true, true);
          }
          pow_mod_crc(2304);
        }
      }
      pow_mod_crc(4608) + pow_mod_crc(2304);
    }
  }



  lemma lut_entry_36()
  ensures bits_of_int(lut[36] as int, 64)
      == pow_mod_crc(4736) + pow_mod_crc(2368)
  {
    calc {
      bits_of_int(lut[36] as int, 64);
      bits_of_int(6940563394906188300, 64);
      {
        lemma_bits_of_int_64_split(6940563394906188300);
      }
      bits_of_int(2390125068, 32) + bits_of_int(1615975842, 32);
      {
        unroll_bits_of_int_32_0x8e766a0c();
        unroll_bits_of_int_32_0x6051d5a2();
      }
      [false, false, true, true, false, false, false, false, false, true, false, true, false, true, true, false, false, true, true, false, true, true, true, false, false, true, true, true, false, false, false, true]+[false, true, false, false, false, true, false, true, true, false, true, false, true, false, true, true, true, false, false, false, true, false, true, false, false, false, false, false, false, true, true, false];
      {
        calc {
          [false, false, true, true, false, false, false, false, false, true, false, true, false, true, true, false, false, true, true, false, true, true, true, false, false, true, true, true, false, false, false, true];
          {
            pow_4703();
            of_pow(4736, true, false, false, false, true, true, true, false, false, true, true, true, false, true, true, false, false, true, true, false, true, false, true, false, false, false, false, false, true, true, false, false);
          }
          pow_mod_crc(4736);
        }
        calc {
          [false, true, false, false, false, true, false, true, true, false, true, false, true, false, true, true, true, false, false, false, true, false, true, false, false, false, false, false, false, true, true, false];
          {
            pow_2335();
            of_pow(2368, false, true, true, false, false, false, false, false, false, true, false, true, false, false, false, true, true, true, false, true, false, true, false, true, true, false, true, false, false, false, true, false);
          }
          pow_mod_crc(2368);
        }
      }
      pow_mod_crc(4736) + pow_mod_crc(2368);
    }
  }



  lemma lut_entry_37()
  ensures bits_of_int(lut[37] as int, 64)
      == pow_mod_crc(4864) + pow_mod_crc(2432)
  {
    calc {
      bits_of_int(lut[37] as int, 64);
      bits_of_int(8708216443325773616, 64);
      {
        lemma_bits_of_int_64_split(8708216443325773616);
      }
      bits_of_int(2477127472, 32) + bits_of_int(2027539639, 32);
      {
        unroll_bits_of_int_32_0x93a5f730();
        unroll_bits_of_int_32_0x78d9ccb7();
      }
      [false, false, false, false, true, true, false, false, true, true, true, false, true, true, true, true, true, false, true, false, false, true, false, true, true, true, false, false, true, false, false, true]+[true, true, true, false, true, true, false, true, false, false, true, true, false, false, true, true, true, false, false, true, true, false, true, true, false, false, false, true, true, true, true, false];
      {
        calc {
          [false, false, false, false, true, true, false, false, true, true, true, false, true, true, true, true, true, false, true, false, false, true, false, true, true, true, false, false, true, false, false, true];
          {
            pow_4831();
            of_pow(4864, true, false, false, true, false, false, true, true, true, false, true, false, false, true, false, true, true, true, true, true, false, true, true, true, false, false, true, true, false, false, false, false);
          }
          pow_mod_crc(4864);
        }
        calc {
          [true, true, true, false, true, true, false, true, false, false, true, true, false, false, true, true, true, false, false, true, true, false, true, true, false, false, false, true, true, true, true, false];
          {
            pow_2399();
            of_pow(2432, false, true, true, true, true, false, false, false, true, true, false, true, true, false, false, true, true, true, false, false, true, true, false, false, true, false, true, true, false, true, true, true);
          }
          pow_mod_crc(2432);
        }
      }
      pow_mod_crc(4864) + pow_mod_crc(2432);
    }
  }



  lemma lut_entry_38()
  ensures bits_of_int(lut[38] as int, 64)
      == pow_mod_crc(4992) + pow_mod_crc(2496)
  {
    calc {
      bits_of_int(lut[38] as int, 64);
      bits_of_int(1779156046316605020, 64);
      {
        lemma_bits_of_int_64_split(1779156046316605020);
      }
      bits_of_int(1823510108, 32) + bits_of_int(414242047, 32);
      {
        unroll_bits_of_int_32_0x6cb08e5c();
        unroll_bits_of_int_32_0x18b0d4ff();
      }
      [false, false, true, true, true, false, true, false, false, true, true, true, false, false, false, true, false, false, false, false, true, true, false, true, false, false, true, true, false, true, true, false]+[true, true, true, true, true, true, true, true, false, false, true, false, true, false, true, true, false, false, false, false, true, true, false, true, false, false, false, true, true, false, false, false];
      {
        calc {
          [false, false, true, true, true, false, true, false, false, true, true, true, false, false, false, true, false, false, false, false, true, true, false, true, false, false, true, true, false, true, true, false];
          {
            pow_4959();
            of_pow(4992, false, true, true, false, true, true, false, false, true, false, true, true, false, false, false, false, true, false, false, false, true, true, true, false, false, true, false, true, true, true, false, false);
          }
          pow_mod_crc(4992);
        }
        calc {
          [true, true, true, true, true, true, true, true, false, false, true, false, true, false, true, true, false, false, false, false, true, true, false, true, false, false, false, true, true, false, false, false];
          {
            pow_2463();
            of_pow(2496, false, false, false, true, true, false, false, false, true, false, true, true, false, false, false, false, true, true, false, true, false, true, false, false, true, true, true, true, true, true, true, true);
          }
          pow_mod_crc(2496);
        }
      }
      pow_mod_crc(4992) + pow_mod_crc(2496);
    }
  }



  lemma lut_entry_39()
  ensures bits_of_int(lut[39] as int, 64)
      == pow_mod_crc(5120) + pow_mod_crc(2560)
  {
    calc {
      bits_of_int(lut[39] as int, 64);
      bits_of_int(13457597343062073266, 64);
      {
        lemma_bits_of_int_64_split(13457597343062073266);
      }
      bits_of_int(1802805170, 32) + bits_of_int(3133341051, 32);
      {
        unroll_bits_of_int_32_0x6b749fb2();
        unroll_bits_of_int_32_0xbac2fd7b();
      }
      [false, true, false, false, true, true, false, true, true, true, true, true, true, false, false, true, false, false, true, false, true, true, true, false, true, true, false, true, false, true, true, false]+[true, true, false, true, true, true, true, false, true, false, true, true, true, true, true, true, false, true, false, false, false, false, true, true, false, true, false, true, true, true, false, true];
      {
        calc {
          [false, true, false, false, true, true, false, true, true, true, true, true, true, false, false, true, false, false, true, false, true, true, true, false, true, true, false, true, false, true, true, false];
          {
            pow_5087();
            of_pow(5120, false, true, true, false, true, false, true, true, false, true, true, true, false, true, false, false, true, false, false, true, true, true, true, true, true, false, true, true, false, false, true, false);
          }
          pow_mod_crc(5120);
        }
        calc {
          [true, true, false, true, true, true, true, false, true, false, true, true, true, true, true, true, false, true, false, false, false, false, true, true, false, true, false, true, true, true, false, true];
          {
            pow_2527();
            of_pow(2560, true, false, true, true, true, false, true, false, true, true, false, false, false, false, true, false, true, true, true, true, true, true, false, true, false, true, true, true, true, false, true, true);
          }
          pow_mod_crc(2560);
        }
      }
      pow_mod_crc(5120) + pow_mod_crc(2560);
    }
  }



  lemma lut_entry_40()
  ensures bits_of_int(lut[40] as int, 64)
      == pow_mod_crc(5248) + pow_mod_crc(2624)
  {
    calc {
      bits_of_int(lut[40] as int, 64);
      bits_of_int(2446538286958895619, 64);
      {
        lemma_bits_of_int_64_split(2446538286958895619);
      }
      bits_of_int(328458755, 32) + bits_of_int(569629084, 32);
      {
        unroll_bits_of_int_32_0x1393e203();
        unroll_bits_of_int_32_0x21f3d99c();
      }
      [true, true, false, false, false, false, false, false, false, true, false, false, false, true, true, true, true, true, false, false, true, false, false, true, true, true, false, false, true, false, false, false]+[false, false, true, true, true, false, false, true, true, false, false, true, true, false, true, true, true, true, false, false, true, true, true, true, true, false, false, false, false, true, false, false];
      {
        calc {
          [true, true, false, false, false, false, false, false, false, true, false, false, false, true, true, true, true, true, false, false, true, false, false, true, true, true, false, false, true, false, false, false];
          {
            pow_5215();
            of_pow(5248, false, false, false, true, false, false, true, true, true, false, false, true, false, false, true, true, true, true, true, false, false, false, true, false, false, false, false, false, false, false, true, true);
          }
          pow_mod_crc(5248);
        }
        calc {
          [false, false, true, true, true, false, false, true, true, false, false, true, true, false, true, true, true, true, false, false, true, true, true, true, true, false, false, false, false, true, false, false];
          {
            pow_2591();
            of_pow(2624, false, false, true, false, false, false, false, true, true, true, true, true, false, false, true, true, true, true, false, true, true, false, false, true, true, false, false, true, true, true, false, false);
          }
          pow_mod_crc(2624);
        }
      }
      pow_mod_crc(5248) + pow_mod_crc(2624);
    }
  }



  lemma lut_entry_41()
  ensures bits_of_int(lut[41] as int, 64)
      == pow_mod_crc(5376) + pow_mod_crc(2688)
  {
    calc {
      bits_of_int(lut[41] as int, 64);
      bits_of_int(11965185132371076654, 64);
      {
        lemma_bits_of_int_64_split(11965185132371076654);
      }
      bits_of_int(3468912174, 32) + bits_of_int(2785861755, 32);
      {
        unroll_bits_of_int_32_0xcec3662e();
        unroll_bits_of_int_32_0xa60ce07b();
      }
      [false, true, true, true, false, true, false, false, false, true, true, false, false, true, true, false, true, true, false, false, false, false, true, true, false, true, true, true, false, false, true, true]+[true, true, false, true, true, true, true, false, false, false, false, false, false, true, true, true, false, false, true, true, false, false, false, false, false, true, true, false, false, true, false, true];
      {
        calc {
          [false, true, true, true, false, true, false, false, false, true, true, false, false, true, true, false, true, true, false, false, false, false, true, true, false, true, true, true, false, false, true, true];
          {
            pow_5343();
            of_pow(5376, true, true, false, false, true, true, true, false, true, true, false, false, false, false, true, true, false, true, true, false, false, true, true, false, false, false, true, false, true, true, true, false);
          }
          pow_mod_crc(5376);
        }
        calc {
          [true, true, false, true, true, true, true, false, false, false, false, false, false, true, true, true, false, false, true, true, false, false, false, false, false, true, true, false, false, true, false, true];
          {
            pow_2655();
            of_pow(2688, true, false, true, false, false, true, true, false, false, false, false, false, true, true, false, false, true, true, true, false, false, false, false, false, false, true, true, true, true, false, true, true);
          }
          pow_mod_crc(2688);
        }
      }
      pow_mod_crc(5376) + pow_mod_crc(2688);
    }
  }



  lemma lut_entry_42()
  ensures bits_of_int(lut[42] as int, 64)
      == pow_mod_crc(5504) + pow_mod_crc(2752)
  {
    calc {
      bits_of_int(lut[42] as int, 64);
      bits_of_int(10310287747851818427, 64);
      {
        lemma_bits_of_int_64_split(10310287747851818427);
      }
      bits_of_int(2529498555, 32) + bits_of_int(2400550932, 32);
      {
        unroll_bits_of_int_32_0x96c515bb();
        unroll_bits_of_int_32_0x8f158014();
      }
      [true, true, false, true, true, true, false, true, true, false, true, false, true, false, false, false, true, false, true, false, false, false, true, true, false, true, true, false, true, false, false, true]+[false, false, true, false, true, false, false, false, false, false, false, false, false, false, false, true, true, false, true, false, true, false, false, false, true, true, true, true, false, false, false, true];
      {
        calc {
          [true, true, false, true, true, true, false, true, true, false, true, false, true, false, false, false, true, false, true, false, false, false, true, true, false, true, true, false, true, false, false, true];
          {
            pow_5471();
            of_pow(5504, true, false, false, true, false, true, true, false, true, true, false, false, false, true, false, true, false, false, false, true, false, true, false, true, true, false, true, true, true, false, true, true);
          }
          pow_mod_crc(5504);
        }
        calc {
          [false, false, true, false, true, false, false, false, false, false, false, false, false, false, false, true, true, false, true, false, true, false, false, false, true, true, true, true, false, false, false, true];
          {
            pow_2719();
            of_pow(2752, true, false, false, false, true, true, true, true, false, false, false, true, false, true, false, true, true, false, false, false, false, false, false, false, false, false, false, true, false, true, false, false);
          }
          pow_mod_crc(2752);
        }
      }
      pow_mod_crc(5504) + pow_mod_crc(2752);
    }
  }



  lemma lut_entry_43()
  ensures bits_of_int(lut[43] as int, 64)
      == pow_mod_crc(5632) + pow_mod_crc(2816)
  {
    calc {
      bits_of_int(lut[43] as int, 64);
      bits_of_int(14879675417865506410, 64);
      {
        lemma_bits_of_int_64_split(14879675417865506410);
      }
      bits_of_int(3875294826, 32) + bits_of_int(3464444404, 32);
      {
        unroll_bits_of_int_32_0xe6fc4e6a();
        unroll_bits_of_int_32_0xce7f39f4();
      }
      [false, true, false, true, false, true, true, false, false, true, true, true, false, false, true, false, false, false, true, true, true, true, true, true, false, true, true, false, false, true, true, true]+[false, false, true, false, true, true, true, true, true, false, false, true, true, true, false, false, true, true, true, true, true, true, true, false, false, true, true, true, false, false, true, true];
      {
        calc {
          [false, true, false, true, false, true, true, false, false, true, true, true, false, false, true, false, false, false, true, true, true, true, true, true, false, true, true, false, false, true, true, true];
          {
            pow_5599();
            of_pow(5632, true, true, true, false, false, true, true, false, true, true, true, true, true, true, false, false, false, true, false, false, true, true, true, false, false, true, true, false, true, false, true, false);
          }
          pow_mod_crc(5632);
        }
        calc {
          [false, false, true, false, true, true, true, true, true, false, false, true, true, true, false, false, true, true, true, true, true, true, true, false, false, true, true, true, false, false, true, true];
          {
            pow_2783();
            of_pow(2816, true, true, false, false, true, true, true, false, false, true, true, true, true, true, true, true, false, false, true, true, true, false, false, true, true, true, true, true, false, true, false, false);
          }
          pow_mod_crc(2816);
        }
      }
      pow_mod_crc(5632) + pow_mod_crc(2816);
    }
  }



  lemma lut_entry_44()
  ensures bits_of_int(lut[44] as int, 64)
      == pow_mod_crc(5760) + pow_mod_crc(2880)
  {
    calc {
      bits_of_int(lut[44] as int, 64);
      bits_of_int(11530437666527493002, 64);
      {
        lemma_bits_of_int_64_split(11530437666527493002);
      }
      bits_of_int(2183641994, 32) + bits_of_int(2684639223, 32);
      {
        unroll_bits_of_int_32_0x8227bb8a();
        unroll_bits_of_int_32_0xa00457f7();
      }
      [false, true, false, true, false, false, false, true, true, true, false, true, true, true, false, true, true, true, true, false, false, true, false, false, false, true, false, false, false, false, false, true]+[true, true, true, false, true, true, true, true, true, true, true, false, true, false, true, false, false, false, true, false, false, false, false, false, false, false, false, false, false, true, false, true];
      {
        calc {
          [false, true, false, true, false, false, false, true, true, true, false, true, true, true, false, true, true, true, true, false, false, true, false, false, false, true, false, false, false, false, false, true];
          {
            pow_5727();
            of_pow(5760, true, false, false, false, false, false, true, false, false, false, true, false, false, true, true, true, true, false, true, true, true, false, true, true, true, false, false, false, true, false, true, false);
          }
          pow_mod_crc(5760);
        }
        calc {
          [true, true, true, false, true, true, true, true, true, true, true, false, true, false, true, false, false, false, true, false, false, false, false, false, false, false, false, false, false, true, false, true];
          {
            pow_2847();
            of_pow(2880, true, false, true, false, false, false, false, false, false, false, false, false, false, true, false, false, false, true, false, true, false, true, true, true, true, true, true, true, false, true, true, true);
          }
          pow_mod_crc(2880);
        }
      }
      pow_mod_crc(5760) + pow_mod_crc(2880);
    }
  }



  lemma lut_entry_45()
  ensures bits_of_int(lut[45] as int, 64)
      == pow_mod_crc(5888) + pow_mod_crc(2944)
  {
    calc {
      bits_of_int(lut[45] as int, 64);
      bits_of_int(7050436166516819816, 64);
      {
        lemma_bits_of_int_64_split(7050436166516819816);
      }
      bits_of_int(2966243176, 32) + bits_of_int(1641557590, 32);
      {
        unroll_bits_of_int_32_0xb0cd4768();
        unroll_bits_of_int_32_0x61d82e56();
      }
      [false, false, false, true, false, true, true, false, true, true, true, false, false, false, true, false, true, false, true, true, false, false, true, true, false, false, false, false, true, true, false, true]+[false, true, true, false, true, false, true, false, false, true, true, true, false, true, false, false, false, false, false, true, true, false, true, true, true, false, false, false, false, true, true, false];
      {
        calc {
          [false, false, false, true, false, true, true, false, true, true, true, false, false, false, true, false, true, false, true, true, false, false, true, true, false, false, false, false, true, true, false, true];
          {
            pow_5855();
            of_pow(5888, true, false, true, true, false, false, false, false, true, true, false, false, true, true, false, true, false, true, false, false, false, true, true, true, false, true, true, false, true, false, false, false);
          }
          pow_mod_crc(5888);
        }
        calc {
          [false, true, true, false, true, false, true, false, false, true, true, true, false, true, false, false, false, false, false, true, true, false, true, true, true, false, false, false, false, true, true, false];
          {
            pow_2911();
            of_pow(2944, false, true, true, false, false, false, false, true, true, true, false, true, true, false, false, false, false, false, true, false, true, true, true, false, false, true, false, true, false, true, true, false);
          }
          pow_mod_crc(2944);
        }
      }
      pow_mod_crc(5888) + pow_mod_crc(2944);
    }
  }



  lemma lut_entry_46()
  ensures bits_of_int(lut[46] as int, 64)
      == pow_mod_crc(6016) + pow_mod_crc(3008)
  {
    calc {
      bits_of_int(lut[46] as int, 64);
      bits_of_int(10190850199053139765, 64);
      {
        lemma_bits_of_int_64_split(10190850199053139765);
      }
      bits_of_int(969408309, 32) + bits_of_int(2372742211, 32);
      {
        unroll_bits_of_int_32_0x39c7ff35();
        unroll_bits_of_int_32_0x8d6d2c43();
      }
      [true, false, true, false, true, true, false, false, true, true, true, true, true, true, true, true, true, true, true, false, false, false, true, true, true, false, false, true, true, true, false, false]+[true, true, false, false, false, false, true, false, false, false, true, true, false, true, false, false, true, false, true, true, false, true, true, false, true, false, true, true, false, false, false, true];
      {
        calc {
          [true, false, true, false, true, true, false, false, true, true, true, true, true, true, true, true, true, true, true, false, false, false, true, true, true, false, false, true, true, true, false, false];
          {
            pow_5983();
            of_pow(6016, false, false, true, true, true, false, false, true, true, true, false, false, false, true, true, true, true, true, true, true, true, true, true, true, false, false, true, true, false, true, false, true);
          }
          pow_mod_crc(6016);
        }
        calc {
          [true, true, false, false, false, false, true, false, false, false, true, true, false, true, false, false, true, false, true, true, false, true, true, false, true, false, true, true, false, false, false, true];
          {
            pow_2975();
            of_pow(3008, true, false, false, false, true, true, false, true, false, true, true, false, true, true, false, true, false, false, true, false, true, true, false, false, false, true, false, false, false, false, true, true);
          }
          pow_mod_crc(3008);
        }
      }
      pow_mod_crc(6016) + pow_mod_crc(3008);
    }
  }



  lemma lut_entry_47()
  ensures bits_of_int(lut[47] as int, 64)
      == pow_mod_crc(6144) + pow_mod_crc(3072)
  {
    calc {
      bits_of_int(lut[47] as int, 64);
      bits_of_int(15163885627061338716, 64);
      {
        lemma_bits_of_int_64_split(15163885627061338716);
      }
      bits_of_int(3617882716, 32) + bits_of_int(3530617250, 32);
      {
        unroll_bits_of_int_32_0xd7a4825c();
        unroll_bits_of_int_32_0xd270f1a2();
      }
      [false, false, true, true, true, false, true, false, false, true, false, false, false, false, false, true, false, false, true, false, false, true, false, true, true, true, true, false, true, false, true, true]+[false, true, false, false, false, true, false, true, true, false, false, false, true, true, true, true, false, false, false, false, true, true, true, false, false, true, false, false, true, false, true, true];
      {
        calc {
          [false, false, true, true, true, false, true, false, false, true, false, false, false, false, false, true, false, false, true, false, false, true, false, true, true, true, true, false, true, false, true, true];
          {
            pow_6111();
            of_pow(6144, true, true, false, true, false, true, true, true, true, false, true, false, false, true, false, false, true, false, false, false, false, false, true, false, false, true, false, true, true, true, false, false);
          }
          pow_mod_crc(6144);
        }
        calc {
          [false, true, false, false, false, true, false, true, true, false, false, false, true, true, true, true, false, false, false, false, true, true, true, false, false, true, false, false, true, false, true, true];
          {
            pow_3039();
            of_pow(3072, true, true, false, true, false, false, true, false, false, true, true, true, false, false, false, false, true, true, true, true, false, false, false, true, true, false, true, false, false, false, true, false);
          }
          pow_mod_crc(3072);
        }
      }
      pow_mod_crc(6144) + pow_mod_crc(3072);
    }
  }



  lemma lut_entry_48()
  ensures bits_of_int(lut[48] as int, 64)
      == pow_mod_crc(6272) + pow_mod_crc(3136)
  {
    calc {
      bits_of_int(lut[48] as int, 64);
      bits_of_int(48459665208738891, 64);
      {
        lemma_bits_of_int_64_split(48459665208738891);
      }
      bits_of_int(179536971, 32) + bits_of_int(11282895, 32);
      {
        unroll_bits_of_int_32_0x0ab3844b();
        unroll_bits_of_int_32_0x00ac29cf();
      }
      [true, true, false, true, false, false, true, false, false, false, true, false, false, false, false, true, true, true, false, false, true, true, false, true, false, true, false, true, false, false, false, false]+[true, true, true, true, false, false, true, true, true, false, false, true, false, true, false, false, false, false, true, true, false, true, false, true, false, false, false, false, false, false, false, false];
      {
        calc {
          [true, true, false, true, false, false, true, false, false, false, true, false, false, false, false, true, true, true, false, false, true, true, false, true, false, true, false, true, false, false, false, false];
          {
            pow_6239();
            of_pow(6272, false, false, false, false, true, false, true, false, true, false, true, true, false, false, true, true, true, false, false, false, false, true, false, false, false, true, false, false, true, false, true, true);
          }
          pow_mod_crc(6272);
        }
        calc {
          [true, true, true, true, false, false, true, true, true, false, false, true, false, true, false, false, false, false, true, true, false, true, false, true, false, false, false, false, false, false, false, false];
          {
            pow_3103();
            of_pow(3136, false, false, false, false, false, false, false, false, true, false, true, false, true, true, false, false, false, false, true, false, true, false, false, true, true, true, false, false, true, true, true, true);
          }
          pow_mod_crc(3136);
        }
      }
      pow_mod_crc(6272) + pow_mod_crc(3136);
    }
  }



  lemma lut_entry_49()
  ensures bits_of_int(lut[49] as int, 64)
      == pow_mod_crc(6400) + pow_mod_crc(3200)
  {
    calc {
      bits_of_int(lut[49] as int, 64);
      bits_of_int(14274581905749299986, 64);
      {
        lemma_bits_of_int_64_split(14274581905749299986);
      }
      bits_of_int(23581458, 32) + bits_of_int(3323560093, 32);
      {
        unroll_bits_of_int_32_0x0167d312();
        unroll_bits_of_int_32_0xc619809d();
      }
      [false, true, false, false, true, false, false, false, true, true, false, false, true, false, true, true, true, true, true, false, false, true, true, false, true, false, false, false, false, false, false, false]+[true, false, true, true, true, false, false, true, false, false, false, false, false, false, false, true, true, false, false, true, true, false, false, false, false, true, true, false, false, false, true, true];
      {
        calc {
          [false, true, false, false, true, false, false, false, true, true, false, false, true, false, true, true, true, true, true, false, false, true, true, false, true, false, false, false, false, false, false, false];
          {
            pow_6367();
            of_pow(6400, false, false, false, false, false, false, false, true, false, true, true, false, false, true, true, true, true, true, false, true, false, false, true, true, false, false, false, true, false, false, true, false);
          }
          pow_mod_crc(6400);
        }
        calc {
          [true, false, true, true, true, false, false, true, false, false, false, false, false, false, false, true, true, false, false, true, true, false, false, false, false, true, true, false, false, false, true, true];
          {
            pow_3167();
            of_pow(3200, true, true, false, false, false, true, true, false, false, false, false, true, true, false, false, true, true, false, false, false, false, false, false, false, true, false, false, true, true, true, false, true);
          }
          pow_mod_crc(3200);
        }
      }
      pow_mod_crc(6400) + pow_mod_crc(3200);
    }
  }



  lemma lut_entry_50()
  ensures bits_of_int(lut[50] as int, 64)
      == pow_mod_crc(6528) + pow_mod_crc(3264)
  {
    calc {
      bits_of_int(lut[50] as int, 64);
      bits_of_int(16838386809552987460, 64);
      {
        lemma_bits_of_int_64_split(16838386809552987460);
      }
      bits_of_int(4127679812, 32) + bits_of_int(3920492438, 32);
      {
        unroll_bits_of_int_32_0xf6076544();
        unroll_bits_of_int_32_0xe9adf796();
      }
      [false, false, true, false, false, false, true, false, true, false, true, false, false, true, true, false, true, true, true, false, false, false, false, false, false, true, true, false, true, true, true, true]+[false, true, true, false, true, false, false, true, true, true, true, false, true, true, true, true, true, false, true, true, false, true, false, true, true, false, false, true, false, true, true, true];
      {
        calc {
          [false, false, true, false, false, false, true, false, true, false, true, false, false, true, true, false, true, true, true, false, false, false, false, false, false, true, true, false, true, true, true, true];
          {
            pow_6495();
            of_pow(6528, true, true, true, true, false, true, true, false, false, false, false, false, false, true, true, true, false, true, true, false, false, true, false, true, false, true, false, false, false, true, false, false);
          }
          pow_mod_crc(6528);
        }
        calc {
          [false, true, true, false, true, false, false, true, true, true, true, false, true, true, true, true, true, false, true, true, false, true, false, true, true, false, false, true, false, true, true, true];
          {
            pow_3231();
            of_pow(3264, true, true, true, false, true, false, false, true, true, false, true, false, true, true, false, true, true, true, true, true, false, true, true, true, true, false, false, true, false, true, true, false);
          }
          pow_mod_crc(3264);
        }
      }
      pow_mod_crc(6528) + pow_mod_crc(3264);
    }
  }



  lemma lut_entry_51()
  ensures bits_of_int(lut[51] as int, 64)
      == pow_mod_crc(6656) + pow_mod_crc(3328)
  {
    calc {
      bits_of_int(lut[51] as int, 64);
      bits_of_int(3115554558319175178, 64);
      {
        lemma_bits_of_int_64_split(3115554558319175178);
      }
      bits_of_int(653698570, 32) + bits_of_int(725396573, 32);
      {
        unroll_bits_of_int_32_0x26f6a60a();
        unroll_bits_of_int_32_0x2b3cac5d();
      }
      [false, true, false, true, false, false, false, false, false, true, true, false, false, true, false, true, false, true, true, false, true, true, true, true, false, true, true, false, false, true, false, false]+[true, false, true, true, true, false, true, false, false, false, true, true, false, true, false, true, false, false, true, true, true, true, false, false, true, true, false, true, false, true, false, false];
      {
        calc {
          [false, true, false, true, false, false, false, false, false, true, true, false, false, true, false, true, false, true, true, false, true, true, true, true, false, true, true, false, false, true, false, false];
          {
            pow_6623();
            of_pow(6656, false, false, true, false, false, true, true, false, true, true, true, true, false, true, true, false, true, false, true, false, false, true, true, false, false, false, false, false, true, false, true, false);
          }
          pow_mod_crc(6656);
        }
        calc {
          [true, false, true, true, true, false, true, false, false, false, true, true, false, true, false, true, false, false, true, true, true, true, false, false, true, true, false, true, false, true, false, false];
          {
            pow_3295();
            of_pow(3328, false, false, true, false, true, false, true, true, false, false, true, true, true, true, false, false, true, false, true, false, true, true, false, false, false, true, false, true, true, true, false, true);
          }
          pow_mod_crc(3328);
        }
      }
      pow_mod_crc(6656) + pow_mod_crc(3328);
    }
  }



  lemma lut_entry_52()
  ensures bits_of_int(lut[52] as int, 64)
      == pow_mod_crc(6784) + pow_mod_crc(3392)
  {
    calc {
      bits_of_int(lut[52] as int, 64);
      bits_of_int(10836658186644210111, 64);
      {
        lemma_bits_of_int_64_split(10836658186644210111);
      }
      bits_of_int(2806104511, 32) + bits_of_int(2523106100, 32);
      {
        unroll_bits_of_int_32_0xa741c1bf();
        unroll_bits_of_int_32_0x96638b34();
      }
      [true, true, true, true, true, true, false, true, true, false, false, false, false, false, true, true, true, false, false, false, false, false, true, false, true, true, true, false, false, true, false, true]+[false, false, true, false, true, true, false, false, true, true, false, true, false, false, false, true, true, true, false, false, false, true, true, false, false, true, true, false, true, false, false, true];
      {
        calc {
          [true, true, true, true, true, true, false, true, true, false, false, false, false, false, true, true, true, false, false, false, false, false, true, false, true, true, true, false, false, true, false, true];
          {
            pow_6751();
            of_pow(6784, true, false, true, false, false, true, true, true, false, true, false, false, false, false, false, true, true, true, false, false, false, false, false, true, true, false, true, true, true, true, true, true);
          }
          pow_mod_crc(6784);
        }
        calc {
          [false, false, true, false, true, true, false, false, true, true, false, true, false, false, false, true, true, true, false, false, false, true, true, false, false, true, true, false, true, false, false, true];
          {
            pow_3359();
            of_pow(3392, true, false, false, true, false, true, true, false, false, true, true, false, false, false, true, true, true, false, false, false, true, false, true, true, false, false, true, true, false, true, false, false);
          }
          pow_mod_crc(3392);
        }
      }
      pow_mod_crc(6784) + pow_mod_crc(3392);
    }
  }



  lemma lut_entry_53()
  ensures bits_of_int(lut[53] as int, 64)
      == pow_mod_crc(6912) + pow_mod_crc(3456)
  {
    calc {
      bits_of_int(lut[53] as int, 64);
      bits_of_int(7315599947957066187, 64);
      {
        lemma_bits_of_int_64_split(7315599947957066187);
      }
      bits_of_int(2564348363, 32) + bits_of_int(1703295844, 32);
      {
        unroll_bits_of_int_32_0x98d8d9cb();
        unroll_bits_of_int_32_0x65863b64();
      }
      [true, true, false, true, false, false, true, true, true, false, false, true, true, false, true, true, false, false, false, true, true, false, true, true, false, false, false, true, true, false, false, true]+[false, false, true, false, false, true, true, false, true, true, false, true, true, true, false, false, false, true, true, false, false, false, false, true, true, false, true, false, false, true, true, false];
      {
        calc {
          [true, true, false, true, false, false, true, true, true, false, false, true, true, false, true, true, false, false, false, true, true, false, true, true, false, false, false, true, true, false, false, true];
          {
            pow_6879();
            of_pow(6912, true, false, false, true, true, false, false, false, true, true, false, true, true, false, false, false, true, true, false, true, true, false, false, true, true, true, false, false, true, false, true, true);
          }
          pow_mod_crc(6912);
        }
        calc {
          [false, false, true, false, false, true, true, false, true, true, false, true, true, true, false, false, false, true, true, false, false, false, false, true, true, false, true, false, false, true, true, false];
          {
            pow_3423();
            of_pow(3456, false, true, true, false, false, true, false, true, true, false, false, false, false, true, true, false, false, false, true, true, true, false, true, true, false, true, true, false, false, true, false, false);
          }
          pow_mod_crc(3456);
        }
      }
      pow_mod_crc(6912) + pow_mod_crc(3456);
    }
  }



  lemma lut_entry_54()
  ensures bits_of_int(lut[54] as int, 64)
      == pow_mod_crc(7040) + pow_mod_crc(3520)
  {
    calc {
      bits_of_int(lut[54] as int, 64);
      bits_of_int(16206752264524909724, 64);
      {
        lemma_bits_of_int_64_split(16206752264524909724);
      }
      bits_of_int(1237568668, 32) + bits_of_int(3773428561, 32);
      {
        unroll_bits_of_int_32_0x49c3cc9c();
        unroll_bits_of_int_32_0xe0e9f351();
      }
      [false, false, true, true, true, false, false, true, false, false, true, true, false, false, true, true, true, true, false, false, false, false, true, true, true, false, false, true, false, false, true, false]+[true, false, false, false, true, false, true, false, true, true, false, false, true, true, true, true, true, false, false, true, false, true, true, true, false, false, false, false, false, true, true, true];
      {
        calc {
          [false, false, true, true, true, false, false, true, false, false, true, true, false, false, true, true, true, true, false, false, false, false, true, true, true, false, false, true, false, false, true, false];
          {
            pow_7007();
            of_pow(7040, false, true, false, false, true, false, false, true, true, true, false, false, false, false, true, true, true, true, false, false, true, true, false, false, true, false, false, true, true, true, false, false);
          }
          pow_mod_crc(7040);
        }
        calc {
          [true, false, false, false, true, false, true, false, true, true, false, false, true, true, true, true, true, false, false, true, false, true, true, true, false, false, false, false, false, true, true, true];
          {
            pow_3487();
            of_pow(3520, true, true, true, false, false, false, false, false, true, true, true, false, true, false, false, true, true, true, true, true, false, false, true, true, false, true, false, true, false, false, false, true);
          }
          pow_mod_crc(3520);
        }
      }
      pow_mod_crc(7040) + pow_mod_crc(3520);
    }
  }



  lemma lut_entry_55()
  ensures bits_of_int(lut[55] as int, 64)
      == pow_mod_crc(7168) + pow_mod_crc(3584)
  {
    calc {
      bits_of_int(lut[55] as int, 64);
      bits_of_int(1946462683335026810, 64);
      {
        lemma_bits_of_int_64_split(1946462683335026810);
      }
      bits_of_int(1757210746, 32) + bits_of_int(453196159, 32);
      {
        unroll_bits_of_int_32_0x68bce87a();
        unroll_bits_of_int_32_0x1b03397f();
      }
      [false, true, false, true, true, true, true, false, false, false, false, true, false, true, true, true, false, false, true, true, true, true, false, true, false, false, false, true, false, true, true, false]+[true, true, true, true, true, true, true, false, true, false, false, true, true, true, false, false, true, true, false, false, false, false, false, false, true, true, false, true, true, false, false, false];
      {
        calc {
          [false, true, false, true, true, true, true, false, false, false, false, true, false, true, true, true, false, false, true, true, true, true, false, true, false, false, false, true, false, true, true, false];
          {
            pow_7135();
            of_pow(7168, false, true, true, false, true, false, false, false, true, false, true, true, true, true, false, false, true, true, true, false, true, false, false, false, false, true, true, true, true, false, true, false);
          }
          pow_mod_crc(7168);
        }
        calc {
          [true, true, true, true, true, true, true, false, true, false, false, true, true, true, false, false, true, true, false, false, false, false, false, false, true, true, false, true, true, false, false, false];
          {
            pow_3551();
            of_pow(3584, false, false, false, true, true, false, true, true, false, false, false, false, false, false, true, true, false, false, true, true, true, false, false, true, false, true, true, true, true, true, true, true);
          }
          pow_mod_crc(3584);
        }
      }
      pow_mod_crc(7168) + pow_mod_crc(3584);
    }
  }



  lemma lut_entry_56()
  ensures bits_of_int(lut[56] as int, 64)
      == pow_mod_crc(7296) + pow_mod_crc(3648)
  {
    calc {
      bits_of_int(lut[56] as int, 64);
      bits_of_int(11164457755855802423, 64);
      {
        lemma_bits_of_int_64_split(11164457755855802423);
      }
      bits_of_int(1470353463, 32) + bits_of_int(2599427885, 32);
      {
        unroll_bits_of_int_32_0x57a3d037();
        unroll_bits_of_int_32_0x9af01f2d();
      }
      [true, true, true, false, true, true, false, false, false, false, false, false, true, false, true, true, true, true, false, false, false, true, false, true, true, true, true, false, true, false, true, false]+[true, false, true, true, false, true, false, false, true, true, true, true, true, false, false, false, false, false, false, false, true, true, true, true, false, true, false, true, true, false, false, true];
      {
        calc {
          [true, true, true, false, true, true, false, false, false, false, false, false, true, false, true, true, true, true, false, false, false, true, false, true, true, true, true, false, true, false, true, false];
          {
            pow_7263();
            of_pow(7296, false, true, false, true, false, true, true, true, true, false, true, false, false, false, true, true, true, true, false, true, false, false, false, false, false, false, true, true, false, true, true, true);
          }
          pow_mod_crc(7296);
        }
        calc {
          [true, false, true, true, false, true, false, false, true, true, true, true, true, false, false, false, false, false, false, false, true, true, true, true, false, true, false, true, true, false, false, true];
          {
            pow_3615();
            of_pow(3648, true, false, false, true, true, false, true, false, true, true, true, true, false, false, false, false, false, false, false, true, true, true, true, true, false, false, true, false, true, true, false, true);
          }
          pow_mod_crc(3648);
        }
      }
      pow_mod_crc(7296) + pow_mod_crc(3648);
    }
  }



  lemma lut_entry_57()
  ensures bits_of_int(lut[57] as int, 64)
      == pow_mod_crc(7424) + pow_mod_crc(3712)
  {
    calc {
      bits_of_int(lut[57] as int, 64);
      bits_of_int(16985470844167191611, 64);
      {
        lemma_bits_of_int_64_split(16985470844167191611);
      }
      bits_of_int(1767308347, 32) + bits_of_int(3954738109, 32);
      {
        unroll_bits_of_int_32_0x6956fc3b();
        unroll_bits_of_int_32_0xebb883bd();
      }
      [true, true, false, true, true, true, false, false, false, false, true, true, true, true, true, true, false, true, true, false, true, false, true, false, true, false, false, true, false, true, true, false]+[true, false, true, true, true, true, false, true, true, true, false, false, false, false, false, true, false, false, false, true, true, true, false, true, true, true, false, true, false, true, true, true];
      {
        calc {
          [true, true, false, true, true, true, false, false, false, false, true, true, true, true, true, true, false, true, true, false, true, false, true, false, true, false, false, true, false, true, true, false];
          {
            pow_7391();
            of_pow(7424, false, true, true, false, true, false, false, true, false, true, false, true, false, true, true, false, true, true, true, true, true, true, false, false, false, false, true, true, true, false, true, true);
          }
          pow_mod_crc(7424);
        }
        calc {
          [true, false, true, true, true, true, false, true, true, true, false, false, false, false, false, true, false, false, false, true, true, true, false, true, true, true, false, true, false, true, true, true];
          {
            pow_3679();
            of_pow(3712, true, true, true, false, true, false, true, true, true, false, true, true, true, false, false, false, true, false, false, false, false, false, true, true, true, false, true, true, true, true, false, true);
          }
          pow_mod_crc(3712);
        }
      }
      pow_mod_crc(7424) + pow_mod_crc(3712);
    }
  }



  lemma lut_entry_58()
  ensures bits_of_int(lut[58] as int, 64)
      == pow_mod_crc(7552) + pow_mod_crc(3776)
  {
    calc {
      bits_of_int(lut[58] as int, 64);
      bits_of_int(3242383714677262472, 64);
      {
        lemma_bits_of_int_64_split(3242383714677262472);
      }
      bits_of_int(1121552520, 32) + bits_of_int(754926287, 32);
      {
        unroll_bits_of_int_32_0x42d98888();
        unroll_bits_of_int_32_0x2cff42cf();
      }
      [false, false, false, true, false, false, false, true, false, false, false, true, false, false, false, true, true, false, false, true, true, false, true, true, false, true, false, false, false, false, true, false]+[true, true, true, true, false, false, true, true, false, true, false, false, false, false, true, false, true, true, true, true, true, true, true, true, false, false, true, true, false, true, false, false];
      {
        calc {
          [false, false, false, true, false, false, false, true, false, false, false, true, false, false, false, true, true, false, false, true, true, false, true, true, false, true, false, false, false, false, true, false];
          {
            pow_7519();
            of_pow(7552, false, true, false, false, false, false, true, false, true, true, false, true, true, false, false, true, true, false, false, false, true, false, false, false, true, false, false, false, true, false, false, false);
          }
          pow_mod_crc(7552);
        }
        calc {
          [true, true, true, true, false, false, true, true, false, true, false, false, false, false, true, false, true, true, true, true, true, true, true, true, false, false, true, true, false, true, false, false];
          {
            pow_3743();
            of_pow(3776, false, false, true, false, true, true, false, false, true, true, true, true, true, true, true, true, false, true, false, false, false, false, true, false, true, true, false, false, true, true, true, true);
          }
          pow_mod_crc(3776);
        }
      }
      pow_mod_crc(7552) + pow_mod_crc(3776);
    }
  }



  lemma lut_entry_59()
  ensures bits_of_int(lut[59] as int, 64)
      == pow_mod_crc(7680) + pow_mod_crc(3840)
  {
    calc {
      bits_of_int(lut[59] as int, 64);
      bits_of_int(12962252703742945679, 64);
      {
        lemma_bits_of_int_64_split(12962252703742945679);
      }
      bits_of_int(930212239, 32) + bits_of_int(3018009640, 32);
      {
        unroll_bits_of_int_32_0x3771e98f();
        unroll_bits_of_int_32_0xb3e32c28();
      }
      [true, true, true, true, false, false, false, true, true, false, false, true, false, true, true, true, true, false, false, false, true, true, true, false, true, true, true, false, true, true, false, false]+[false, false, false, true, false, true, false, false, false, false, true, true, false, true, false, false, true, true, false, false, false, true, true, true, true, true, false, false, true, true, false, true];
      {
        calc {
          [true, true, true, true, false, false, false, true, true, false, false, true, false, true, true, true, true, false, false, false, true, true, true, false, true, true, true, false, true, true, false, false];
          {
            pow_7647();
            of_pow(7680, false, false, true, true, false, true, true, true, false, true, true, true, false, false, false, true, true, true, true, false, true, false, false, true, true, false, false, false, true, true, true, true);
          }
          pow_mod_crc(7680);
        }
        calc {
          [false, false, false, true, false, true, false, false, false, false, true, true, false, true, false, false, true, true, false, false, false, true, true, true, true, true, false, false, true, true, false, true];
          {
            pow_3807();
            of_pow(3840, true, false, true, true, false, false, true, true, true, true, true, false, false, false, true, true, false, false, true, false, true, true, false, false, false, false, true, false, true, false, false, false);
          }
          pow_mod_crc(3840);
        }
      }
      pow_mod_crc(7680) + pow_mod_crc(3840);
    }
  }



  lemma lut_entry_60()
  ensures bits_of_int(lut[60] as int, 64)
      == pow_mod_crc(7808) + pow_mod_crc(3904)
  {
    calc {
      bits_of_int(lut[60] as int, 64);
      bits_of_int(9868048941699490777, 64);
      {
        lemma_bits_of_int_64_split(9868048941699490777);
      }
      bits_of_int(3022709721, 32) + bits_of_int(2297584186, 32);
      {
        unroll_bits_of_int_32_0xb42ae3d9();
        unroll_bits_of_int_32_0x88f25a3a();
      }
      [true, false, false, true, true, false, true, true, true, true, false, false, false, true, true, true, false, true, false, true, false, true, false, false, false, false, true, false, true, true, false, true]+[false, true, false, true, true, true, false, false, false, true, false, true, true, false, true, false, false, true, false, false, true, true, true, true, false, false, false, true, false, false, false, true];
      {
        calc {
          [true, false, false, true, true, false, true, true, true, true, false, false, false, true, true, true, false, true, false, true, false, true, false, false, false, false, true, false, true, true, false, true];
          {
            pow_7775();
            of_pow(7808, true, false, true, true, false, true, false, false, false, false, true, false, true, false, true, false, true, true, true, false, false, false, true, true, true, true, false, true, true, false, false, true);
          }
          pow_mod_crc(7808);
        }
        calc {
          [false, true, false, true, true, true, false, false, false, true, false, true, true, false, true, false, false, true, false, false, true, true, true, true, false, false, false, true, false, false, false, true];
          {
            pow_3871();
            of_pow(3904, true, false, false, false, true, false, false, false, true, true, true, true, false, false, true, false, false, true, false, true, true, false, true, false, false, false, true, true, true, false, true, false);
          }
          pow_mod_crc(3904);
        }
      }
      pow_mod_crc(7808) + pow_mod_crc(3904);
    }
  }



  lemma lut_entry_61()
  ensures bits_of_int(lut[61] as int, 64)
      == pow_mod_crc(7936) + pow_mod_crc(3968)
  {
    calc {
      bits_of_int(lut[61] as int, 64);
      bits_of_int(454721889134727482, 64);
      {
        lemma_bits_of_int_64_split(454721889134727482);
      }
      bits_of_int(561533242, 32) + bits_of_int(105873190, 32);
      {
        unroll_bits_of_int_32_0x2178513a();
        unroll_bits_of_int_32_0x064f7f26();
      }
      [false, true, false, true, true, true, false, false, true, false, false, false, true, false, true, false, false, false, false, true, true, true, true, false, true, false, false, false, false, true, false, false]+[false, true, true, false, false, true, false, false, true, true, true, true, true, true, true, false, true, true, true, true, false, false, true, false, false, true, true, false, false, false, false, false];
      {
        calc {
          [false, true, false, true, true, true, false, false, true, false, false, false, true, false, true, false, false, false, false, true, true, true, true, false, true, false, false, false, false, true, false, false];
          {
            pow_7903();
            of_pow(7936, false, false, true, false, false, false, false, true, false, true, true, true, true, false, false, false, false, true, false, true, false, false, false, true, false, false, true, true, true, false, true, false);
          }
          pow_mod_crc(7936);
        }
        calc {
          [false, true, true, false, false, true, false, false, true, true, true, true, true, true, true, false, true, true, true, true, false, false, true, false, false, true, true, false, false, false, false, false];
          {
            pow_3935();
            of_pow(3968, false, false, false, false, false, true, true, false, false, true, false, false, true, true, true, true, false, true, true, true, true, true, true, true, false, false, true, false, false, true, true, false);
          }
          pow_mod_crc(3968);
        }
      }
      pow_mod_crc(7936) + pow_mod_crc(3968);
    }
  }



  lemma lut_entry_62()
  ensures bits_of_int(lut[62] as int, 64)
      == pow_mod_crc(8064) + pow_mod_crc(4032)
  {
    calc {
      bits_of_int(lut[62] as int, 64);
      bits_of_int(5635956626175038366, 64);
      {
        lemma_bits_of_int_64_split(5635956626175038366);
      }
      bits_of_int(3769373598, 32) + bits_of_int(1312223408, 32);
      {
        unroll_bits_of_int_32_0xe0ac139e();
        unroll_bits_of_int_32_0x4e36f0b0();
      }
      [false, true, true, true, true, false, false, true, true, true, false, false, true, false, false, false, false, false, true, true, false, true, false, true, false, false, false, false, false, true, true, true]+[false, false, false, false, true, true, false, true, false, false, false, false, true, true, true, true, false, true, true, false, true, true, false, false, false, true, true, true, false, false, true, false];
      {
        calc {
          [false, true, true, true, true, false, false, true, true, true, false, false, true, false, false, false, false, false, true, true, false, true, false, true, false, false, false, false, false, true, true, true];
          {
            pow_8031();
            of_pow(8064, true, true, true, false, false, false, false, false, true, false, true, false, true, true, false, false, false, false, false, true, false, false, true, true, true, false, false, true, true, true, true, false);
          }
          pow_mod_crc(8064);
        }
        calc {
          [false, false, false, false, true, true, false, true, false, false, false, false, true, true, true, true, false, true, true, false, true, true, false, false, false, true, true, true, false, false, true, false];
          {
            pow_3999();
            of_pow(4032, false, true, false, false, true, true, true, false, false, false, true, true, false, true, true, false, true, true, true, true, false, false, false, false, true, false, true, true, false, false, false, false);
          }
          pow_mod_crc(4032);
        }
      }
      pow_mod_crc(8064) + pow_mod_crc(4032);
    }
  }



  lemma lut_entry_63()
  ensures bits_of_int(lut[63] as int, 64)
      == pow_mod_crc(8192) + pow_mod_crc(4096)
  {
    calc {
      bits_of_int(lut[63] as int, 64);
      bits_of_int(15960259052559169274, 64);
      {
        lemma_bits_of_int_64_split(15960259052559169274);
      }
      bits_of_int(385906426, 32) + bits_of_int(3716037388, 32);
      {
        unroll_bits_of_int_32_0x170076fa();
        unroll_bits_of_int_32_0xdd7e3b0c();
      }
      [false, true, false, true, true, true, true, true, false, true, true, false, true, true, true, false, false, false, false, false, false, false, false, false, true, true, true, false, true, false, false, false]+[false, false, true, true, false, false, false, false, true, true, false, true, true, true, false, false, false, true, true, true, true, true, true, false, true, false, true, true, true, false, true, true];
      {
        calc {
          [false, true, false, true, true, true, true, true, false, true, true, false, true, true, true, false, false, false, false, false, false, false, false, false, true, true, true, false, true, false, false, false];
          {
            pow_8159();
            of_pow(8192, false, false, false, true, false, true, true, true, false, false, false, false, false, false, false, false, false, true, true, true, false, true, true, false, true, true, true, true, true, false, true, false);
          }
          pow_mod_crc(8192);
        }
        calc {
          [false, false, true, true, false, false, false, false, true, true, false, true, true, true, false, false, false, true, true, true, true, true, true, false, true, false, true, true, true, false, true, true];
          {
            pow_4063();
            of_pow(4096, true, true, false, true, true, true, false, true, false, true, true, true, true, true, true, false, false, false, true, true, true, false, true, true, false, false, false, false, true, true, false, false);
          }
          pow_mod_crc(4096);
        }
      }
      pow_mod_crc(8192) + pow_mod_crc(4096);
    }
  }



  lemma lut_entry_64()
  ensures bits_of_int(lut[64] as int, 64)
      == pow_mod_crc(8320) + pow_mod_crc(4160)
  {
    calc {
      bits_of_int(lut[64] as int, 64);
      bits_of_int(13650271898881086483, 64);
      {
        lemma_bits_of_int_64_split(13650271898881086483);
      }
      bits_of_int(1145951251, 32) + bits_of_int(3178201592, 32);
      {
        unroll_bits_of_int_32_0x444dd413();
        unroll_bits_of_int_32_0xbd6f81f8();
      }
      [true, true, false, false, true, false, false, false, false, false, true, false, true, false, true, true, true, false, true, true, false, false, true, false, false, false, true, false, false, false, true, false]+[false, false, false, true, true, true, true, true, true, false, false, false, false, false, false, true, true, true, true, true, false, true, true, false, true, false, true, true, true, true, false, true];
      {
        calc {
          [true, true, false, false, true, false, false, false, false, false, true, false, true, false, true, true, true, false, true, true, false, false, true, false, false, false, true, false, false, false, true, false];
          {
            pow_8287();
            of_pow(8320, false, true, false, false, false, true, false, false, false, true, false, false, true, true, false, true, true, true, false, true, false, true, false, false, false, false, false, true, false, false, true, true);
          }
          pow_mod_crc(8320);
        }
        calc {
          [false, false, false, true, true, true, true, true, true, false, false, false, false, false, false, true, true, true, true, true, false, true, true, false, true, false, true, true, true, true, false, true];
          {
            pow_4127();
            of_pow(4160, true, false, true, true, true, true, false, true, false, true, true, false, true, true, true, true, true, false, false, false, false, false, false, true, true, true, true, true, true, false, false, false);
          }
          pow_mod_crc(4160);
        }
      }
      pow_mod_crc(8320) + pow_mod_crc(4160);
    }
  }



  lemma lut_entry_65()
  ensures bits_of_int(lut[65] as int, 64)
      == pow_mod_crc(8448) + pow_mod_crc(4224)
  {
    calc {
      bits_of_int(lut[65] as int, 64);
      bits_of_int(17475485101880270405, 64);
      {
        lemma_bits_of_int_64_split(17475485101880270405);
      }
      bits_of_int(1865702981, 32) + bits_of_int(4068828444, 32);
      {
        unroll_bits_of_int_32_0x6f345e45();
        unroll_bits_of_int_32_0xf285651c();
      }
      [true, false, true, false, false, false, true, false, false, true, true, true, true, false, true, false, false, false, true, false, true, true, false, false, true, true, true, true, false, true, true, false]+[false, false, true, true, true, false, false, false, true, false, true, false, false, true, true, false, true, false, true, false, false, false, false, true, false, true, false, false, true, true, true, true];
      {
        calc {
          [true, false, true, false, false, false, true, false, false, true, true, true, true, false, true, false, false, false, true, false, true, true, false, false, true, true, true, true, false, true, true, false];
          {
            pow_8415();
            of_pow(8448, false, true, true, false, true, true, true, true, false, false, true, true, false, true, false, false, false, true, false, true, true, true, true, false, false, true, false, false, false, true, false, true);
          }
          pow_mod_crc(8448);
        }
        calc {
          [false, false, true, true, true, false, false, false, true, false, true, false, false, true, true, false, true, false, true, false, false, false, false, true, false, true, false, false, true, true, true, true];
          {
            pow_4191();
            of_pow(4224, true, true, true, true, false, false, true, false, true, false, false, false, false, true, false, true, false, true, true, false, false, true, false, true, false, false, false, true, true, true, false, false);
          }
          pow_mod_crc(4224);
        }
      }
      pow_mod_crc(8448) + pow_mod_crc(4224);
    }
  }



  lemma lut_entry_66()
  ensures bits_of_int(lut[66] as int, 64)
      == pow_mod_crc(8576) + pow_mod_crc(4288)
  {
    calc {
      bits_of_int(lut[66] as int, 64);
      bits_of_int(10505135736742837092, 64);
      {
        lemma_bits_of_int_64_split(10505135736742837092);
      }
      bits_of_int(1104247652, 32) + bits_of_int(2445917515, 32);
      {
        unroll_bits_of_int_32_0x41d17b64();
        unroll_bits_of_int_32_0x91c9bd4b();
      }
      [false, false, true, false, false, true, true, false, true, true, false, true, true, true, true, false, true, false, false, false, true, false, true, true, true, false, false, false, false, false, true, false]+[true, true, false, true, false, false, true, false, true, false, true, true, true, true, false, true, true, false, false, true, false, false, true, true, true, false, false, false, true, false, false, true];
      {
        calc {
          [false, false, true, false, false, true, true, false, true, true, false, true, true, true, true, false, true, false, false, false, true, false, true, true, true, false, false, false, false, false, true, false];
          {
            pow_8543();
            of_pow(8576, false, true, false, false, false, false, false, true, true, true, false, true, false, false, false, true, false, true, true, true, true, false, true, true, false, true, true, false, false, true, false, false);
          }
          pow_mod_crc(8576);
        }
        calc {
          [true, true, false, true, false, false, true, false, true, false, true, true, true, true, false, true, true, false, false, true, false, false, true, true, true, false, false, false, true, false, false, true];
          {
            pow_4255();
            of_pow(4288, true, false, false, true, false, false, false, true, true, true, false, false, true, false, false, true, true, false, true, true, true, true, false, true, false, true, false, false, true, false, true, true);
          }
          pow_mod_crc(4288);
        }
      }
      pow_mod_crc(8576) + pow_mod_crc(4288);
    }
  }



  lemma lut_entry_67()
  ensures bits_of_int(lut[67] as int, 64)
      == pow_mod_crc(8704) + pow_mod_crc(4352)
  {
    calc {
      bits_of_int(lut[67] as int, 64);
      bits_of_int(1185694909673093783, 64);
      {
        lemma_bits_of_int_64_split(1185694909673093783);
      }
      bits_of_int(4279089815, 32) + bits_of_int(276066108, 32);
      {
        unroll_bits_of_int_32_0xff0dba97();
        unroll_bits_of_int_32_0x10746f3c();
      }
      [true, true, true, false, true, false, false, true, false, true, false, true, true, true, false, true, true, false, true, true, false, false, false, false, true, true, true, true, true, true, true, true]+[false, false, true, true, true, true, false, false, true, true, true, true, false, true, true, false, false, false, true, false, true, true, true, false, false, false, false, false, true, false, false, false];
      {
        calc {
          [true, true, true, false, true, false, false, true, false, true, false, true, true, true, false, true, true, false, true, true, false, false, false, false, true, true, true, true, true, true, true, true];
          {
            pow_8671();
            of_pow(8704, true, true, true, true, true, true, true, true, false, false, false, false, true, true, false, true, true, false, true, true, true, false, true, false, true, false, false, true, false, true, true, true);
          }
          pow_mod_crc(8704);
        }
        calc {
          [false, false, true, true, true, true, false, false, true, true, true, true, false, true, true, false, false, false, true, false, true, true, true, false, false, false, false, false, true, false, false, false];
          {
            pow_4319();
            of_pow(4352, false, false, false, true, false, false, false, false, false, true, true, true, false, true, false, false, false, true, true, false, true, true, true, true, false, false, true, true, true, true, false, false);
          }
          pow_mod_crc(4352);
        }
      }
      pow_mod_crc(8704) + pow_mod_crc(4352);
    }
  }



  lemma lut_entry_68()
  ensures bits_of_int(lut[68] as int, 64)
      == pow_mod_crc(8832) + pow_mod_crc(4416)
  {
    calc {
      bits_of_int(lut[68] as int, 64);
      bits_of_int(9826582239049629169, 64);
      {
        lemma_bits_of_int_64_split(9826582239049629169);
      }
      bits_of_int(2729917937, 32) + bits_of_int(2287929467, 32);
      {
        unroll_bits_of_int_32_0xa2b73df1();
        unroll_bits_of_int_32_0x885f087b();
      }
      [true, false, false, false, true, true, true, true, true, false, true, true, true, true, false, false, true, true, true, false, true, true, false, true, false, true, false, false, false, true, false, true]+[true, true, false, true, true, true, true, false, false, false, false, true, false, false, false, false, true, true, true, true, true, false, true, false, false, false, false, true, false, false, false, true];
      {
        calc {
          [true, false, false, false, true, true, true, true, true, false, true, true, true, true, false, false, true, true, true, false, true, true, false, true, false, true, false, false, false, true, false, true];
          {
            pow_8799();
            of_pow(8832, true, false, true, false, false, false, true, false, true, false, true, true, false, true, true, true, false, false, true, true, true, true, false, true, true, true, true, true, false, false, false, true);
          }
          pow_mod_crc(8832);
        }
        calc {
          [true, true, false, true, true, true, true, false, false, false, false, true, false, false, false, false, true, true, true, true, true, false, true, false, false, false, false, true, false, false, false, true];
          {
            pow_4383();
            of_pow(4416, true, false, false, false, true, false, false, false, false, true, false, true, true, true, true, true, false, false, false, false, true, false, false, false, false, true, true, true, true, false, true, true);
          }
          pow_mod_crc(4416);
        }
      }
      pow_mod_crc(8832) + pow_mod_crc(4416);
    }
  }



  lemma lut_entry_69()
  ensures bits_of_int(lut[69] as int, 64)
      == pow_mod_crc(8960) + pow_mod_crc(4480)
  {
    calc {
      bits_of_int(lut[69] as int, 64);
      bits_of_int(14386335962503505228, 64);
      {
        lemma_bits_of_int_64_split(14386335962503505228);
      }
      bits_of_int(4168279372, 32) + bits_of_int(3349579861, 32);
      {
        unroll_bits_of_int_32_0xf872e54c();
        unroll_bits_of_int_32_0xc7a68855();
      }
      [false, false, true, true, false, false, true, false, true, false, true, false, false, true, true, true, false, true, false, false, true, true, true, false, false, false, false, true, true, true, true, true]+[true, false, true, false, true, false, true, false, false, false, false, true, false, false, false, true, false, true, true, false, false, true, false, true, true, true, true, false, false, false, true, true];
      {
        calc {
          [false, false, true, true, false, false, true, false, true, false, true, false, false, true, true, true, false, true, false, false, true, true, true, false, false, false, false, true, true, true, true, true];
          {
            pow_8927();
            of_pow(8960, true, true, true, true, true, false, false, false, false, true, true, true, false, false, true, false, true, true, true, false, false, true, false, true, false, true, false, false, true, true, false, false);
          }
          pow_mod_crc(8960);
        }
        calc {
          [true, false, true, false, true, false, true, false, false, false, false, true, false, false, false, true, false, true, true, false, false, true, false, true, true, true, true, false, false, false, true, true];
          {
            pow_4447();
            of_pow(4480, true, true, false, false, false, true, true, true, true, false, true, false, false, true, true, false, true, false, false, false, true, false, false, false, false, true, false, true, false, true, false, true);
          }
          pow_mod_crc(4480);
        }
      }
      pow_mod_crc(8960) + pow_mod_crc(4480);
    }
  }



  lemma lut_entry_70()
  ensures bits_of_int(lut[70] as int, 64)
      == pow_mod_crc(9088) + pow_mod_crc(4544)
  {
    calc {
      bits_of_int(lut[70] as int, 64);
      bits_of_int(5482087126021564924, 64);
      {
        lemma_bits_of_int_64_split(5482087126021564924);
      }
      bits_of_int(507636220, 32) + bits_of_int(1276397874, 32);
      {
        unroll_bits_of_int_32_0x1e41e9fc();
        unroll_bits_of_int_32_0x4c144932();
      }
      [false, false, true, true, true, true, true, true, true, false, false, true, false, true, true, true, true, false, false, false, false, false, true, false, false, true, true, true, true, false, false, false]+[false, true, false, false, true, true, false, false, true, false, false, true, false, false, true, false, false, false, true, false, true, false, false, false, false, false, true, true, false, false, true, false];
      {
        calc {
          [false, false, true, true, true, true, true, true, true, false, false, true, false, true, true, true, true, false, false, false, false, false, true, false, false, true, true, true, true, false, false, false];
          {
            pow_9055();
            of_pow(9088, false, false, false, true, true, true, true, false, false, true, false, false, false, false, false, true, true, true, true, false, true, false, false, true, true, true, true, true, true, true, false, false);
          }
          pow_mod_crc(9088);
        }
        calc {
          [false, true, false, false, true, true, false, false, true, false, false, true, false, false, true, false, false, false, true, false, true, false, false, false, false, false, true, true, false, false, true, false];
          {
            pow_4511();
            of_pow(4544, false, true, false, false, true, true, false, false, false, false, false, true, false, true, false, false, false, true, false, false, true, false, false, true, false, false, true, true, false, false, true, false);
          }
          pow_mod_crc(4544);
        }
      }
      pow_mod_crc(9088) + pow_mod_crc(4544);
    }
  }



  lemma lut_entry_71()
  ensures bits_of_int(lut[71] as int, 64)
      == pow_mod_crc(9216) + pow_mod_crc(4608)
  {
    calc {
      bits_of_int(lut[71] as int, 64);
      bits_of_int(2818576361891357906, 64);
      {
        lemma_bits_of_int_64_split(2818576361891357906);
      }
      bits_of_int(2262361298, 32) + bits_of_int(656250948, 32);
      {
        unroll_bits_of_int_32_0x86d8e4d2();
        unroll_bits_of_int_32_0x271d9844();
      }
      [false, true, false, false, true, false, true, true, false, false, true, false, false, true, true, true, false, false, false, true, true, false, true, true, false, true, true, false, false, false, false, true]+[false, false, true, false, false, false, true, false, false, false, false, true, true, false, false, true, true, false, true, true, true, false, false, false, true, true, true, false, false, true, false, false];
      {
        calc {
          [false, true, false, false, true, false, true, true, false, false, true, false, false, true, true, true, false, false, false, true, true, false, true, true, false, true, true, false, false, false, false, true];
          {
            pow_9183();
            of_pow(9216, true, false, false, false, false, true, true, false, true, true, false, true, true, false, false, false, true, true, true, false, false, true, false, false, true, true, false, true, false, false, true, false);
          }
          pow_mod_crc(9216);
        }
        calc {
          [false, false, true, false, false, false, true, false, false, false, false, true, true, false, false, true, true, false, true, true, true, false, false, false, true, true, true, false, false, true, false, false];
          {
            pow_4575();
            of_pow(4608, false, false, true, false, false, true, true, true, false, false, false, true, true, true, false, true, true, false, false, true, true, false, false, false, false, true, false, false, false, true, false, false);
          }
          pow_mod_crc(4608);
        }
      }
      pow_mod_crc(9216) + pow_mod_crc(4608);
    }
  }



  lemma lut_entry_72()
  ensures bits_of_int(lut[72] as int, 64)
      == pow_mod_crc(9344) + pow_mod_crc(4672)
  {
    calc {
      bits_of_int(lut[72] as int, 64);
      bits_of_int(5914509451093334411, 64);
      {
        lemma_bits_of_int_64_split(5914509451093334411);
      }
      bits_of_int(1696323979, 32) + bits_of_int(1377079042, 32);
      {
        unroll_bits_of_int_32_0x651bd98b();
        unroll_bits_of_int_32_0x52148f02();
      }
      [true, true, false, true, false, false, false, true, true, false, false, true, true, false, true, true, true, true, false, true, true, false, false, false, true, false, true, false, false, true, true, false]+[false, true, false, false, false, false, false, false, true, true, true, true, false, false, false, true, false, false, true, false, true, false, false, false, false, true, false, false, true, false, true, false];
      {
        calc {
          [true, true, false, true, false, false, false, true, true, false, false, true, true, false, true, true, true, true, false, true, true, false, false, false, true, false, true, false, false, true, true, false];
          {
            pow_9311();
            of_pow(9344, false, true, true, false, false, true, false, true, false, false, false, true, true, false, true, true, true, true, false, true, true, false, false, true, true, false, false, false, true, false, true, true);
          }
          pow_mod_crc(9344);
        }
        calc {
          [false, true, false, false, false, false, false, false, true, true, true, true, false, false, false, true, false, false, true, false, true, false, false, false, false, true, false, false, true, false, true, false];
          {
            pow_4639();
            of_pow(4672, false, true, false, true, false, false, true, false, false, false, false, true, false, true, false, false, true, false, false, false, true, true, true, true, false, false, false, false, false, false, true, false);
          }
          pow_mod_crc(4672);
        }
      }
      pow_mod_crc(9344) + pow_mod_crc(4672);
    }
  }



  lemma lut_entry_73()
  ensures bits_of_int(lut[73] as int, 64)
      == pow_mod_crc(9472) + pow_mod_crc(4736)
  {
    calc {
      bits_of_int(lut[73] as int, 64);
      bits_of_int(10265509001948623292, 64);
      {
        lemma_bits_of_int_64_split(10265509001948623292);
      }
      bits_of_int(1538847164, 32) + bits_of_int(2390125068, 32);
      {
        unroll_bits_of_int_32_0x5bb8f1bc();
        unroll_bits_of_int_32_0x8e766a0c();
      }
      [false, false, true, true, true, true, false, true, true, false, false, false, true, true, true, true, false, false, false, true, true, true, false, true, true, true, false, true, true, false, true, false]+[false, false, true, true, false, false, false, false, false, true, false, true, false, true, true, false, false, true, true, false, true, true, true, false, false, true, true, true, false, false, false, true];
      {
        calc {
          [false, false, true, true, true, true, false, true, true, false, false, false, true, true, true, true, false, false, false, true, true, true, false, true, true, true, false, true, true, false, true, false];
          {
            pow_9439();
            of_pow(9472, false, true, false, true, true, false, true, true, true, false, true, true, true, false, false, false, true, true, true, true, false, false, false, true, true, false, true, true, true, true, false, false);
          }
          pow_mod_crc(9472);
        }
        calc {
          [false, false, true, true, false, false, false, false, false, true, false, true, false, true, true, false, false, true, true, false, true, true, true, false, false, true, true, true, false, false, false, true];
          {
            pow_4703();
            of_pow(4736, true, false, false, false, true, true, true, false, false, true, true, true, false, true, true, false, false, true, true, false, true, false, true, false, false, false, false, false, true, true, false, false);
          }
          pow_mod_crc(4736);
        }
      }
      pow_mod_crc(9472) + pow_mod_crc(4736);
    }
  }



  lemma lut_entry_74()
  ensures bits_of_int(lut[74] as int, 64)
      == pow_mod_crc(9600) + pow_mod_crc(4800)
  {
    calc {
      bits_of_int(lut[74] as int, 64);
      bits_of_int(11801387581718909562, 64);
      {
        lemma_bits_of_int_64_split(11801387581718909562);
      }
      bits_of_int(2836386426, 32) + bits_of_int(2747724666, 32);
      {
        unroll_bits_of_int_32_0xa90fd27a();
        unroll_bits_of_int_32_0xa3c6f37a();
      }
      [false, true, false, true, true, true, true, false, false, true, false, false, true, false, true, true, true, true, true, true, false, false, false, false, true, false, false, true, false, true, false, true]+[false, true, false, true, true, true, true, false, true, true, false, false, true, true, true, true, false, true, true, false, false, false, true, true, true, true, false, false, false, true, false, true];
      {
        calc {
          [false, true, false, true, true, true, true, false, false, true, false, false, true, false, true, true, true, true, true, true, false, false, false, false, true, false, false, true, false, true, false, true];
          {
            pow_9567();
            of_pow(9600, true, false, true, false, true, false, false, true, false, false, false, false, true, true, true, true, true, true, false, true, false, false, true, false, false, true, true, true, true, false, true, false);
          }
          pow_mod_crc(9600);
        }
        calc {
          [false, true, false, true, true, true, true, false, true, true, false, false, true, true, true, true, false, true, true, false, false, false, true, true, true, true, false, false, false, true, false, true];
          {
            pow_4767();
            of_pow(4800, true, false, true, false, false, false, true, true, true, true, false, false, false, true, true, false, true, true, true, true, false, false, true, true, false, true, true, true, true, false, true, false);
          }
          pow_mod_crc(4800);
        }
      }
      pow_mod_crc(9600) + pow_mod_crc(4800);
    }
  }



  lemma lut_entry_75()
  ensures bits_of_int(lut[75] as int, 64)
      == pow_mod_crc(9728) + pow_mod_crc(4864)
  {
    calc {
      bits_of_int(lut[75] as int, 64);
      bits_of_int(10639181483277748090, 64);
      {
        lemma_bits_of_int_64_split(10639181483277748090);
      }
      bits_of_int(3014592378, 32) + bits_of_int(2477127472, 32);
      {
        unroll_bits_of_int_32_0xb3af077a();
        unroll_bits_of_int_32_0x93a5f730();
      }
      [false, true, false, true, true, true, true, false, true, true, true, false, false, false, false, false, true, true, true, true, false, true, false, true, true, true, false, false, true, true, false, true]+[false, false, false, false, true, true, false, false, true, true, true, false, true, true, true, true, true, false, true, false, false, true, false, true, true, true, false, false, true, false, false, true];
      {
        calc {
          [false, true, false, true, true, true, true, false, true, true, true, false, false, false, false, false, true, true, true, true, false, true, false, true, true, true, false, false, true, true, false, true];
          {
            pow_9695();
            of_pow(9728, true, false, true, true, false, false, true, true, true, false, true, false, true, true, true, true, false, false, false, false, false, true, true, true, false, true, true, true, true, false, true, false);
          }
          pow_mod_crc(9728);
        }
        calc {
          [false, false, false, false, true, true, false, false, true, true, true, false, true, true, true, true, true, false, true, false, false, true, false, true, true, true, false, false, true, false, false, true];
          {
            pow_4831();
            of_pow(4864, true, false, false, true, false, false, true, true, true, false, true, false, false, true, false, true, true, true, true, true, false, true, true, true, false, false, true, true, false, false, false, false);
          }
          pow_mod_crc(4864);
        }
      }
      pow_mod_crc(9728) + pow_mod_crc(4864);
    }
  }



  lemma lut_entry_76()
  ensures bits_of_int(lut[76] as int, 64)
      == pow_mod_crc(9856) + pow_mod_crc(4928)
  {
    calc {
      bits_of_int(lut[76] as int, 64);
      bits_of_int(15546519918865602434, 64);
      {
        lemma_bits_of_int_64_split(15546519918865602434);
      }
      bits_of_int(1233442690, 32) + bits_of_int(3619706239, 32);
      {
        unroll_bits_of_int_32_0x4984d782();
        unroll_bits_of_int_32_0xd7c0557f();
      }
      [false, true, false, false, false, false, false, true, true, true, true, false, true, false, true, true, false, false, true, false, false, false, false, true, true, false, false, true, false, false, true, false]+[true, true, true, true, true, true, true, false, true, false, true, false, true, false, true, false, false, false, false, false, false, false, true, true, true, true, true, false, true, false, true, true];
      {
        calc {
          [false, true, false, false, false, false, false, true, true, true, true, false, true, false, true, true, false, false, true, false, false, false, false, true, true, false, false, true, false, false, true, false];
          {
            pow_9823();
            of_pow(9856, false, true, false, false, true, false, false, true, true, false, false, false, false, true, false, false, true, true, false, true, false, true, true, true, true, false, false, false, false, false, true, false);
          }
          pow_mod_crc(9856);
        }
        calc {
          [true, true, true, true, true, true, true, false, true, false, true, false, true, false, true, false, false, false, false, false, false, false, true, true, true, true, true, false, true, false, true, true];
          {
            pow_4895();
            of_pow(4928, true, true, false, true, false, true, true, true, true, true, false, false, false, false, false, false, false, true, false, true, false, true, false, true, false, true, true, true, true, true, true, true);
          }
          pow_mod_crc(4928);
        }
      }
      pow_mod_crc(9856) + pow_mod_crc(4928);
    }
  }



  lemma lut_entry_77()
  ensures bits_of_int(lut[77] as int, 64)
      == pow_mod_crc(9984) + pow_mod_crc(4992)
  {
    calc {
      bits_of_int(lut[77] as int, 64);
      bits_of_int(7831916281181696940, 64);
      {
        lemma_bits_of_int_64_split(7831916281181696940);
      }
      bits_of_int(3396268972, 32) + bits_of_int(1823510108, 32);
      {
        unroll_bits_of_int_32_0xca6ef3ac();
        unroll_bits_of_int_32_0x6cb08e5c();
      }
      [false, false, true, true, false, true, false, true, true, true, false, false, true, true, true, true, false, true, true, true, false, true, true, false, false, true, false, true, false, false, true, true]+[false, false, true, true, true, false, true, false, false, true, true, true, false, false, false, true, false, false, false, false, true, true, false, true, false, false, true, true, false, true, true, false];
      {
        calc {
          [false, false, true, true, false, true, false, true, true, true, false, false, true, true, true, true, false, true, true, true, false, true, true, false, false, true, false, true, false, false, true, true];
          {
            pow_9951();
            of_pow(9984, true, true, false, false, true, false, true, false, false, true, true, false, true, true, true, false, true, true, true, true, false, false, true, true, true, false, true, false, true, true, false, false);
          }
          pow_mod_crc(9984);
        }
        calc {
          [false, false, true, true, true, false, true, false, false, true, true, true, false, false, false, true, false, false, false, false, true, true, false, true, false, false, true, true, false, true, true, false];
          {
            pow_4959();
            of_pow(4992, false, true, true, false, true, true, false, false, true, false, true, true, false, false, false, false, true, false, false, false, true, true, true, false, false, true, false, true, true, true, false, false);
          }
          pow_mod_crc(4992);
        }
      }
      pow_mod_crc(9984) + pow_mod_crc(4992);
    }
  }



  lemma lut_entry_78()
  ensures bits_of_int(lut[78] as int, 64)
      == pow_mod_crc(10112) + pow_mod_crc(5056)
  {
    calc {
      bits_of_int(lut[78] as int, 64);
      bits_of_int(7196418408862059302, 64);
      {
        lemma_bits_of_int_64_split(7196418408862059302);
      }
      bits_of_int(592317222, 32) + bits_of_int(1675546730, 32);
      {
        unroll_bits_of_int_32_0x234e0b26();
        unroll_bits_of_int_32_0x63ded06a();
      }
      [false, true, true, false, false, true, false, false, true, true, false, true, false, false, false, false, false, true, true, true, false, false, true, false, true, true, false, false, false, true, false, false]+[false, true, false, true, false, true, true, false, false, false, false, false, true, false, true, true, false, true, true, true, true, false, true, true, true, true, false, false, false, true, true, false];
      {
        calc {
          [false, true, true, false, false, true, false, false, true, true, false, true, false, false, false, false, false, true, true, true, false, false, true, false, true, true, false, false, false, true, false, false];
          {
            pow_10079();
            of_pow(10112, false, false, true, false, false, false, true, true, false, true, false, false, true, true, true, false, false, false, false, false, true, false, true, true, false, false, true, false, false, true, true, false);
          }
          pow_mod_crc(10112);
        }
        calc {
          [false, true, false, true, false, true, true, false, false, false, false, false, true, false, true, true, false, true, true, true, true, false, true, true, true, true, false, false, false, true, true, false];
          {
            pow_5023();
            of_pow(5056, false, true, true, false, false, false, true, true, true, true, false, true, true, true, true, false, true, true, false, true, false, false, false, false, false, true, true, false, true, false, true, false);
          }
          pow_mod_crc(5056);
        }
      }
      pow_mod_crc(10112) + pow_mod_crc(5056);
    }
  }



  lemma lut_entry_79()
  ensures bits_of_int(lut[79] as int, 64)
      == pow_mod_crc(10240) + pow_mod_crc(5120)
  {
    calc {
      bits_of_int(lut[79] as int, 64);
      bits_of_int(7742989249924221883, 64);
      {
        lemma_bits_of_int_64_split(7742989249924221883);
      }
      bits_of_int(3714501563, 32) + bits_of_int(1802805170, 32);
      {
        unroll_bits_of_int_32_0xdd66cbbb();
        unroll_bits_of_int_32_0x6b749fb2();
      }
      [true, true, false, true, true, true, false, true, true, true, false, true, false, false, true, true, false, true, true, false, false, true, true, false, true, false, true, true, true, false, true, true]+[false, true, false, false, true, true, false, true, true, true, true, true, true, false, false, true, false, false, true, false, true, true, true, false, true, true, false, true, false, true, true, false];
      {
        calc {
          [true, true, false, true, true, true, false, true, true, true, false, true, false, false, true, true, false, true, true, false, false, true, true, false, true, false, true, true, true, false, true, true];
          {
            pow_10207();
            of_pow(10240, true, true, false, true, true, true, false, true, false, true, true, false, false, true, true, false, true, true, false, false, true, false, true, true, true, false, true, true, true, false, true, true);
          }
          pow_mod_crc(10240);
        }
        calc {
          [false, true, false, false, true, true, false, true, true, true, true, true, true, false, false, true, false, false, true, false, true, true, true, false, true, true, false, true, false, true, true, false];
          {
            pow_5087();
            of_pow(5120, false, true, true, false, true, false, true, true, false, true, true, true, false, true, false, false, true, false, false, true, true, true, true, true, true, false, true, true, false, false, true, false);
          }
          pow_mod_crc(5120);
        }
      }
      pow_mod_crc(10240) + pow_mod_crc(5120);
    }
  }



  lemma lut_entry_80()
  ensures bits_of_int(lut[80] as int, 64)
      == pow_mod_crc(10368) + pow_mod_crc(5184)
  {
    calc {
      bits_of_int(lut[80] as int, 64);
      bits_of_int(5572807874038941034, 64);
      {
        lemma_bits_of_int_64_split(5572807874038941034);
      }
      bits_of_int(1167541610, 32) + bits_of_int(1297520444, 32);
      {
        unroll_bits_of_int_32_0x4597456a();
        unroll_bits_of_int_32_0x4d56973c();
      }
      [false, true, false, true, false, true, true, false, true, false, true, false, false, false, true, false, true, true, true, false, true, false, false, true, true, false, true, false, false, false, true, false]+[false, false, true, true, true, true, false, false, true, true, true, false, true, false, false, true, false, true, true, false, true, false, true, false, true, false, true, true, false, false, true, false];
      {
        calc {
          [false, true, false, true, false, true, true, false, true, false, true, false, false, false, true, false, true, true, true, false, true, false, false, true, true, false, true, false, false, false, true, false];
          {
            pow_10335();
            of_pow(10368, false, true, false, false, false, true, false, true, true, false, false, true, false, true, true, true, false, true, false, false, false, true, false, true, false, true, true, false, true, false, true, false);
          }
          pow_mod_crc(10368);
        }
        calc {
          [false, false, true, true, true, true, false, false, true, true, true, false, true, false, false, true, false, true, true, false, true, false, true, false, true, false, true, true, false, false, true, false];
          {
            pow_5151();
            of_pow(5184, false, true, false, false, true, true, false, true, false, true, false, true, false, true, true, false, true, false, false, true, false, true, true, true, false, false, true, true, true, true, false, false);
          }
          pow_mod_crc(5184);
        }
      }
      pow_mod_crc(10368) + pow_mod_crc(5184);
    }
  }



  lemma lut_entry_81()
  ensures bits_of_int(lut[81] as int, 64)
      == pow_mod_crc(10496) + pow_mod_crc(5248)
  {
    calc {
      bits_of_int(lut[81] as int, 64);
      bits_of_int(1410719614733815476, 64);
      {
        lemma_bits_of_int_64_split(1410719614733815476);
      }
      bits_of_int(3923938996, 32) + bits_of_int(328458755, 32);
      {
        unroll_bits_of_int_32_0xe9e28eb4();
        unroll_bits_of_int_32_0x1393e203();
      }
      [false, false, true, false, true, true, false, true, false, true, true, true, false, false, false, true, false, true, false, false, false, true, true, true, true, false, false, true, false, true, true, true]+[true, true, false, false, false, false, false, false, false, true, false, false, false, true, true, true, true, true, false, false, true, false, false, true, true, true, false, false, true, false, false, false];
      {
        calc {
          [false, false, true, false, true, true, false, true, false, true, true, true, false, false, false, true, false, true, false, false, false, true, true, true, true, false, false, true, false, true, true, true];
          {
            pow_10463();
            of_pow(10496, true, true, true, false, true, false, false, true, true, true, true, false, false, false, true, false, true, false, false, false, true, true, true, false, true, false, true, true, false, true, false, false);
          }
          pow_mod_crc(10496);
        }
        calc {
          [true, true, false, false, false, false, false, false, false, true, false, false, false, true, true, true, true, true, false, false, true, false, false, true, true, true, false, false, true, false, false, false];
          {
            pow_5215();
            of_pow(5248, false, false, false, true, false, false, true, true, true, false, false, true, false, false, true, true, true, true, true, false, false, false, true, false, false, false, false, false, false, false, true, true);
          }
          pow_mod_crc(5248);
        }
      }
      pow_mod_crc(10496) + pow_mod_crc(5248);
    }
  }



  lemma lut_entry_82()
  ensures bits_of_int(lut[82] as int, 64)
      == pow_mod_crc(10624) + pow_mod_crc(5312)
  {
    calc {
      bits_of_int(lut[82] as int, 64);
      bits_of_int(10838415939926488442, 64);
      {
        lemma_bits_of_int_64_split(10838415939926488442);
      }
      bits_of_int(2067789178, 32) + bits_of_int(2523515359, 32);
      {
        unroll_bits_of_int_32_0x7b3ff57a();
        unroll_bits_of_int_32_0x9669c9df();
      }
      [false, true, false, true, true, true, true, false, true, false, true, false, true, true, true, true, true, true, true, true, true, true, false, false, true, true, false, true, true, true, true, false]+[true, true, true, true, true, false, true, true, true, false, false, true, false, false, true, true, true, false, false, true, false, true, true, false, false, true, true, false, true, false, false, true];
      {
        calc {
          [false, true, false, true, true, true, true, false, true, false, true, false, true, true, true, true, true, true, true, true, true, true, false, false, true, true, false, true, true, true, true, false];
          {
            pow_10591();
            of_pow(10624, false, true, true, true, true, false, true, true, false, false, true, true, true, true, true, true, true, true, true, true, false, true, false, true, false, true, true, true, true, false, true, false);
          }
          pow_mod_crc(10624);
        }
        calc {
          [true, true, true, true, true, false, true, true, true, false, false, true, false, false, true, true, true, false, false, true, false, true, true, false, false, true, true, false, true, false, false, true];
          {
            pow_5279();
            of_pow(5312, true, false, false, true, false, true, true, false, false, true, true, false, true, false, false, true, true, true, false, false, true, false, false, true, true, true, false, true, true, true, true, true);
          }
          pow_mod_crc(5312);
        }
      }
      pow_mod_crc(10624) + pow_mod_crc(5312);
    }
  }



  lemma lut_entry_83()
  ensures bits_of_int(lut[83] as int, 64)
      == pow_mod_crc(10752) + pow_mod_crc(5376)
  {
    calc {
      bits_of_int(lut[83] as int, 64);
      bits_of_int(14898864343411636098, 64);
      {
        lemma_bits_of_int_64_split(14898864343411636098);
      }
      bits_of_int(3385374594, 32) + bits_of_int(3468912174, 32);
      {
        unroll_bits_of_int_32_0xc9c8b782();
        unroll_bits_of_int_32_0xcec3662e();
      }
      [false, true, false, false, false, false, false, true, true, true, true, false, true, true, false, true, false, false, false, true, false, false, true, true, true, false, false, true, false, false, true, true]+[false, true, true, true, false, true, false, false, false, true, true, false, false, true, true, false, true, true, false, false, false, false, true, true, false, true, true, true, false, false, true, true];
      {
        calc {
          [false, true, false, false, false, false, false, true, true, true, true, false, true, true, false, true, false, false, false, true, false, false, true, true, true, false, false, true, false, false, true, true];
          {
            pow_10719();
            of_pow(10752, true, true, false, false, true, false, false, true, true, true, false, false, true, false, false, false, true, false, true, true, false, true, true, true, true, false, false, false, false, false, true, false);
          }
          pow_mod_crc(10752);
        }
        calc {
          [false, true, true, true, false, true, false, false, false, true, true, false, false, true, true, false, true, true, false, false, false, false, true, true, false, true, true, true, false, false, true, true];
          {
            pow_5343();
            of_pow(5376, true, true, false, false, true, true, true, false, true, true, false, false, false, false, true, true, false, true, true, false, false, true, true, false, false, false, true, false, true, true, true, false);
          }
          pow_mod_crc(5376);
        }
      }
      pow_mod_crc(10752) + pow_mod_crc(5376);
    }
  }



  lemma lut_entry_84()
  ensures bits_of_int(lut[84] as int, 64)
      == pow_mod_crc(10880) + pow_mod_crc(5440)
  {
    calc {
      bits_of_int(lut[84] as int, 64);
      bits_of_int(16435873140207307887, 64);
      {
        lemma_bits_of_int_64_split(16435873140207307887);
      }
      bits_of_int(1064356975, 32) + bits_of_int(3826774922, 32);
      {
        unroll_bits_of_int_32_0x3f70cc6f();
        unroll_bits_of_int_32_0xe417f38a();
      }
      [true, true, true, true, false, true, true, false, false, false, true, true, false, false, true, true, false, false, false, false, true, true, true, false, true, true, true, true, true, true, false, false]+[false, true, false, true, false, false, false, true, true, true, false, false, true, true, true, true, true, true, true, false, true, false, false, false, false, false, true, false, false, true, true, true];
      {
        calc {
          [true, true, true, true, false, true, true, false, false, false, true, true, false, false, true, true, false, false, false, false, true, true, true, false, true, true, true, true, true, true, false, false];
          {
            pow_10847();
            of_pow(10880, false, false, true, true, true, true, true, true, false, true, true, true, false, false, false, false, true, true, false, false, true, true, false, false, false, true, true, false, true, true, true, true);
          }
          pow_mod_crc(10880);
        }
        calc {
          [false, true, false, true, false, false, false, true, true, true, false, false, true, true, true, true, true, true, true, false, true, false, false, false, false, false, true, false, false, true, true, true];
          {
            pow_5407();
            of_pow(5440, true, true, true, false, false, true, false, false, false, false, false, true, false, true, true, true, true, true, true, true, false, false, true, true, true, false, false, false, true, false, true, false);
          }
          pow_mod_crc(5440);
        }
      }
      pow_mod_crc(10880) + pow_mod_crc(5440);
    }
  }



  lemma lut_entry_85()
  ensures bits_of_int(lut[85] as int, 64)
      == pow_mod_crc(11008) + pow_mod_crc(5504)
  {
    calc {
      bits_of_int(lut[85] as int, 64);
      bits_of_int(10864113571485255332, 64);
      {
        lemma_bits_of_int_64_split(10864113571485255332);
      }
      bits_of_int(2480998052, 32) + bits_of_int(2529498555, 32);
      {
        unroll_bits_of_int_32_0x93e106a4();
        unroll_bits_of_int_32_0x96c515bb();
      }
      [false, false, true, false, false, true, false, true, false, true, true, false, false, false, false, false, true, false, false, false, false, true, true, true, true, true, false, false, true, false, false, true]+[true, true, false, true, true, true, false, true, true, false, true, false, true, false, false, false, true, false, true, false, false, false, true, true, false, true, true, false, true, false, false, true];
      {
        calc {
          [false, false, true, false, false, true, false, true, false, true, true, false, false, false, false, false, true, false, false, false, false, true, true, true, true, true, false, false, true, false, false, true];
          {
            pow_10975();
            of_pow(11008, true, false, false, true, false, false, true, true, true, true, true, false, false, false, false, true, false, false, false, false, false, true, true, false, true, false, true, false, false, true, false, false);
          }
          pow_mod_crc(11008);
        }
        calc {
          [true, true, false, true, true, true, false, true, true, false, true, false, true, false, false, false, true, false, true, false, false, false, true, true, false, true, true, false, true, false, false, true];
          {
            pow_5471();
            of_pow(5504, true, false, false, true, false, true, true, false, true, true, false, false, false, true, false, true, false, false, false, true, false, true, false, true, true, false, true, true, true, false, true, true);
          }
          pow_mod_crc(5504);
        }
      }
      pow_mod_crc(11008) + pow_mod_crc(5504);
    }
  }



  lemma lut_entry_86()
  ensures bits_of_int(lut[86] as int, 64)
      == pow_mod_crc(11136) + pow_mod_crc(5568)
  {
    calc {
      bits_of_int(lut[86] as int, 64);
      bits_of_int(5448809578830261357, 64);
      {
        lemma_bits_of_int_64_split(5448809578830261357);
      }
      bits_of_int(1659661421, 32) + bits_of_int(1268649841, 32);
      {
        unroll_bits_of_int_32_0x62ec6c6d();
        unroll_bits_of_int_32_0x4b9e0f71();
      }
      [true, false, true, true, false, true, true, false, false, false, true, true, false, true, true, false, false, false, true, true, false, true, true, true, false, true, false, false, false, true, true, false]+[true, false, false, false, true, true, true, false, true, true, true, true, false, false, false, false, false, true, true, true, true, false, false, true, true, true, false, true, false, false, true, false];
      {
        calc {
          [true, false, true, true, false, true, true, false, false, false, true, true, false, true, true, false, false, false, true, true, false, true, true, true, false, true, false, false, false, true, true, false];
          {
            pow_11103();
            of_pow(11136, false, true, true, false, false, false, true, false, true, true, true, false, true, true, false, false, false, true, true, false, true, true, false, false, false, true, true, false, true, true, false, true);
          }
          pow_mod_crc(11136);
        }
        calc {
          [true, false, false, false, true, true, true, false, true, true, true, true, false, false, false, false, false, true, true, true, true, false, false, true, true, true, false, true, false, false, true, false];
          {
            pow_5535();
            of_pow(5568, false, true, false, false, true, false, true, true, true, false, false, true, true, true, true, false, false, false, false, false, true, true, true, true, false, true, true, true, false, false, false, true);
          }
          pow_mod_crc(5568);
        }
      }
      pow_mod_crc(11136) + pow_mod_crc(5568);
    }
  }



  lemma lut_entry_87()
  ensures bits_of_int(lut[87] as int, 64)
      == pow_mod_crc(11264) + pow_mod_crc(5632)
  {
    calc {
      bits_of_int(lut[87] as int, 64);
      bits_of_int(16644264543653180197, 64);
      {
        lemma_bits_of_int_64_split(16644264543653180197);
      }
      bits_of_int(3625169701, 32) + bits_of_int(3875294826, 32);
      {
        unroll_bits_of_int_32_0xd813b325();
        unroll_bits_of_int_32_0xe6fc4e6a();
      }
      [true, false, true, false, false, true, false, false, true, true, false, false, true, true, false, true, true, true, false, false, true, false, false, false, false, false, false, true, true, false, true, true]+[false, true, false, true, false, true, true, false, false, true, true, true, false, false, true, false, false, false, true, true, true, true, true, true, false, true, true, false, false, true, true, true];
      {
        calc {
          [true, false, true, false, false, true, false, false, true, true, false, false, true, true, false, true, true, true, false, false, true, false, false, false, false, false, false, true, true, false, true, true];
          {
            pow_11231();
            of_pow(11264, true, true, false, true, true, false, false, false, false, false, false, true, false, false, true, true, true, false, true, true, false, false, true, true, false, false, true, false, false, true, false, true);
          }
          pow_mod_crc(11264);
        }
        calc {
          [false, true, false, true, false, true, true, false, false, true, true, true, false, false, true, false, false, false, true, true, true, true, true, true, false, true, true, false, false, true, true, true];
          {
            pow_5599();
            of_pow(5632, true, true, true, false, false, true, true, false, true, true, true, true, true, true, false, false, false, true, false, false, true, true, true, false, false, true, true, false, true, false, true, false);
          }
          pow_mod_crc(5632);
        }
      }
      pow_mod_crc(11264) + pow_mod_crc(5632);
    }
  }



  lemma lut_entry_88()
  ensures bits_of_int(lut[88] as int, 64)
      == pow_mod_crc(11392) + pow_mod_crc(5696)
  {
    calc {
      bits_of_int(lut[88] as int, 64);
      bits_of_int(15061366446538901120, 64);
      {
        lemma_bits_of_int_64_split(15061366446538901120);
      }
      bits_of_int(233850496, 32) + bits_of_int(3506747644, 32);
      {
        unroll_bits_of_int_32_0x0df04680();
        unroll_bits_of_int_32_0xd104b8fc();
      }
      [false, false, false, false, false, false, false, true, false, true, true, false, false, false, true, false, false, false, false, false, true, true, true, true, true, false, true, true, false, false, false, false]+[false, false, true, true, true, true, true, true, false, false, false, true, true, true, false, true, false, false, true, false, false, false, false, false, true, false, false, false, true, false, true, true];
      {
        calc {
          [false, false, false, false, false, false, false, true, false, true, true, false, false, false, true, false, false, false, false, false, true, true, true, true, true, false, true, true, false, false, false, false];
          {
            pow_11359();
            of_pow(11392, false, false, false, false, true, true, false, true, true, true, true, true, false, false, false, false, false, true, false, false, false, true, true, false, true, false, false, false, false, false, false, false);
          }
          pow_mod_crc(11392);
        }
        calc {
          [false, false, true, true, true, true, true, true, false, false, false, true, true, true, false, true, false, false, true, false, false, false, false, false, true, false, false, false, true, false, true, true];
          {
            pow_5663();
            of_pow(5696, true, true, false, true, false, false, false, true, false, false, false, false, false, true, false, false, true, false, true, true, true, false, false, false, true, true, true, true, true, true, false, false);
          }
          pow_mod_crc(5696);
        }
      }
      pow_mod_crc(11392) + pow_mod_crc(5696);
    }
  }



  lemma lut_entry_89()
  ensures bits_of_int(lut[89] as int, 64)
      == pow_mod_crc(11520) + pow_mod_crc(5760)
  {
    calc {
      bits_of_int(lut[89] as int, 64);
      bits_of_int(9378670950993756190, 64);
      {
        lemma_bits_of_int_64_split(9378670950993756190);
      }
      bits_of_int(591527966, 32) + bits_of_int(2183641994, 32);
      {
        unroll_bits_of_int_32_0x2342001e();
        unroll_bits_of_int_32_0x8227bb8a();
      }
      [false, true, true, true, true, false, false, false, false, false, false, false, false, false, false, false, false, true, false, false, false, false, true, false, true, true, false, false, false, true, false, false]+[false, true, false, true, false, false, false, true, true, true, false, true, true, true, false, true, true, true, true, false, false, true, false, false, false, true, false, false, false, false, false, true];
      {
        calc {
          [false, true, true, true, true, false, false, false, false, false, false, false, false, false, false, false, false, true, false, false, false, false, true, false, true, true, false, false, false, true, false, false];
          {
            pow_11487();
            of_pow(11520, false, false, true, false, false, false, true, true, false, true, false, false, false, false, true, false, false, false, false, false, false, false, false, false, false, false, false, true, true, true, true, false);
          }
          pow_mod_crc(11520);
        }
        calc {
          [false, true, false, true, false, false, false, true, true, true, false, true, true, true, false, true, true, true, true, false, false, true, false, false, false, true, false, false, false, false, false, true];
          {
            pow_5727();
            of_pow(5760, true, false, false, false, false, false, true, false, false, false, true, false, false, true, true, true, true, false, true, true, true, false, true, true, true, false, false, false, true, false, true, false);
          }
          pow_mod_crc(5760);
        }
      }
      pow_mod_crc(11520) + pow_mod_crc(5760);
    }
  }



  lemma lut_entry_90()
  ensures bits_of_int(lut[90] as int, 64)
      == pow_mod_crc(11648) + pow_mod_crc(5824)
  {
    calc {
      bits_of_int(lut[90] as int, 64);
      bits_of_int(6573416179336646014, 64);
      {
        lemma_bits_of_int_64_split(6573416179336646014);
      }
      bits_of_int(170560894, 32) + bits_of_int(1530492720, 32);
      {
        unroll_bits_of_int_32_0x0a2a8d7e();
        unroll_bits_of_int_32_0x5b397730();
      }
      [false, true, true, true, true, true, true, false, true, false, true, true, false, false, false, true, false, true, false, true, false, true, false, false, false, true, false, true, false, false, false, false]+[false, false, false, false, true, true, false, false, true, true, true, false, true, true, true, false, true, false, false, true, true, true, false, false, true, true, false, true, true, false, true, false];
      {
        calc {
          [false, true, true, true, true, true, true, false, true, false, true, true, false, false, false, true, false, true, false, true, false, true, false, false, false, true, false, true, false, false, false, false];
          {
            pow_11615();
            of_pow(11648, false, false, false, false, true, false, true, false, false, false, true, false, true, false, true, false, true, false, false, false, true, true, false, true, false, true, true, true, true, true, true, false);
          }
          pow_mod_crc(11648);
        }
        calc {
          [false, false, false, false, true, true, false, false, true, true, true, false, true, true, true, false, true, false, false, true, true, true, false, false, true, true, false, true, true, false, true, false];
          {
            pow_5791();
            of_pow(5824, false, true, false, true, true, false, true, true, false, false, true, true, true, false, false, true, false, true, true, true, false, true, true, true, false, false, true, true, false, false, false, false);
          }
          pow_mod_crc(5824);
        }
      }
      pow_mod_crc(11648) + pow_mod_crc(5824);
    }
  }



  lemma lut_entry_91()
  ensures bits_of_int(lut[91] as int, 64)
      == pow_mod_crc(11776) + pow_mod_crc(5888)
  {
    calc {
      bits_of_int(lut[91] as int, 64);
      bits_of_int(12739917434741999959, 64);
      {
        lemma_bits_of_int_64_split(12739917434741999959);
      }
      bits_of_int(1838827863, 32) + bits_of_int(2966243176, 32);
      {
        unroll_bits_of_int_32_0x6d9a4957();
        unroll_bits_of_int_32_0xb0cd4768();
      }
      [true, true, true, false, true, false, true, false, true, false, false, true, false, false, true, false, false, true, false, true, true, false, false, true, true, false, true, true, false, true, true, false]+[false, false, false, true, false, true, true, false, true, true, true, false, false, false, true, false, true, false, true, true, false, false, true, true, false, false, false, false, true, true, false, true];
      {
        calc {
          [true, true, true, false, true, false, true, false, true, false, false, true, false, false, true, false, false, true, false, true, true, false, false, true, true, false, true, true, false, true, true, false];
          {
            pow_11743();
            of_pow(11776, false, true, true, false, true, true, false, true, true, false, false, true, true, false, true, false, false, true, false, false, true, false, false, true, false, true, false, true, false, true, true, true);
          }
          pow_mod_crc(11776);
        }
        calc {
          [false, false, false, true, false, true, true, false, true, true, true, false, false, false, true, false, true, false, true, true, false, false, true, true, false, false, false, false, true, true, false, true];
          {
            pow_5855();
            of_pow(5888, true, false, true, true, false, false, false, false, true, true, false, false, true, true, false, true, false, true, false, false, false, true, true, true, false, true, true, false, true, false, false, false);
          }
          pow_mod_crc(5888);
        }
      }
      pow_mod_crc(11776) + pow_mod_crc(5888);
    }
  }



  lemma lut_entry_92()
  ensures bits_of_int(lut[92] as int, 64)
      == pow_mod_crc(11904) + pow_mod_crc(5952)
  {
    calc {
      bits_of_int(lut[92] as int, 64);
      bits_of_int(16685471679940802187, 64);
      {
        lemma_bits_of_int_64_split(16685471679940802187);
      }
      bits_of_int(3904255627, 32) + bits_of_int(3884889110, 32);
      {
        unroll_bits_of_int_32_0xe8b6368b();
        unroll_bits_of_int_32_0xe78eb416();
      }
      [true, true, false, true, false, false, false, true, false, true, true, false, true, true, false, false, false, true, true, false, true, true, false, true, false, false, false, true, false, true, true, true]+[false, true, true, false, true, false, false, false, false, false, true, false, true, true, false, true, false, true, true, true, false, false, false, true, true, true, true, false, false, true, true, true];
      {
        calc {
          [true, true, false, true, false, false, false, true, false, true, true, false, true, true, false, false, false, true, true, false, true, true, false, true, false, false, false, true, false, true, true, true];
          {
            pow_11871();
            of_pow(11904, true, true, true, false, true, false, false, false, true, false, true, true, false, true, true, false, false, false, true, true, false, true, true, false, true, false, false, false, true, false, true, true);
          }
          pow_mod_crc(11904);
        }
        calc {
          [false, true, true, false, true, false, false, false, false, false, true, false, true, true, false, true, false, true, true, true, false, false, false, true, true, true, true, false, false, true, true, true];
          {
            pow_5919();
            of_pow(5952, true, true, true, false, false, true, true, true, true, false, false, false, true, true, true, false, true, false, true, true, false, true, false, false, false, false, false, true, false, true, true, false);
          }
          pow_mod_crc(5952);
        }
      }
      pow_mod_crc(11904) + pow_mod_crc(5952);
    }
  }



  lemma lut_entry_93()
  ensures bits_of_int(lut[93] as int, 64)
      == pow_mod_crc(12032) + pow_mod_crc(6016)
  {
    calc {
      bits_of_int(lut[93] as int, 64);
      bits_of_int(4163576987161718042, 64);
      {
        lemma_bits_of_int_64_split(4163576987161718042);
      }
      bits_of_int(3536055578, 32) + bits_of_int(969408309, 32);
      {
        unroll_bits_of_int_32_0xd2c3ed1a();
        unroll_bits_of_int_32_0x39c7ff35();
      }
      [false, true, false, true, true, false, false, false, true, false, true, true, false, true, true, true, true, true, false, false, false, false, true, true, false, true, false, false, true, false, true, true]+[true, false, true, false, true, true, false, false, true, true, true, true, true, true, true, true, true, true, true, false, false, false, true, true, true, false, false, true, true, true, false, false];
      {
        calc {
          [false, true, false, true, true, false, false, false, true, false, true, true, false, true, true, true, true, true, false, false, false, false, true, true, false, true, false, false, true, false, true, true];
          {
            pow_11999();
            of_pow(12032, true, true, false, true, false, false, true, false, true, true, false, false, false, false, true, true, true, true, true, false, true, true, false, true, false, false, false, true, true, false, true, false);
          }
          pow_mod_crc(12032);
        }
        calc {
          [true, false, true, false, true, true, false, false, true, true, true, true, true, true, true, true, true, true, true, false, false, false, true, true, true, false, false, true, true, true, false, false];
          {
            pow_5983();
            of_pow(6016, false, false, true, true, true, false, false, true, true, true, false, false, false, true, true, true, true, true, true, true, true, true, true, true, false, false, true, true, false, true, false, true);
          }
          pow_mod_crc(6016);
        }
      }
      pow_mod_crc(12032) + pow_mod_crc(6016);
    }
  }



  lemma lut_entry_94()
  ensures bits_of_int(lut[94] as int, 64)
      == pow_mod_crc(12160) + pow_mod_crc(6080)
  {
    calc {
      bits_of_int(lut[94] as int, 64);
      bits_of_int(7061378140770817828, 64);
      {
        lemma_bits_of_int_64_split(7061378140770817828);
      }
      bits_of_int(2572834596, 32) + bits_of_int(1644105217, 32);
      {
        unroll_bits_of_int_32_0x995a5724();
        unroll_bits_of_int_32_0x61ff0e01();
      }
      [false, false, true, false, false, true, false, false, true, true, true, false, true, false, true, false, false, true, false, true, true, false, true, false, true, false, false, true, true, false, false, true]+[true, false, false, false, false, false, false, false, false, true, true, true, false, false, false, false, true, true, true, true, true, true, true, true, true, false, false, false, false, true, true, false];
      {
        calc {
          [false, false, true, false, false, true, false, false, true, true, true, false, true, false, true, false, false, true, false, true, true, false, true, false, true, false, false, true, true, false, false, true];
          {
            pow_12127();
            of_pow(12160, true, false, false, true, true, false, false, true, false, true, false, true, true, false, true, false, false, true, false, true, false, true, true, true, false, false, true, false, false, true, false, false);
          }
          pow_mod_crc(12160);
        }
        calc {
          [true, false, false, false, false, false, false, false, false, true, true, true, false, false, false, false, true, true, true, true, true, true, true, true, true, false, false, false, false, true, true, false];
          {
            pow_6047();
            of_pow(6080, false, true, true, false, false, false, false, true, true, true, true, true, true, true, true, true, false, false, false, false, true, true, true, false, false, false, false, false, false, false, false, true);
          }
          pow_mod_crc(6080);
        }
      }
      pow_mod_crc(12160) + pow_mod_crc(6080);
    }
  }



  lemma lut_entry_95()
  ensures bits_of_int(lut[95] as int, 64)
      == pow_mod_crc(12288) + pow_mod_crc(6144)
  {
    calc {
      bits_of_int(lut[95] as int, 64);
      bits_of_int(15538687948650614069, 64);
      {
        lemma_bits_of_int_64_split(15538687948650614069);
      }
      bits_of_int(2666958133, 32) + bits_of_int(3617882716, 32);
      {
        unroll_bits_of_int_32_0x9ef68d35();
        unroll_bits_of_int_32_0xd7a4825c();
      }
      [true, false, true, false, true, true, false, false, true, false, true, true, false, false, false, true, false, true, true, false, true, true, true, true, false, true, true, true, true, false, false, true]+[false, false, true, true, true, false, true, false, false, true, false, false, false, false, false, true, false, false, true, false, false, true, false, true, true, true, true, false, true, false, true, true];
      {
        calc {
          [true, false, true, false, true, true, false, false, true, false, true, true, false, false, false, true, false, true, true, false, true, true, true, true, false, true, true, true, true, false, false, true];
          {
            pow_12255();
            of_pow(12288, true, false, false, true, true, true, true, false, true, true, true, true, false, true, true, false, true, false, false, false, true, true, false, true, false, false, true, true, false, true, false, true);
          }
          pow_mod_crc(12288);
        }
        calc {
          [false, false, true, true, true, false, true, false, false, true, false, false, false, false, false, true, false, false, true, false, false, true, false, true, true, true, true, false, true, false, true, true];
          {
            pow_6111();
            of_pow(6144, true, true, false, true, false, true, true, true, true, false, true, false, false, true, false, false, true, false, false, false, false, false, true, false, false, true, false, true, true, true, false, false);
          }
          pow_mod_crc(6144);
        }
      }
      pow_mod_crc(12288) + pow_mod_crc(6144);
    }
  }



  lemma lut_entry_96()
  ensures bits_of_int(lut[96] as int, 64)
      == pow_mod_crc(12416) + pow_mod_crc(6208)
  {
    calc {
      bits_of_int(lut[96] as int, 64);
      bits_of_int(10202435584804494129, 64);
      {
        lemma_bits_of_int_64_split(10202435584804494129);
      }
      bits_of_int(202611505, 32) + bits_of_int(2375439644, 32);
      {
        unroll_bits_of_int_32_0x0c139b31();
        unroll_bits_of_int_32_0x8d96551c();
      }
      [true, false, false, false, true, true, false, false, true, true, false, true, true, false, false, true, true, true, false, false, true, false, false, false, false, false, true, true, false, false, false, false]+[false, false, true, true, true, false, false, false, true, false, true, false, true, false, true, false, false, true, true, false, true, false, false, true, true, false, true, true, false, false, false, true];
      {
        calc {
          [true, false, false, false, true, true, false, false, true, true, false, true, true, false, false, true, true, true, false, false, true, false, false, false, false, false, true, true, false, false, false, false];
          {
            pow_12383();
            of_pow(12416, false, false, false, false, true, true, false, false, false, false, false, true, false, false, true, true, true, false, false, true, true, false, true, true, false, false, true, true, false, false, false, true);
          }
          pow_mod_crc(12416);
        }
        calc {
          [false, false, true, true, true, false, false, false, true, false, true, false, true, false, true, false, false, true, true, false, true, false, false, true, true, false, true, true, false, false, false, true];
          {
            pow_6175();
            of_pow(6208, true, false, false, false, true, true, false, true, true, false, false, true, false, true, true, false, false, true, false, true, false, true, false, true, false, false, false, true, true, true, false, false);
          }
          pow_mod_crc(6208);
        }
      }
      pow_mod_crc(12416) + pow_mod_crc(6208);
    }
  }



  lemma lut_entry_97()
  ensures bits_of_int(lut[97] as int, 64)
      == pow_mod_crc(12544) + pow_mod_crc(6272)
  {
    calc {
      bits_of_int(lut[97] as int, 64);
      bits_of_int(771105422930550368, 64);
      {
        lemma_bits_of_int_64_split(771105422930550368);
      }
      bits_of_int(4062649952, 32) + bits_of_int(179536971, 32);
      {
        unroll_bits_of_int_32_0xf2271e60();
        unroll_bits_of_int_32_0x0ab3844b();
      }
      [false, false, false, false, false, true, true, false, false, true, true, true, true, false, false, false, true, true, true, false, false, true, false, false, false, true, false, false, true, true, true, true]+[true, true, false, true, false, false, true, false, false, false, true, false, false, false, false, true, true, true, false, false, true, true, false, true, false, true, false, true, false, false, false, false];
      {
        calc {
          [false, false, false, false, false, true, true, false, false, true, true, true, true, false, false, false, true, true, true, false, false, true, false, false, false, true, false, false, true, true, true, true];
          {
            pow_12511();
            of_pow(12544, true, true, true, true, false, false, true, false, false, false, true, false, false, true, true, true, false, false, false, true, true, true, true, false, false, true, true, false, false, false, false, false);
          }
          pow_mod_crc(12544);
        }
        calc {
          [true, true, false, true, false, false, true, false, false, false, true, false, false, false, false, true, true, true, false, false, true, true, false, true, false, true, false, true, false, false, false, false];
          {
            pow_6239();
            of_pow(6272, false, false, false, false, true, false, true, false, true, false, true, true, false, false, true, true, true, false, false, false, false, true, false, false, false, true, false, false, true, false, true, true);
          }
          pow_mod_crc(6272);
        }
      }
      pow_mod_crc(12544) + pow_mod_crc(6272);
    }
  }



  lemma lut_entry_98()
  ensures bits_of_int(lut[98] as int, 64)
      == pow_mod_crc(12672) + pow_mod_crc(6336)
  {
    calc {
      bits_of_int(lut[98] as int, 64);
      bits_of_int(862454524421077194, 64);
      {
        lemma_bits_of_int_64_split(862454524421077194);
      }
      bits_of_int(185333962, 32) + bits_of_int(200805842, 32);
      {
        unroll_bits_of_int_32_0x0b0bf8ca();
        unroll_bits_of_int_32_0x0bf80dd2();
      }
      [false, true, false, true, false, false, true, true, false, false, false, true, true, true, true, true, true, true, false, true, false, false, false, false, true, true, false, true, false, false, false, false]+[false, true, false, false, true, false, true, true, true, false, true, true, false, false, false, false, false, false, false, true, true, true, true, true, true, true, false, true, false, false, false, false];
      {
        calc {
          [false, true, false, true, false, false, true, true, false, false, false, true, true, true, true, true, true, true, false, true, false, false, false, false, true, true, false, true, false, false, false, false];
          {
            pow_12639();
            of_pow(12672, false, false, false, false, true, false, true, true, false, false, false, false, true, false, true, true, true, true, true, true, true, false, false, false, true, true, false, false, true, false, true, false);
          }
          pow_mod_crc(12672);
        }
        calc {
          [false, true, false, false, true, false, true, true, true, false, true, true, false, false, false, false, false, false, false, true, true, true, true, true, true, true, false, true, false, false, false, false];
          {
            pow_6303();
            of_pow(6336, false, false, false, false, true, false, true, true, true, true, true, true, true, false, false, false, false, false, false, false, true, true, false, true, true, true, false, true, false, false, true, false);
          }
          pow_mod_crc(6336);
        }
      }
      pow_mod_crc(12672) + pow_mod_crc(6336);
    }
  }



  lemma lut_entry_99()
  ensures bits_of_int(lut[99] as int, 64)
      == pow_mod_crc(12800) + pow_mod_crc(6400)
  {
    calc {
      bits_of_int(lut[99] as int, 64);
      bits_of_int(101281591546150283, 64);
      {
        lemma_bits_of_int_64_split(101281591546150283);
      }
      bits_of_int(644152715, 32) + bits_of_int(23581458, 32);
      {
        unroll_bits_of_int_32_0x2664fd8b();
        unroll_bits_of_int_32_0x0167d312();
      }
      [true, true, false, true, false, false, false, true, true, false, true, true, true, true, true, true, false, false, true, false, false, true, true, false, false, true, true, false, false, true, false, false]+[false, true, false, false, true, false, false, false, true, true, false, false, true, false, true, true, true, true, true, false, false, true, true, false, true, false, false, false, false, false, false, false];
      {
        calc {
          [true, true, false, true, false, false, false, true, true, false, true, true, true, true, true, true, false, false, true, false, false, true, true, false, false, true, true, false, false, true, false, false];
          {
            pow_12767();
            of_pow(12800, false, false, true, false, false, true, true, false, false, true, true, false, false, true, false, false, true, true, true, true, true, true, false, true, true, false, false, false, true, false, true, true);
          }
          pow_mod_crc(12800);
        }
        calc {
          [false, true, false, false, true, false, false, false, true, true, false, false, true, false, true, true, true, true, true, false, false, true, true, false, true, false, false, false, false, false, false, false];
          {
            pow_6367();
            of_pow(6400, false, false, false, false, false, false, false, true, false, true, true, false, false, true, true, true, true, true, false, true, false, false, true, true, false, false, false, true, false, false, true, false);
          }
          pow_mod_crc(6400);
        }
      }
      pow_mod_crc(12800) + pow_mod_crc(6400);
    }
  }



  lemma lut_entry_100()
  ensures bits_of_int(lut[100] as int, 64)
      == pow_mod_crc(12928) + pow_mod_crc(6464)
  {
    calc {
      bits_of_int(lut[100] as int, 64);
      bits_of_int(9809310501768036653, 64);
      {
        lemma_bits_of_int_64_split(9809310501768036653);
      }
      bits_of_int(3982786861, 32) + bits_of_int(2283908077, 32);
      {
        unroll_bits_of_int_32_0xed64812d();
        unroll_bits_of_int_32_0x8821abed();
      }
      [true, false, true, true, false, true, false, false, true, false, false, false, false, false, false, true, false, false, true, false, false, true, true, false, true, false, true, true, false, true, true, true]+[true, false, true, true, false, true, true, true, true, true, false, true, false, true, false, true, true, false, false, false, false, true, false, false, false, false, false, true, false, false, false, true];
      {
        calc {
          [true, false, true, true, false, true, false, false, true, false, false, false, false, false, false, true, false, false, true, false, false, true, true, false, true, false, true, true, false, true, true, true];
          {
            pow_12895();
            of_pow(12928, true, true, true, false, true, true, false, true, false, true, true, false, false, true, false, false, true, false, false, false, false, false, false, true, false, false, true, false, true, true, false, true);
          }
          pow_mod_crc(12928);
        }
        calc {
          [true, false, true, true, false, true, true, true, true, true, false, true, false, true, false, true, true, false, false, false, false, true, false, false, false, false, false, true, false, false, false, true];
          {
            pow_6431();
            of_pow(6464, true, false, false, false, true, false, false, false, false, false, true, false, false, false, false, true, true, false, true, false, true, false, true, true, true, true, true, false, true, true, false, true);
          }
          pow_mod_crc(6464);
        }
      }
      pow_mod_crc(12928) + pow_mod_crc(6464);
    }
  }



  lemma lut_entry_101()
  ensures bits_of_int(lut[101] as int, 64)
      == pow_mod_crc(13056) + pow_mod_crc(6528)
  {
    calc {
      bits_of_int(lut[101] as int, 64);
      bits_of_int(17728249800948581298, 64);
      {
        lemma_bits_of_int_64_split(17728249800948581298);
      }
      bits_of_int(49152946, 32) + bits_of_int(4127679812, 32);
      {
        unroll_bits_of_int_32_0x02ee03b2();
        unroll_bits_of_int_32_0xf6076544();
      }
      [false, true, false, false, true, true, false, true, true, true, false, false, false, false, false, false, false, true, true, true, false, true, true, true, false, true, false, false, false, false, false, false]+[false, false, true, false, false, false, true, false, true, false, true, false, false, true, true, false, true, true, true, false, false, false, false, false, false, true, true, false, true, true, true, true];
      {
        calc {
          [false, true, false, false, true, true, false, true, true, true, false, false, false, false, false, false, false, true, true, true, false, true, true, true, false, true, false, false, false, false, false, false];
          {
            pow_13023();
            of_pow(13056, false, false, false, false, false, false, true, false, true, true, true, false, true, true, true, false, false, false, false, false, false, false, true, true, true, false, true, true, false, false, true, false);
          }
          pow_mod_crc(13056);
        }
        calc {
          [false, false, true, false, false, false, true, false, true, false, true, false, false, true, true, false, true, true, true, false, false, false, false, false, false, true, true, false, true, true, true, true];
          {
            pow_6495();
            of_pow(6528, true, true, true, true, false, true, true, false, false, false, false, false, false, true, true, true, false, true, true, false, false, true, false, true, false, true, false, false, false, true, false, false);
          }
          pow_mod_crc(6528);
        }
      }
      pow_mod_crc(13056) + pow_mod_crc(6528);
    }
  }



  lemma lut_entry_102()
  ensures bits_of_int(lut[102] as int, 64)
      == pow_mod_crc(13184) + pow_mod_crc(6592)
  {
    calc {
      bits_of_int(lut[102] as int, 64);
      bits_of_int(7657758405607861775, 64);
      {
        lemma_bits_of_int_64_split(7657758405607861775);
      }
      bits_of_int(2248453647, 32) + bits_of_int(1782960818, 32);
      {
        unroll_bits_of_int_32_0x8604ae0f();
        unroll_bits_of_int_32_0x6a45d2b2();
      }
      [true, true, true, true, false, false, false, false, false, true, true, true, false, true, false, true, false, false, true, false, false, false, false, false, false, true, true, false, false, false, false, true]+[false, true, false, false, true, true, false, true, false, true, false, false, true, false, true, true, true, false, true, false, false, false, true, false, false, true, false, true, false, true, true, false];
      {
        calc {
          [true, true, true, true, false, false, false, false, false, true, true, true, false, true, false, true, false, false, true, false, false, false, false, false, false, true, true, false, false, false, false, true];
          {
            pow_13151();
            of_pow(13184, true, false, false, false, false, true, true, false, false, false, false, false, false, true, false, false, true, false, true, false, true, true, true, false, false, false, false, false, true, true, true, true);
          }
          pow_mod_crc(13184);
        }
        calc {
          [false, true, false, false, true, true, false, true, false, true, false, false, true, false, true, true, true, false, true, false, false, false, true, false, false, true, false, true, false, true, true, false];
          {
            pow_6559();
            of_pow(6592, false, true, true, false, true, false, true, false, false, true, false, false, false, true, false, true, true, true, false, true, false, false, true, false, true, false, true, true, false, false, true, false);
          }
          pow_mod_crc(6592);
        }
      }
      pow_mod_crc(13184) + pow_mod_crc(6592);
    }
  }



  lemma lut_entry_103()
  ensures bits_of_int(lut[103] as int, 64)
      == pow_mod_crc(13312) + pow_mod_crc(6656)
  {
    calc {
      bits_of_int(lut[103] as int, 64);
      bits_of_int(2807613980501857971, 64);
      {
        lemma_bits_of_int_64_split(2807613980501857971);
      }
      bits_of_int(909891251, 32) + bits_of_int(653698570, 32);
      {
        unroll_bits_of_int_32_0x363bd6b3();
        unroll_bits_of_int_32_0x26f6a60a();
      }
      [true, true, false, false, true, true, false, true, false, true, true, false, true, false, true, true, true, true, false, true, true, true, false, false, false, true, true, false, true, true, false, false]+[false, true, false, true, false, false, false, false, false, true, true, false, false, true, false, true, false, true, true, false, true, true, true, true, false, true, true, false, false, true, false, false];
      {
        calc {
          [true, true, false, false, true, true, false, true, false, true, true, false, true, false, true, true, true, true, false, true, true, true, false, false, false, true, true, false, true, true, false, false];
          {
            pow_13279();
            of_pow(13312, false, false, true, true, false, true, true, false, false, false, true, true, true, false, true, true, true, true, false, true, false, true, true, false, true, false, true, true, false, false, true, true);
          }
          pow_mod_crc(13312);
        }
        calc {
          [false, true, false, true, false, false, false, false, false, true, true, false, false, true, false, true, false, true, true, false, true, true, true, true, false, true, true, false, false, true, false, false];
          {
            pow_6623();
            of_pow(6656, false, false, true, false, false, true, true, false, true, true, true, true, false, true, true, false, true, false, true, false, false, true, true, false, false, false, false, false, true, false, true, false);
          }
          pow_mod_crc(6656);
        }
      }
      pow_mod_crc(13312) + pow_mod_crc(6656);
    }
  }



  lemma lut_entry_104()
  ensures bits_of_int(lut[104] as int, 64)
      == pow_mod_crc(13440) + pow_mod_crc(6720)
  {
    calc {
      bits_of_int(lut[104] as int, 64);
      bits_of_int(15623662315186717693, 64);
      {
        lemma_bits_of_int_64_split(15623662315186717693);
      }
      bits_of_int(324830205, 32) + bits_of_int(3637667353, 32);
      {
        unroll_bits_of_int_32_0x135c83fd();
        unroll_bits_of_int_32_0xd8d26619();
      }
      [true, false, true, true, true, true, true, true, true, true, false, false, false, false, false, true, false, false, true, true, true, false, true, false, true, true, false, false, true, false, false, false]+[true, false, false, true, true, false, false, false, false, true, true, false, false, true, true, false, false, true, false, false, true, false, true, true, false, false, false, true, true, false, true, true];
      {
        calc {
          [true, false, true, true, true, true, true, true, true, true, false, false, false, false, false, true, false, false, true, true, true, false, true, false, true, true, false, false, true, false, false, false];
          {
            pow_13407();
            of_pow(13440, false, false, false, true, false, false, true, true, false, true, false, true, true, true, false, false, true, false, false, false, false, false, true, true, true, true, true, true, true, true, false, true);
          }
          pow_mod_crc(13440);
        }
        calc {
          [true, false, false, true, true, false, false, false, false, true, true, false, false, true, true, false, false, true, false, false, true, false, true, true, false, false, false, true, true, false, true, true];
          {
            pow_6687();
            of_pow(6720, true, true, false, true, true, false, false, false, true, true, false, true, false, false, true, false, false, true, true, false, false, true, true, false, false, false, false, true, true, false, false, true);
          }
          pow_mod_crc(6720);
        }
      }
      pow_mod_crc(13440) + pow_mod_crc(6720);
    }
  }



  lemma lut_entry_105()
  ensures bits_of_int(lut[105] as int, 64)
      == pow_mod_crc(13568) + pow_mod_crc(6784)
  {
    calc {
      bits_of_int(lut[105] as int, 64);
      bits_of_int(12052127105508173424, 64);
      {
        lemma_bits_of_int_64_split(12052127105508173424);
      }
      bits_of_int(1605101168, 32) + bits_of_int(2806104511, 32);
      {
        unroll_bits_of_int_32_0x5fabe670();
        unroll_bits_of_int_32_0xa741c1bf();
      }
      [false, false, false, false, true, true, true, false, false, true, true, false, false, true, true, true, true, true, false, true, false, true, false, true, true, true, true, true, true, false, true, false]+[true, true, true, true, true, true, false, true, true, false, false, false, false, false, true, true, true, false, false, false, false, false, true, false, true, true, true, false, false, true, false, true];
      {
        calc {
          [false, false, false, false, true, true, true, false, false, true, true, false, false, true, true, true, true, true, false, true, false, true, false, true, true, true, true, true, true, false, true, false];
          {
            pow_13535();
            of_pow(13568, false, true, false, true, true, true, true, true, true, false, true, false, true, false, true, true, true, true, true, false, false, true, true, false, false, true, true, true, false, false, false, false);
          }
          pow_mod_crc(13568);
        }
        calc {
          [true, true, true, true, true, true, false, true, true, false, false, false, false, false, true, true, true, false, false, false, false, false, true, false, true, true, true, false, false, true, false, true];
          {
            pow_6751();
            of_pow(6784, true, false, true, false, false, true, true, true, false, true, false, false, false, false, false, true, true, true, false, false, false, false, false, true, true, false, true, true, true, true, true, true);
          }
          pow_mod_crc(6784);
        }
      }
      pow_mod_crc(13568) + pow_mod_crc(6784);
    }
  }



  lemma lut_entry_106()
  ensures bits_of_int(lut[106] as int, 64)
      == pow_mod_crc(13696) + pow_mod_crc(6848)
  {
    calc {
      bits_of_int(lut[106] as int, 64);
      bits_of_int(16034926200525435513, 64);
      {
        lemma_bits_of_int_64_split(16034926200525435513);
      }
      bits_of_int(904671865, 32) + bits_of_int(3733422188, 32);
      {
        unroll_bits_of_int_32_0x35ec3279();
        unroll_bits_of_int_32_0xde87806c();
      }
      [true, false, false, true, true, true, true, false, false, true, false, false, true, true, false, false, false, false, true, true, false, true, true, true, true, false, true, false, true, true, false, false]+[false, false, true, true, false, true, true, false, false, false, false, false, false, false, false, true, true, true, true, false, false, false, false, true, false, true, true, true, true, false, true, true];
      {
        calc {
          [true, false, false, true, true, true, true, false, false, true, false, false, true, true, false, false, false, false, true, true, false, true, true, true, true, false, true, false, true, true, false, false];
          {
            pow_13663();
            of_pow(13696, false, false, true, true, false, true, false, true, true, true, true, false, true, true, false, false, false, false, true, true, false, false, true, false, false, true, true, true, true, false, false, true);
          }
          pow_mod_crc(13696);
        }
        calc {
          [false, false, true, true, false, true, true, false, false, false, false, false, false, false, false, true, true, true, true, false, false, false, false, true, false, true, true, true, true, false, true, true];
          {
            pow_6815();
            of_pow(6848, true, true, false, true, true, true, true, false, true, false, false, false, false, true, true, true, true, false, false, false, false, false, false, false, false, true, true, false, true, true, false, false);
          }
          pow_mod_crc(6848);
        }
      }
      pow_mod_crc(13696) + pow_mod_crc(6848);
    }
  }



  lemma lut_entry_107()
  ensures bits_of_int(lut[107] as int, 64)
      == pow_mod_crc(13824) + pow_mod_crc(6912)
  {
    calc {
      bits_of_int(lut[107] as int, 64);
      bits_of_int(11013792354648520182, 64);
      {
        lemma_bits_of_int_64_split(11013792354648520182);
      }
      bits_of_int(12383734, 32) + bits_of_int(2564348363, 32);
      {
        unroll_bits_of_int_32_0x00bcf5f6();
        unroll_bits_of_int_32_0x98d8d9cb();
      }
      [false, true, true, false, true, true, true, true, true, false, true, false, true, true, true, true, false, false, true, true, true, true, false, true, false, false, false, false, false, false, false, false]+[true, true, false, true, false, false, true, true, true, false, false, true, true, false, true, true, false, false, false, true, true, false, true, true, false, false, false, true, true, false, false, true];
      {
        calc {
          [false, true, true, false, true, true, true, true, true, false, true, false, true, true, true, true, false, false, true, true, true, true, false, true, false, false, false, false, false, false, false, false];
          {
            pow_13791();
            of_pow(13824, false, false, false, false, false, false, false, false, true, false, true, true, true, true, false, false, true, true, true, true, false, true, false, true, true, true, true, true, false, true, true, false);
          }
          pow_mod_crc(13824);
        }
        calc {
          [true, true, false, true, false, false, true, true, true, false, false, true, true, false, true, true, false, false, false, true, true, false, true, true, false, false, false, true, true, false, false, true];
          {
            pow_6879();
            of_pow(6912, true, false, false, true, true, false, false, false, true, true, false, true, true, false, false, false, true, true, false, true, true, false, false, true, true, true, false, false, true, false, true, true);
          }
          pow_mod_crc(6912);
        }
      }
      pow_mod_crc(13824) + pow_mod_crc(6912);
    }
  }



  lemma lut_entry_108()
  ensures bits_of_int(lut[108] as int, 64)
      == pow_mod_crc(13952) + pow_mod_crc(6976)
  {
    calc {
      bits_of_int(lut[108] as int, 64);
      bits_of_int(1455655901747742345, 64);
      {
        lemma_bits_of_int_64_split(1455655901747742345);
      }
      bits_of_int(2329937545, 32) + bits_of_int(338921300, 32);
      {
        unroll_bits_of_int_32_0x8ae00689();
        unroll_bits_of_int_32_0x14338754();
      }
      [true, false, false, true, false, false, false, true, false, true, true, false, false, false, false, false, false, false, false, false, false, true, true, true, false, true, false, true, false, false, false, true]+[false, false, true, false, true, false, true, false, true, true, true, false, false, false, false, true, true, true, false, false, true, true, false, false, false, false, true, false, true, false, false, false];
      {
        calc {
          [true, false, false, true, false, false, false, true, false, true, true, false, false, false, false, false, false, false, false, false, false, true, true, true, false, true, false, true, false, false, false, true];
          {
            pow_13919();
            of_pow(13952, true, false, false, false, true, false, true, false, true, true, true, false, false, false, false, false, false, false, false, false, false, true, true, false, true, false, false, false, true, false, false, true);
          }
          pow_mod_crc(13952);
        }
        calc {
          [false, false, true, false, true, false, true, false, true, true, true, false, false, false, false, true, true, true, false, false, true, true, false, false, false, false, true, false, true, false, false, false];
          {
            pow_6943();
            of_pow(6976, false, false, false, true, false, true, false, false, false, false, true, true, false, false, true, true, true, false, false, false, false, true, true, true, false, true, false, true, false, true, false, false);
          }
          pow_mod_crc(6976);
        }
      }
      pow_mod_crc(13952) + pow_mod_crc(6976);
    }
  }



  lemma lut_entry_109()
  ensures bits_of_int(lut[109] as int, 64)
      == pow_mod_crc(14080) + pow_mod_crc(7040)
  {
    calc {
      bits_of_int(lut[109] as int, 64);
      bits_of_int(5315316956016047768, 64);
      {
        lemma_bits_of_int_64_split(5315316956016047768);
      }
      bits_of_int(401766040, 32) + bits_of_int(1237568668, 32);
      {
        unroll_bits_of_int_32_0x17f27698();
        unroll_bits_of_int_32_0x49c3cc9c();
      }
      [false, false, false, true, true, false, false, true, false, true, true, false, true, true, true, false, false, true, false, false, true, true, true, true, true, true, true, false, true, false, false, false]+[false, false, true, true, true, false, false, true, false, false, true, true, false, false, true, true, true, true, false, false, false, false, true, true, true, false, false, true, false, false, true, false];
      {
        calc {
          [false, false, false, true, true, false, false, true, false, true, true, false, true, true, true, false, false, true, false, false, true, true, true, true, true, true, true, false, true, false, false, false];
          {
            pow_14047();
            of_pow(14080, false, false, false, true, false, true, true, true, true, true, true, true, false, false, true, false, false, true, true, true, false, true, true, false, true, false, false, true, true, false, false, false);
          }
          pow_mod_crc(14080);
        }
        calc {
          [false, false, true, true, true, false, false, true, false, false, true, true, false, false, true, true, true, true, false, false, false, false, true, true, true, false, false, true, false, false, true, false];
          {
            pow_7007();
            of_pow(7040, false, true, false, false, true, false, false, true, true, true, false, false, false, false, true, true, true, true, false, false, true, true, false, false, true, false, false, true, true, true, false, false);
          }
          pow_mod_crc(7040);
        }
      }
      pow_mod_crc(14080) + pow_mod_crc(7040);
    }
  }



  lemma lut_entry_110()
  ensures bits_of_int(lut[110] as int, 64)
      == pow_mod_crc(14208) + pow_mod_crc(7104)
  {
    calc {
      bits_of_int(lut[110] as int, 64);
      bits_of_int(6616352036705951488, 64);
      {
        lemma_bits_of_int_64_split(6616352036705951488);
      }
      bits_of_int(1489657600, 32) + bits_of_int(1540489503, 32);
      {
        unroll_bits_of_int_32_0x58ca5f00();
        unroll_bits_of_int_32_0x5bd2011f();
      }
      [false, false, false, false, false, false, false, false, true, true, true, true, true, false, true, false, false, true, false, true, false, false, true, true, false, false, false, true, true, false, true, false]+[true, true, true, true, true, false, false, false, true, false, false, false, false, false, false, false, false, true, false, false, true, false, true, true, true, true, false, true, true, false, true, false];
      {
        calc {
          [false, false, false, false, false, false, false, false, true, true, true, true, true, false, true, false, false, true, false, true, false, false, true, true, false, false, false, true, true, false, true, false];
          {
            pow_14175();
            of_pow(14208, false, true, false, true, true, false, false, false, true, true, false, false, true, false, true, false, false, true, false, true, true, true, true, true, false, false, false, false, false, false, false, false);
          }
          pow_mod_crc(14208);
        }
        calc {
          [true, true, true, true, true, false, false, false, true, false, false, false, false, false, false, false, false, true, false, false, true, false, true, true, true, true, false, true, true, false, true, false];
          {
            pow_7071();
            of_pow(7104, false, true, false, true, true, false, true, true, true, true, false, true, false, false, true, false, false, false, false, false, false, false, false, true, false, false, false, true, true, true, true, true);
          }
          pow_mod_crc(7104);
        }
      }
      pow_mod_crc(14208) + pow_mod_crc(7104);
    }
  }



  lemma lut_entry_111()
  ensures bits_of_int(lut[111] as int, 64)
      == pow_mod_crc(14336) + pow_mod_crc(7168)
  {
    calc {
      bits_of_int(lut[111] as int, 64);
      bits_of_int(7547162689110047445, 64);
      {
        lemma_bits_of_int_64_split(7547162689110047445);
      }
      bits_of_int(2860284629, 32) + bits_of_int(1757210746, 32);
      {
        unroll_bits_of_int_32_0xaa7c7ad5();
        unroll_bits_of_int_32_0x68bce87a();
      }
      [true, false, true, false, true, false, true, true, false, true, false, true, true, true, true, false, false, false, true, true, true, true, true, false, false, true, false, true, false, true, false, true]+[false, true, false, true, true, true, true, false, false, false, false, true, false, true, true, true, false, false, true, true, true, true, false, true, false, false, false, true, false, true, true, false];
      {
        calc {
          [true, false, true, false, true, false, true, true, false, true, false, true, true, true, true, false, false, false, true, true, true, true, true, false, false, true, false, true, false, true, false, true];
          {
            pow_14303();
            of_pow(14336, true, false, true, false, true, false, true, false, false, true, true, true, true, true, false, false, false, true, true, true, true, false, true, false, true, true, false, true, false, true, false, true);
          }
          pow_mod_crc(14336);
        }
        calc {
          [false, true, false, true, true, true, true, false, false, false, false, true, false, true, true, true, false, false, true, true, true, true, false, true, false, false, false, true, false, true, true, false];
          {
            pow_7135();
            of_pow(7168, false, true, true, false, true, false, false, false, true, false, true, true, true, true, false, false, true, true, true, false, true, false, false, false, false, true, true, true, true, false, true, false);
          }
          pow_mod_crc(7168);
        }
      }
      pow_mod_crc(14336) + pow_mod_crc(7168);
    }
  }



  lemma lut_entry_112()
  ensures bits_of_int(lut[112] as int, 64)
      == pow_mod_crc(14464) + pow_mod_crc(7232)
  {
    calc {
      bits_of_int(lut[112] as int, 64);
      bits_of_int(15926773986945387048, 64);
      {
        lemma_bits_of_int_64_split(15926773986945387048);
      }
      bits_of_int(3050293800, 32) + bits_of_int(3708241038, 32);
      {
        unroll_bits_of_int_32_0xb5cfca28();
        unroll_bits_of_int_32_0xdd07448e();
      }
      [false, false, false, true, false, true, false, false, false, true, false, true, false, false, true, true, true, true, true, true, false, false, true, true, true, false, true, false, true, true, false, true]+[false, true, true, true, false, false, false, true, false, false, true, false, false, false, true, false, true, true, true, false, false, false, false, false, true, false, true, true, true, false, true, true];
      {
        calc {
          [false, false, false, true, false, true, false, false, false, true, false, true, false, false, true, true, true, true, true, true, false, false, true, true, true, false, true, false, true, true, false, true];
          {
            pow_14431();
            of_pow(14464, true, false, true, true, false, true, false, true, true, true, false, false, true, true, true, true, true, true, false, false, true, false, true, false, false, false, true, false, true, false, false, false);
          }
          pow_mod_crc(14464);
        }
        calc {
          [false, true, true, true, false, false, false, true, false, false, true, false, false, false, true, false, true, true, true, false, false, false, false, false, true, false, true, true, true, false, true, true];
          {
            pow_7199();
            of_pow(7232, true, true, false, true, true, true, false, true, false, false, false, false, false, true, true, true, false, true, false, false, false, true, false, false, true, false, false, false, true, true, true, false);
          }
          pow_mod_crc(7232);
        }
      }
      pow_mod_crc(14464) + pow_mod_crc(7232);
    }
  }



  lemma lut_entry_113()
  ensures bits_of_int(lut[113] as int, 64)
      == pow_mod_crc(14592) + pow_mod_crc(7296)
  {
    calc {
      bits_of_int(lut[113] as int, 64);
      bits_of_int(6315120040883685624, 64);
      {
        lemma_bits_of_int_64_split(6315120040883685624);
      }
      bits_of_int(3738339576, 32) + bits_of_int(1470353463, 32);
      {
        unroll_bits_of_int_32_0xded288f8();
        unroll_bits_of_int_32_0x57a3d037();
      }
      [false, false, false, true, true, true, true, true, false, false, false, true, false, false, false, true, false, true, false, false, true, false, true, true, false, true, true, true, true, false, true, true]+[true, true, true, false, true, true, false, false, false, false, false, false, true, false, true, true, true, true, false, false, false, true, false, true, true, true, true, false, true, false, true, false];
      {
        calc {
          [false, false, false, true, true, true, true, true, false, false, false, true, false, false, false, true, false, true, false, false, true, false, true, true, false, true, true, true, true, false, true, true];
          {
            pow_14559();
            of_pow(14592, true, true, false, true, true, true, true, false, true, true, false, true, false, false, true, false, true, false, false, false, true, false, false, false, true, true, true, true, true, false, false, false);
          }
          pow_mod_crc(14592);
        }
        calc {
          [true, true, true, false, true, true, false, false, false, false, false, false, true, false, true, true, true, true, false, false, false, true, false, true, true, true, true, false, true, false, true, false];
          {
            pow_7263();
            of_pow(7296, false, true, false, true, false, true, true, true, true, false, true, false, false, false, true, true, true, true, false, true, false, false, false, false, false, false, true, true, false, true, true, true);
          }
          pow_mod_crc(7296);
        }
      }
      pow_mod_crc(14592) + pow_mod_crc(7296);
    }
  }



  lemma lut_entry_114()
  ensures bits_of_int(lut[114] as int, 64)
      == pow_mod_crc(14720) + pow_mod_crc(7360)
  {
    calc {
      bits_of_int(lut[114] as int, 64);
      bits_of_int(15990300653405743548, 64);
      {
        lemma_bits_of_int_64_split(15990300653405743548);
      }
      bits_of_int(1509042620, 32) + bits_of_int(3723031993, 32);
      {
        unroll_bits_of_int_32_0x59f229bc();
        unroll_bits_of_int_32_0xdde8f5b9();
      }
      [false, false, true, true, true, true, false, true, true, false, false, true, false, true, false, false, false, true, false, false, true, true, true, true, true, false, false, true, true, false, true, false]+[true, false, false, true, true, true, false, true, true, false, true, false, true, true, true, true, false, false, false, true, false, true, true, true, true, false, true, true, true, false, true, true];
      {
        calc {
          [false, false, true, true, true, true, false, true, true, false, false, true, false, true, false, false, false, true, false, false, true, true, true, true, true, false, false, true, true, false, true, false];
          {
            pow_14687();
            of_pow(14720, false, true, false, true, true, false, false, true, true, true, true, true, false, false, true, false, false, false, true, false, true, false, false, true, true, false, true, true, true, true, false, false);
          }
          pow_mod_crc(14720);
        }
        calc {
          [true, false, false, true, true, true, false, true, true, false, true, false, true, true, true, true, false, false, false, true, false, true, true, true, true, false, true, true, true, false, true, true];
          {
            pow_7327();
            of_pow(7360, true, true, false, true, true, true, false, true, true, true, true, false, true, false, false, false, true, true, true, true, false, true, false, true, true, false, true, true, true, false, false, true);
          }
          pow_mod_crc(7360);
        }
      }
      pow_mod_crc(14720) + pow_mod_crc(7360);
    }
  }



  lemma lut_entry_115()
  ensures bits_of_int(lut[115] as int, 64)
      == pow_mod_crc(14848) + pow_mod_crc(7424)
  {
    calc {
      bits_of_int(lut[115] as int, 64);
      bits_of_int(7590531554145275372, 64);
      {
        lemma_bits_of_int_64_split(7590531554145275372);
      }
      bits_of_int(1832455660, 32) + bits_of_int(1767308347, 32);
      {
        unroll_bits_of_int_32_0x6d390dec();
        unroll_bits_of_int_32_0x6956fc3b();
      }
      [false, false, true, true, false, true, true, true, true, false, true, true, false, false, false, false, true, false, false, true, true, true, false, false, true, false, true, true, false, true, true, false]+[true, true, false, true, true, true, false, false, false, false, true, true, true, true, true, true, false, true, true, false, true, false, true, false, true, false, false, true, false, true, true, false];
      {
        calc {
          [false, false, true, true, false, true, true, true, true, false, true, true, false, false, false, false, true, false, false, true, true, true, false, false, true, false, true, true, false, true, true, false];
          {
            pow_14815();
            of_pow(14848, false, true, true, false, true, true, false, true, false, false, true, true, true, false, false, true, false, false, false, false, true, true, false, true, true, true, true, false, true, true, false, false);
          }
          pow_mod_crc(14848);
        }
        calc {
          [true, true, false, true, true, true, false, false, false, false, true, true, true, true, true, true, false, true, true, false, true, false, true, false, true, false, false, true, false, true, true, false];
          {
            pow_7391();
            of_pow(7424, false, true, true, false, true, false, false, true, false, true, false, true, false, true, true, false, true, true, true, true, true, true, false, false, false, false, true, true, true, false, true, true);
          }
          pow_mod_crc(7424);
        }
      }
      pow_mod_crc(14848) + pow_mod_crc(7424);
    }
  }



  lemma lut_entry_116()
  ensures bits_of_int(lut[116] as int, 64)
      == pow_mod_crc(14976) + pow_mod_crc(7488)
  {
    calc {
      bits_of_int(lut[116] as int, 64);
      bits_of_int(11809529128403010448, 64);
      {
        lemma_bits_of_int_64_split(11809529128403010448);
      }
      bits_of_int(924255120, 32) + bits_of_int(2749620268, 32);
      {
        unroll_bits_of_int_32_0x37170390();
        unroll_bits_of_int_32_0xa3e3e02c();
      }
      [false, false, false, false, true, false, false, true, true, true, false, false, false, false, false, false, true, true, true, false, true, false, false, false, true, true, true, false, true, true, false, false]+[false, false, true, true, false, true, false, false, false, false, false, false, false, true, true, true, true, true, false, false, false, true, true, true, true, true, false, false, false, true, false, true];
      {
        calc {
          [false, false, false, false, true, false, false, true, true, true, false, false, false, false, false, false, true, true, true, false, true, false, false, false, true, true, true, false, true, true, false, false];
          {
            pow_14943();
            of_pow(14976, false, false, true, true, false, true, true, true, false, false, false, true, false, true, true, true, false, false, false, false, false, false, true, true, true, false, false, true, false, false, false, false);
          }
          pow_mod_crc(14976);
        }
        calc {
          [false, false, true, true, false, true, false, false, false, false, false, false, false, true, true, true, true, true, false, false, false, true, true, true, true, true, false, false, false, true, false, true];
          {
            pow_7455();
            of_pow(7488, true, false, true, false, false, false, true, true, true, true, true, false, false, false, true, true, true, true, true, false, false, false, false, false, false, false, true, false, true, true, false, false);
          }
          pow_mod_crc(7488);
        }
      }
      pow_mod_crc(14976) + pow_mod_crc(7488);
    }
  }



  lemma lut_entry_117()
  ensures bits_of_int(lut[117] as int, 64)
      == pow_mod_crc(15104) + pow_mod_crc(7552)
  {
    calc {
      bits_of_int(lut[117] as int, 64);
      bits_of_int(4817031395812819404, 64);
      {
        lemma_bits_of_int_64_split(4817031395812819404);
      }
      bits_of_int(1666433484, 32) + bits_of_int(1121552520, 32);
      {
        unroll_bits_of_int_32_0x6353c1cc();
        unroll_bits_of_int_32_0x42d98888();
      }
      [false, false, true, true, false, false, true, true, true, false, false, false, false, false, true, true, true, true, false, false, true, false, true, false, true, true, false, false, false, true, true, false]+[false, false, false, true, false, false, false, true, false, false, false, true, false, false, false, true, true, false, false, true, true, false, true, true, false, true, false, false, false, false, true, false];
      {
        calc {
          [false, false, true, true, false, false, true, true, true, false, false, false, false, false, true, true, true, true, false, false, true, false, true, false, true, true, false, false, false, true, true, false];
          {
            pow_15071();
            of_pow(15104, false, true, true, false, false, false, true, true, false, true, false, true, false, false, true, true, true, true, false, false, false, false, false, true, true, true, false, false, true, true, false, false);
          }
          pow_mod_crc(15104);
        }
        calc {
          [false, false, false, true, false, false, false, true, false, false, false, true, false, false, false, true, true, false, false, true, true, false, true, true, false, true, false, false, false, false, true, false];
          {
            pow_7519();
            of_pow(7552, false, true, false, false, false, false, true, false, true, true, false, true, true, false, false, true, true, false, false, false, true, false, false, false, true, false, false, false, true, false, false, false);
          }
          pow_mod_crc(7552);
        }
      }
      pow_mod_crc(15104) + pow_mod_crc(7552);
    }
  }



  lemma lut_entry_118()
  ensures bits_of_int(lut[118] as int, 64)
      == pow_mod_crc(15232) + pow_mod_crc(7616)
  {
    calc {
      bits_of_int(lut[118] as int, 64);
      bits_of_int(15509407465003831132, 64);
      {
        lemma_bits_of_int_64_split(15509407465003831132);
      }
      bits_of_int(3294121820, 32) + bits_of_int(3611065322, 32);
      {
        unroll_bits_of_int_32_0xc4584f5c();
        unroll_bits_of_int_32_0xd73c7bea();
      }
      [false, false, true, true, true, false, true, false, true, true, true, true, false, false, true, false, false, false, false, true, true, false, true, false, false, false, true, false, false, false, true, true]+[false, true, false, true, false, true, true, true, true, true, false, true, true, true, true, false, false, false, true, true, true, true, false, false, true, true, true, false, true, false, true, true];
      {
        calc {
          [false, false, true, true, true, false, true, false, true, true, true, true, false, false, true, false, false, false, false, true, true, false, true, false, false, false, true, false, false, false, true, true];
          {
            pow_15199();
            of_pow(15232, true, true, false, false, false, true, false, false, false, true, false, true, true, false, false, false, false, true, false, false, true, true, true, true, false, true, false, true, true, true, false, false);
          }
          pow_mod_crc(15232);
        }
        calc {
          [false, true, false, true, false, true, true, true, true, true, false, true, true, true, true, false, false, false, true, true, true, true, false, false, true, true, true, false, true, false, true, true];
          {
            pow_7583();
            of_pow(7616, true, true, false, true, false, true, true, true, false, false, true, true, true, true, false, false, false, true, true, true, true, false, true, true, true, true, true, false, true, false, true, false);
          }
          pow_mod_crc(7616);
        }
      }
      pow_mod_crc(15232) + pow_mod_crc(7616);
    }
  }



  lemma lut_entry_119()
  ensures bits_of_int(lut[119] as int, 64)
      == pow_mod_crc(15360) + pow_mod_crc(7680)
  {
    calc {
      bits_of_int(lut[119] as int, 64);
      bits_of_int(3995231148946375401, 64);
      {
        lemma_bits_of_int_64_split(3995231148946375401);
      }
      bits_of_int(4102439657, 32) + bits_of_int(930212239, 32);
      {
        unroll_bits_of_int_32_0xf48642e9();
        unroll_bits_of_int_32_0x3771e98f();
      }
      [true, false, false, true, false, true, true, true, false, true, false, false, false, false, true, false, false, true, true, false, false, false, false, true, false, false, true, false, true, true, true, true]+[true, true, true, true, false, false, false, true, true, false, false, true, false, true, true, true, true, false, false, false, true, true, true, false, true, true, true, false, true, true, false, false];
      {
        calc {
          [true, false, false, true, false, true, true, true, false, true, false, false, false, false, true, false, false, true, true, false, false, false, false, true, false, false, true, false, true, true, true, true];
          {
            pow_15327();
            of_pow(15360, true, true, true, true, false, true, false, false, true, false, false, false, false, true, true, false, false, true, false, false, false, false, true, false, true, true, true, false, true, false, false, true);
          }
          pow_mod_crc(15360);
        }
        calc {
          [true, true, true, true, false, false, false, true, true, false, false, true, false, true, true, true, true, false, false, false, true, true, true, false, true, true, true, false, true, true, false, false];
          {
            pow_7647();
            of_pow(7680, false, false, true, true, false, true, true, true, false, true, true, true, false, false, false, true, true, true, true, false, true, false, false, true, true, false, false, false, true, true, true, true);
          }
          pow_mod_crc(7680);
        }
      }
      pow_mod_crc(15360) + pow_mod_crc(7680);
    }
  }



  lemma lut_entry_120()
  ensures bits_of_int(lut[120] as int, 64)
      == pow_mod_crc(15488) + pow_mod_crc(7744)
  {
    calc {
      bits_of_int(lut[120] as int, 64);
      bits_of_int(9295148788669970402, 64);
      {
        lemma_bits_of_int_64_split(9295148788669970402);
      }
      bits_of_int(1393784802, 32) + bits_of_int(2164195475, 32);
      {
        unroll_bits_of_int_32_0x531377e2();
        unroll_bits_of_int_32_0x80ff0093();
      }
      [false, true, false, false, false, true, true, true, true, true, true, false, true, true, true, false, true, true, false, false, true, false, false, false, true, true, false, false, true, false, true, false]+[true, true, false, false, true, false, false, true, false, false, false, false, false, false, false, false, true, true, true, true, true, true, true, true, false, false, false, false, false, false, false, true];
      {
        calc {
          [false, true, false, false, false, true, true, true, true, true, true, false, true, true, true, false, true, true, false, false, true, false, false, false, true, true, false, false, true, false, true, false];
          {
            pow_15455();
            of_pow(15488, false, true, false, true, false, false, true, true, false, false, false, true, false, false, true, true, false, true, true, true, false, true, true, true, true, true, true, false, false, false, true, false);
          }
          pow_mod_crc(15488);
        }
        calc {
          [true, true, false, false, true, false, false, true, false, false, false, false, false, false, false, false, true, true, true, true, true, true, true, true, false, false, false, false, false, false, false, true];
          {
            pow_7711();
            of_pow(7744, true, false, false, false, false, false, false, false, true, true, true, true, true, true, true, true, false, false, false, false, false, false, false, false, true, false, false, true, false, false, true, true);
          }
          pow_mod_crc(7744);
        }
      }
      pow_mod_crc(15488) + pow_mod_crc(7744);
    }
  }



  lemma lut_entry_121()
  ensures bits_of_int(lut[121] as int, 64)
      == pow_mod_crc(15616) + pow_mod_crc(7808)
  {
    calc {
      bits_of_int(lut[121] as int, 64);
      bits_of_int(12982439400707570829, 64);
      {
        lemma_bits_of_int_64_split(12982439400707570829);
      }
      bits_of_int(3711286413, 32) + bits_of_int(3022709721, 32);
      {
        unroll_bits_of_int_32_0xdd35bc8d();
        unroll_bits_of_int_32_0xb42ae3d9();
      }
      [true, false, true, true, false, false, false, true, false, false, true, true, true, true, false, true, true, false, true, false, true, true, false, false, true, false, true, true, true, false, true, true]+[true, false, false, true, true, false, true, true, true, true, false, false, false, true, true, true, false, true, false, true, false, true, false, false, false, false, true, false, true, true, false, true];
      {
        calc {
          [true, false, true, true, false, false, false, true, false, false, true, true, true, true, false, true, true, false, true, false, true, true, false, false, true, false, true, true, true, false, true, true];
          {
            pow_15583();
            of_pow(15616, true, true, false, true, true, true, false, true, false, false, true, true, false, true, false, true, true, false, true, true, true, true, false, false, true, false, false, false, true, true, false, true);
          }
          pow_mod_crc(15616);
        }
        calc {
          [true, false, false, true, true, false, true, true, true, true, false, false, false, true, true, true, false, true, false, true, false, true, false, false, false, false, true, false, true, true, false, true];
          {
            pow_7775();
            of_pow(7808, true, false, true, true, false, true, false, false, false, false, true, false, true, false, true, false, true, true, true, false, false, false, true, true, true, true, false, true, true, false, false, true);
          }
          pow_mod_crc(7808);
        }
      }
      pow_mod_crc(15616) + pow_mod_crc(7808);
    }
  }



  lemma lut_entry_122()
  ensures bits_of_int(lut[122] as int, 64)
      == pow_mod_crc(15744) + pow_mod_crc(7872)
  {
    calc {
      bits_of_int(lut[122] as int, 64);
      bits_of_int(10368626980585941490, 64);
      {
        lemma_bits_of_int_64_split(10368626980585941490);
      }
      bits_of_int(2992318962, 32) + bits_of_int(2414134093, 32);
      {
        unroll_bits_of_int_32_0xb25b29f2();
        unroll_bits_of_int_32_0x8fe4c34d();
      }
      [false, true, false, false, true, true, true, true, true, false, false, true, false, true, false, false, true, true, false, true, true, false, true, false, false, true, false, false, true, true, false, true]+[true, false, true, true, false, false, true, false, true, true, false, false, false, false, true, true, false, false, true, false, false, true, true, true, true, true, true, true, false, false, false, true];
      {
        calc {
          [false, true, false, false, true, true, true, true, true, false, false, true, false, true, false, false, true, true, false, true, true, false, true, false, false, true, false, false, true, true, false, true];
          {
            pow_15711();
            of_pow(15744, true, false, true, true, false, false, true, false, false, true, false, true, true, false, true, true, false, false, true, false, true, false, false, true, true, true, true, true, false, false, true, false);
          }
          pow_mod_crc(15744);
        }
        calc {
          [true, false, true, true, false, false, true, false, true, true, false, false, false, false, true, true, false, false, true, false, false, true, true, true, true, true, true, true, false, false, false, true];
          {
            pow_7839();
            of_pow(7872, true, false, false, false, true, true, true, true, true, true, true, false, false, true, false, false, true, true, false, false, false, false, true, true, false, true, false, false, true, true, false, true);
          }
          pow_mod_crc(7872);
        }
      }
      pow_mod_crc(15744) + pow_mod_crc(7872);
    }
  }



  lemma lut_entry_123()
  ensures bits_of_int(lut[123] as int, 64)
      == pow_mod_crc(15872) + pow_mod_crc(7936)
  {
    calc {
      bits_of_int(lut[123] as int, 64);
      bits_of_int(2411766912596762177, 64);
      {
        lemma_bits_of_int_64_split(2411766912596762177);
      }
      bits_of_int(2589908545, 32) + bits_of_int(561533242, 32);
      {
        unroll_bits_of_int_32_0x9a5ede41();
        unroll_bits_of_int_32_0x2178513a();
      }
      [true, false, false, false, false, false, true, false, false, true, true, true, true, false, true, true, false, true, true, true, true, false, true, false, false, true, false, true, true, false, false, true]+[false, true, false, true, true, true, false, false, true, false, false, false, true, false, true, false, false, false, false, true, true, true, true, false, true, false, false, false, false, true, false, false];
      {
        calc {
          [true, false, false, false, false, false, true, false, false, true, true, true, true, false, true, true, false, true, true, true, true, false, true, false, false, true, false, true, true, false, false, true];
          {
            pow_15839();
            of_pow(15872, true, false, false, true, true, false, true, false, false, true, false, true, true, true, true, false, true, true, false, true, true, true, true, false, false, true, false, false, false, false, false, true);
          }
          pow_mod_crc(15872);
        }
        calc {
          [false, true, false, true, true, true, false, false, true, false, false, false, true, false, true, false, false, false, false, true, true, true, true, false, true, false, false, false, false, true, false, false];
          {
            pow_7903();
            of_pow(7936, false, false, true, false, false, false, false, true, false, true, true, true, true, false, false, false, false, true, false, true, false, false, false, true, false, false, true, true, true, false, true, false);
          }
          pow_mod_crc(7936);
        }
      }
      pow_mod_crc(15872) + pow_mod_crc(7936);
    }
  }



  lemma lut_entry_124()
  ensures bits_of_int(lut[124] as int, 64)
      == pow_mod_crc(16000) + pow_mod_crc(8000)
  {
    calc {
      bits_of_int(lut[124] as int, 64);
      bits_of_int(16112186294614069341, 64);
      {
        lemma_bits_of_int_64_split(16112186294614069341);
      }
      bits_of_int(2774765661, 32) + bits_of_int(3751410705, 32);
      {
        unroll_bits_of_int_32_0xa563905d();
        unroll_bits_of_int_32_0xdf99fc11();
      }
      [true, false, true, true, true, false, true, false, false, false, false, false, true, false, false, true, true, true, false, false, false, true, true, false, true, false, true, false, false, true, false, true]+[true, false, false, false, true, false, false, false, false, false, true, true, true, true, true, true, true, false, false, true, true, false, false, true, true, true, true, true, true, false, true, true];
      {
        calc {
          [true, false, true, true, true, false, true, false, false, false, false, false, true, false, false, true, true, true, false, false, false, true, true, false, true, false, true, false, false, true, false, true];
          {
            pow_15967();
            of_pow(16000, true, false, true, false, false, true, false, true, false, true, true, false, false, false, true, true, true, false, false, true, false, false, false, false, false, true, false, true, true, true, false, true);
          }
          pow_mod_crc(16000);
        }
        calc {
          [true, false, false, false, true, false, false, false, false, false, true, true, true, true, true, true, true, false, false, true, true, false, false, true, true, true, true, true, true, false, true, true];
          {
            pow_7967();
            of_pow(8000, true, true, false, true, true, true, true, true, true, false, false, true, true, false, false, true, true, true, true, true, true, true, false, false, false, false, false, true, false, false, false, true);
          }
          pow_mod_crc(8000);
        }
      }
      pow_mod_crc(16000) + pow_mod_crc(8000);
    }
  }



  lemma lut_entry_125()
  ensures bits_of_int(lut[125] as int, 64)
      == pow_mod_crc(16128) + pow_mod_crc(8064)
  {
    calc {
      bits_of_int(lut[125] as int, 64);
      bits_of_int(16189336330986970958, 64);
      {
        lemma_bits_of_int_64_split(16189336330986970958);
      }
      bits_of_int(1171119950, 32) + bits_of_int(3769373598, 32);
      {
        unroll_bits_of_int_32_0x45cddf4e();
        unroll_bits_of_int_32_0xe0ac139e();
      }
      [false, true, true, true, false, false, true, false, true, true, true, true, true, false, true, true, true, false, true, true, false, false, true, true, true, false, true, false, false, false, true, false]+[false, true, true, true, true, false, false, true, true, true, false, false, true, false, false, false, false, false, true, true, false, true, false, true, false, false, false, false, false, true, true, true];
      {
        calc {
          [false, true, true, true, false, false, true, false, true, true, true, true, true, false, true, true, true, false, true, true, false, false, true, true, true, false, true, false, false, false, true, false];
          {
            pow_16095();
            of_pow(16128, false, true, false, false, false, true, false, true, true, true, false, false, true, true, false, true, true, true, false, true, true, true, true, true, false, true, false, false, true, true, true, false);
          }
          pow_mod_crc(16128);
        }
        calc {
          [false, true, true, true, true, false, false, true, true, true, false, false, true, false, false, false, false, false, true, true, false, true, false, true, false, false, false, false, false, true, true, true];
          {
            pow_8031();
            of_pow(8064, true, true, true, false, false, false, false, false, true, false, true, false, true, true, false, false, false, false, false, true, false, false, true, true, true, false, false, true, true, true, true, false);
          }
          pow_mod_crc(8064);
        }
      }
      pow_mod_crc(16128) + pow_mod_crc(8064);
    }
  }



  lemma lut_entry_126()
  ensures bits_of_int(lut[126] as int, 64)
      == pow_mod_crc(16256) + pow_mod_crc(8128)
  {
    calc {
      bits_of_int(lut[126] as int, 64);
      bits_of_int(7792327149053686019, 64);
      {
        lemma_bits_of_int_64_split(7792327149053686019);
      }
      bits_of_int(2902077699, 32) + bits_of_int(1814292545, 32);
      {
        unroll_bits_of_int_32_0xacfa3103();
        unroll_bits_of_int_32_0x6c23e841();
      }
      [true, true, false, false, false, false, false, false, true, false, false, false, true, true, false, false, false, true, false, true, true, true, true, true, false, false, true, true, false, true, false, true]+[true, false, false, false, false, false, true, false, false, false, false, true, false, true, true, true, true, true, false, false, false, true, false, false, false, false, true, true, false, true, true, false];
      {
        calc {
          [true, true, false, false, false, false, false, false, true, false, false, false, true, true, false, false, false, true, false, true, true, true, true, true, false, false, true, true, false, true, false, true];
          {
            pow_16223();
            of_pow(16256, true, false, true, false, true, true, false, false, true, true, true, true, true, false, true, false, false, false, true, true, false, false, false, true, false, false, false, false, false, false, true, true);
          }
          pow_mod_crc(16256);
        }
        calc {
          [true, false, false, false, false, false, true, false, false, false, false, true, false, true, true, true, true, true, false, false, false, true, false, false, false, false, true, true, false, true, true, false];
          {
            pow_8095();
            of_pow(8128, false, true, true, false, true, true, false, false, false, false, true, false, false, false, true, true, true, true, true, false, true, false, false, false, false, true, false, false, false, false, false, true);
          }
          pow_mod_crc(8128);
        }
      }
      pow_mod_crc(16256) + pow_mod_crc(8128);
    }
  }



  lemma lut_entry_127()
  ensures bits_of_int(lut[127] as int, 64)
      == pow_mod_crc(16384) + pow_mod_crc(8192)
  {
    calc {
      bits_of_int(lut[127] as int, 64);
      bits_of_int(1657455481756279093, 64);
      {
        lemma_bits_of_int_64_split(1657455481756279093);
      }
      bits_of_int(2770034997, 32) + bits_of_int(385906426, 32);
      {
        unroll_bits_of_int_32_0xa51b6135();
        unroll_bits_of_int_32_0x170076fa();
      }
      [true, false, true, false, true, true, false, false, true, false, false, false, false, true, true, false, true, true, false, true, true, false, false, false, true, false, true, false, false, true, false, true]+[false, true, false, true, true, true, true, true, false, true, true, false, true, true, true, false, false, false, false, false, false, false, false, false, true, true, true, false, true, false, false, false];
      {
        calc {
          [true, false, true, false, true, true, false, false, true, false, false, false, false, true, true, false, true, true, false, true, true, false, false, false, true, false, true, false, false, true, false, true];
          {
            pow_16351();
            of_pow(16384, true, false, true, false, false, true, false, true, false, false, false, true, true, false, true, true, false, true, true, false, false, false, false, true, false, false, true, true, false, true, false, true);
          }
          pow_mod_crc(16384);
        }
        calc {
          [false, true, false, true, true, true, true, true, false, true, true, false, true, true, true, false, false, false, false, false, false, false, false, false, true, true, true, false, true, false, false, false];
          {
            pow_8159();
            of_pow(8192, false, false, false, true, false, true, true, true, false, false, false, false, false, false, false, false, false, true, true, true, false, true, true, false, true, true, true, true, true, false, true, false);
          }
          pow_mod_crc(8192);
        }
      }
      pow_mod_crc(16384) + pow_mod_crc(8192);
    }
  }



  lemma lut_entry_128()
  ensures bits_of_int(lut[128] as int, 64)
      == pow_mod_crc(16512) + pow_mod_crc(8256)
  {
    calc {
      bits_of_int(lut[128] as int, 64);
      bits_of_int(18316494108972634034, 64);
      {
        lemma_bits_of_int_64_split(18316494108972634034);
      }
      bits_of_int(3755560882, 32) + bits_of_int(4264641112, 32);
      {
        unroll_bits_of_int_32_0xdfd94fb2();
        unroll_bits_of_int_32_0xfe314258();
      }
      [false, true, false, false, true, true, false, true, true, true, true, true, false, false, true, false, true, false, false, true, true, false, true, true, true, true, true, true, true, false, true, true]+[false, false, false, true, true, false, true, false, false, true, false, false, false, false, true, false, true, false, false, false, true, true, false, false, false, true, true, true, true, true, true, true];
      {
        calc {
          [false, true, false, false, true, true, false, true, true, true, true, true, false, false, true, false, true, false, false, true, true, false, true, true, true, true, true, true, true, false, true, true];
          {
            pow_16479();
            of_pow(16512, true, true, false, true, true, true, true, true, true, true, false, true, true, false, false, true, false, true, false, false, true, true, true, true, true, false, true, true, false, false, true, false);
          }
          pow_mod_crc(16512);
        }
        calc {
          [false, false, false, true, true, false, true, false, false, true, false, false, false, false, true, false, true, false, false, false, true, true, false, false, false, true, true, true, true, true, true, true];
          {
            pow_8223();
            of_pow(8256, true, true, true, true, true, true, true, false, false, false, true, true, false, false, false, true, false, true, false, false, false, false, true, false, false, true, false, true, true, false, false, false);
          }
          pow_mod_crc(8256);
        }
      }
      pow_mod_crc(16512) + pow_mod_crc(8256);
    }
  }



  lemma lut_entry_129()
  ensures bits_of_int(lut[129] as int, 64)
      == pow_mod_crc(16640) + pow_mod_crc(8320)
  {
    calc {
      bits_of_int(lut[129] as int, 64);
      bits_of_int(4921823148018665579, 64);
      {
        lemma_bits_of_int_64_split(4921823148018665579);
      }
      bits_of_int(2163378283, 32) + bits_of_int(1145951251, 32);
      {
        unroll_bits_of_int_32_0x80f2886b();
        unroll_bits_of_int_32_0x444dd413();
      }
      [true, true, false, true, false, true, true, false, false, false, false, true, false, false, false, true, false, true, false, false, true, true, true, true, false, false, false, false, false, false, false, true]+[true, true, false, false, true, false, false, false, false, false, true, false, true, false, true, true, true, false, true, true, false, false, true, false, false, false, true, false, false, false, true, false];
      {
        calc {
          [true, true, false, true, false, true, true, false, false, false, false, true, false, false, false, true, false, true, false, false, true, true, true, true, false, false, false, false, false, false, false, true];
          {
            pow_16607();
            of_pow(16640, true, false, false, false, false, false, false, false, true, true, true, true, false, false, true, false, true, false, false, false, true, false, false, false, false, true, true, false, true, false, true, true);
          }
          pow_mod_crc(16640);
        }
        calc {
          [true, true, false, false, true, false, false, false, false, false, true, false, true, false, true, true, true, false, true, true, false, false, true, false, false, false, true, false, false, false, true, false];
          {
            pow_8287();
            of_pow(8320, false, true, false, false, false, true, false, false, false, true, false, false, true, true, false, true, true, true, false, true, false, true, false, false, false, false, false, true, false, false, true, true);
          }
          pow_mod_crc(8320);
        }
      }
      pow_mod_crc(16640) + pow_mod_crc(8320);
    }
  }



  lemma lut_entry_130()
  ensures bits_of_int(lut[130] as int, 64)
      == pow_mod_crc(16768) + pow_mod_crc(8384)
  {
    calc {
      bits_of_int(lut[130] as int, 64);
      bits_of_int(973749077212043882, 64);
      {
        lemma_bits_of_int_64_split(973749077212043882);
      }
      bits_of_int(1737923178, 32) + bits_of_int(226718624, 32);
      {
        unroll_bits_of_int_32_0x67969a6a();
        unroll_bits_of_int_32_0x0d8373a0();
      }
      [false, true, false, true, false, true, true, false, false, true, false, true, true, false, false, true, false, true, true, false, true, false, false, true, true, true, true, false, false, true, true, false]+[false, false, false, false, false, true, false, true, true, true, false, false, true, true, true, false, true, true, false, false, false, false, false, true, true, false, true, true, false, false, false, false];
      {
        calc {
          [false, true, false, true, false, true, true, false, false, true, false, true, true, false, false, true, false, true, true, false, true, false, false, true, true, true, true, false, false, true, true, false];
          {
            pow_16735();
            of_pow(16768, false, true, true, false, false, true, true, true, true, false, false, true, false, true, true, false, true, false, false, true, true, false, true, false, false, true, true, false, true, false, true, false);
          }
          pow_mod_crc(16768);
        }
        calc {
          [false, false, false, false, false, true, false, true, true, true, false, false, true, true, true, false, true, true, false, false, false, false, false, true, true, false, true, true, false, false, false, false];
          {
            pow_8351();
            of_pow(8384, false, false, false, false, true, true, false, true, true, false, false, false, false, false, true, true, false, true, true, true, false, false, true, true, true, false, true, false, false, false, false, false);
          }
          pow_mod_crc(8384);
        }
      }
      pow_mod_crc(16768) + pow_mod_crc(8384);
    }
  }



  lemma lut_entry_131()
  ensures bits_of_int(lut[131] as int, 64)
      == pow_mod_crc(16896) + pow_mod_crc(8448)
  {
    calc {
      bits_of_int(lut[131] as int, 64);
      bits_of_int(8013133287480018415, 64);
      {
        lemma_bits_of_int_64_split(8013133287480018415);
      }
      bits_of_int(35309039, 32) + bits_of_int(1865702981, 32);
      {
        unroll_bits_of_int_32_0x021ac5ef();
        unroll_bits_of_int_32_0x6f345e45();
      }
      [true, true, true, true, false, true, true, true, true, false, true, false, false, false, true, true, false, true, false, true, true, false, false, false, false, true, false, false, false, false, false, false]+[true, false, true, false, false, false, true, false, false, true, true, true, true, false, true, false, false, false, true, false, true, true, false, false, true, true, true, true, false, true, true, false];
      {
        calc {
          [true, true, true, true, false, true, true, true, true, false, true, false, false, false, true, true, false, true, false, true, true, false, false, false, false, true, false, false, false, false, false, false];
          {
            pow_16863();
            of_pow(16896, false, false, false, false, false, false, true, false, false, false, false, true, true, false, true, false, true, true, false, false, false, true, false, true, true, true, true, false, true, true, true, true);
          }
          pow_mod_crc(16896);
        }
        calc {
          [true, false, true, false, false, false, true, false, false, true, true, true, true, false, true, false, false, false, true, false, true, true, false, false, true, true, true, true, false, true, true, false];
          {
            pow_8415();
            of_pow(8448, false, true, true, false, true, true, true, true, false, false, true, true, false, true, false, false, false, true, false, true, true, true, true, false, false, true, false, false, false, true, false, true);
          }
          pow_mod_crc(8448);
        }
      }
      pow_mod_crc(16896) + pow_mod_crc(8448);
    }
  }



  lemma lut_entry_132()
  ensures bits_of_int(lut[132] as int, 64)
      == pow_mod_crc(17024) + pow_mod_crc(8512)
  {
    calc {
      bits_of_int(lut[132] as int, 64);
      bits_of_int(1865443929935121146, 64);
      {
        lemma_bits_of_int_64_split(1865443929935121146);
      }
      bits_of_int(3895528186, 32) + bits_of_int(434332510, 32);
      {
        unroll_bits_of_int_32_0xe8310afa();
        unroll_bits_of_int_32_0x19e3635e();
      }
      [false, true, false, true, true, true, true, true, false, true, false, true, false, false, false, false, true, false, false, false, true, true, false, false, false, false, false, true, false, true, true, true]+[false, true, true, true, true, false, true, false, true, true, false, false, false, true, true, false, true, true, false, false, false, true, true, true, true, false, false, true, true, false, false, false];
      {
        calc {
          [false, true, false, true, true, true, true, true, false, true, false, true, false, false, false, false, true, false, false, false, true, true, false, false, false, false, false, true, false, true, true, true];
          {
            pow_16991();
            of_pow(17024, true, true, true, false, true, false, false, false, false, false, true, true, false, false, false, true, false, false, false, false, true, false, true, false, true, true, true, true, true, false, true, false);
          }
          pow_mod_crc(17024);
        }
        calc {
          [false, true, true, true, true, false, true, false, true, true, false, false, false, true, true, false, true, true, false, false, false, true, true, true, true, false, false, true, true, false, false, false];
          {
            pow_8479();
            of_pow(8512, false, false, false, true, true, false, false, true, true, true, true, false, false, false, true, true, false, true, true, false, false, false, true, true, false, true, false, true, true, true, true, false);
          }
          pow_mod_crc(8512);
        }
      }
      pow_mod_crc(17024) + pow_mod_crc(8512);
    }
  }



  lemma lut_entry_133()
  ensures bits_of_int(lut[133] as int, 64)
      == pow_mod_crc(17152) + pow_mod_crc(8576)
  {
    calc {
      bits_of_int(lut[133] as int, 64);
      bits_of_int(4742707553992252164, 64);
      {
        lemma_bits_of_int_64_split(4742707553992252164);
      }
      bits_of_int(1967463172, 32) + bits_of_int(1104247652, 32);
      {
        unroll_bits_of_int_32_0x75451b04();
        unroll_bits_of_int_32_0x41d17b64();
      }
      [false, false, true, false, false, false, false, false, true, true, false, true, true, false, false, false, true, false, true, false, false, false, true, false, true, false, true, false, true, true, true, false]+[false, false, true, false, false, true, true, false, true, true, false, true, true, true, true, false, true, false, false, false, true, false, true, true, true, false, false, false, false, false, true, false];
      {
        calc {
          [false, false, true, false, false, false, false, false, true, true, false, true, true, false, false, false, true, false, true, false, false, false, true, false, true, false, true, false, true, true, true, false];
          {
            pow_17119();
            of_pow(17152, false, true, true, true, false, true, false, true, false, true, false, false, false, true, false, true, false, false, false, true, true, false, true, true, false, false, false, false, false, true, false, false);
          }
          pow_mod_crc(17152);
        }
        calc {
          [false, false, true, false, false, true, true, false, true, true, false, true, true, true, true, false, true, false, false, false, true, false, true, true, true, false, false, false, false, false, true, false];
          {
            pow_8543();
            of_pow(8576, false, true, false, false, false, false, false, true, true, true, false, true, false, false, false, true, false, true, true, true, true, false, true, true, false, true, true, false, false, true, false, false);
          }
          pow_mod_crc(8576);
        }
      }
      pow_mod_crc(17152) + pow_mod_crc(8576);
    }
  }



  lemma lut_entry_134()
  ensures bits_of_int(lut[134] as int, 64)
      == pow_mod_crc(17280) + pow_mod_crc(8640)
  {
    calc {
      bits_of_int(lut[134] as int, 64);
      bits_of_int(3022593424606122231, 64);
      {
        lemma_bits_of_int_64_split(3022593424606122231);
      }
      bits_of_int(2383696119, 32) + bits_of_int(703752372, 32);
      {
        unroll_bits_of_int_32_0x8e1450f7();
        unroll_bits_of_int_32_0x29f268b4();
      }
      [true, true, true, false, true, true, true, true, false, false, false, false, true, false, true, false, false, false, true, false, true, false, false, false, false, true, true, true, false, false, false, true]+[false, false, true, false, true, true, false, true, false, false, false, true, false, true, true, false, false, true, false, false, true, true, true, true, true, false, false, true, false, true, false, false];
      {
        calc {
          [true, true, true, false, true, true, true, true, false, false, false, false, true, false, true, false, false, false, true, false, true, false, false, false, false, true, true, true, false, false, false, true];
          {
            pow_17247();
            of_pow(17280, true, false, false, false, true, true, true, false, false, false, false, true, false, true, false, false, false, true, false, true, false, false, false, false, true, true, true, true, false, true, true, true);
          }
          pow_mod_crc(17280);
        }
        calc {
          [false, false, true, false, true, true, false, true, false, false, false, true, false, true, true, false, false, true, false, false, true, true, true, true, true, false, false, true, false, true, false, false];
          {
            pow_8607();
            of_pow(8640, false, false, true, false, true, false, false, true, true, true, true, true, false, false, true, false, false, true, true, false, true, false, false, false, true, false, true, true, false, true, false, false);
          }
          pow_mod_crc(8640);
        }
      }
      pow_mod_crc(17280) + pow_mod_crc(8640);
    }
  }



  lemma lut_entry_135()
  ensures bits_of_int(lut[135] as int, 64)
      == pow_mod_crc(17408) + pow_mod_crc(8704)
  {
    calc {
      bits_of_int(lut[135] as int, 64);
      bits_of_int(18378550815489937121, 64);
      {
        lemma_bits_of_int_64_split(18378550815489937121);
      }
      bits_of_int(3418246881, 32) + bits_of_int(4279089815, 32);
      {
        unroll_bits_of_int_32_0xcbbe4ee1();
        unroll_bits_of_int_32_0xff0dba97();
      }
      [true, false, false, false, false, true, true, true, false, true, true, true, false, false, true, false, false, true, true, true, true, true, false, true, true, true, false, true, false, false, true, true]+[true, true, true, false, true, false, false, true, false, true, false, true, true, true, false, true, true, false, true, true, false, false, false, false, true, true, true, true, true, true, true, true];
      {
        calc {
          [true, false, false, false, false, true, true, true, false, true, true, true, false, false, true, false, false, true, true, true, true, true, false, true, true, true, false, true, false, false, true, true];
          {
            pow_17375();
            of_pow(17408, true, true, false, false, true, false, true, true, true, false, true, true, true, true, true, false, false, true, false, false, true, true, true, false, true, true, true, false, false, false, false, true);
          }
          pow_mod_crc(17408);
        }
        calc {
          [true, true, true, false, true, false, false, true, false, true, false, true, true, true, false, true, true, false, true, true, false, false, false, false, true, true, true, true, true, true, true, true];
          {
            pow_8671();
            of_pow(8704, true, true, true, true, true, true, true, true, false, false, false, false, true, true, false, true, true, false, true, true, true, false, true, false, true, false, false, true, false, true, true, true);
          }
          pow_mod_crc(8704);
        }
      }
      pow_mod_crc(17408) + pow_mod_crc(8704);
    }
  }



  lemma lut_entry_136()
  ensures bits_of_int(lut[136] as int, 64)
      == pow_mod_crc(17536) + pow_mod_crc(8768)
  {
    calc {
      bits_of_int(lut[136] as int, 64);
      bits_of_int(2143822455649852961, 64);
      {
        lemma_bits_of_int_64_split(2143822455649852961);
      }
      bits_of_int(981720609, 32) + bits_of_int(499147562, 32);
      {
        unroll_bits_of_int_32_0x3a83de21();
        unroll_bits_of_int_32_0x1dc0632a();
      }
      [true, false, false, false, false, true, false, false, false, true, true, true, true, false, true, true, true, true, false, false, false, false, false, true, false, true, false, true, true, true, false, false]+[false, true, false, true, false, true, false, false, true, true, false, false, false, true, true, false, false, false, false, false, false, false, true, true, true, false, true, true, true, false, false, false];
      {
        calc {
          [true, false, false, false, false, true, false, false, false, true, true, true, true, false, true, true, true, true, false, false, false, false, false, true, false, true, false, true, true, true, false, false];
          {
            pow_17503();
            of_pow(17536, false, false, true, true, true, false, true, false, true, false, false, false, false, false, true, true, true, true, false, true, true, true, true, false, false, false, true, false, false, false, false, true);
          }
          pow_mod_crc(17536);
        }
        calc {
          [false, true, false, true, false, true, false, false, true, true, false, false, false, true, true, false, false, false, false, false, false, false, true, true, true, false, true, true, true, false, false, false];
          {
            pow_8735();
            of_pow(8768, false, false, false, true, true, true, false, true, true, true, false, false, false, false, false, false, false, true, true, false, false, false, true, true, false, false, true, false, true, false, true, false);
          }
          pow_mod_crc(8768);
        }
      }
      pow_mod_crc(17536) + pow_mod_crc(8768);
    }
  }



  lemma lut_entry_137()
  ensures bits_of_int(lut[137] as int, 64)
      == pow_mod_crc(17664) + pow_mod_crc(8832)
  {
    calc {
      bits_of_int(lut[137] as int, 64);
      bits_of_int(11724908263950372742, 64);
      {
        lemma_bits_of_int_64_split(11724908263950372742);
      }
      bits_of_int(3771584390, 32) + bits_of_int(2729917937, 32);
      {
        unroll_bits_of_int_32_0xe0cdcf86();
        unroll_bits_of_int_32_0xa2b73df1();
      }
      [false, true, true, false, false, false, false, true, true, true, true, true, false, false, true, true, true, false, true, true, false, false, true, true, false, false, false, false, false, true, true, true]+[true, false, false, false, true, true, true, true, true, false, true, true, true, true, false, false, true, true, true, false, true, true, false, true, false, true, false, false, false, true, false, true];
      {
        calc {
          [false, true, true, false, false, false, false, true, true, true, true, true, false, false, true, true, true, false, true, true, false, false, true, true, false, false, false, false, false, true, true, true];
          {
            pow_17631();
            of_pow(17664, true, true, true, false, false, false, false, false, true, true, false, false, true, true, false, true, true, true, false, false, true, true, true, true, true, false, false, false, false, true, true, false);
          }
          pow_mod_crc(17664);
        }
        calc {
          [true, false, false, false, true, true, true, true, true, false, true, true, true, true, false, false, true, true, true, false, true, true, false, true, false, true, false, false, false, true, false, true];
          {
            pow_8799();
            of_pow(8832, true, false, true, false, false, false, true, false, true, false, true, true, false, true, true, true, false, false, true, true, true, true, false, true, true, true, true, true, false, false, false, true);
          }
          pow_mod_crc(8832);
        }
      }
      pow_mod_crc(17664) + pow_mod_crc(8832);
    }
  }



  lemma lut_entry_138()
  ensures bits_of_int(lut[138] as int, 64)
      == pow_mod_crc(17792) + pow_mod_crc(8896)
  {
    calc {
      bits_of_int(lut[138] as int, 64);
      bits_of_int(1591164395100837497, 64);
      {
        lemma_bits_of_int_64_split(1591164395100837497);
      }
      bits_of_int(1161565817, 32) + bits_of_int(370471830, 32);
      {
        unroll_bits_of_int_32_0x453c1679();
        unroll_bits_of_int_32_0x1614f396();
      }
      [true, false, false, true, true, true, true, false, false, true, true, false, true, false, false, false, false, false, true, true, true, true, false, false, true, false, true, false, false, false, true, false]+[false, true, true, false, true, false, false, true, true, true, false, false, true, true, true, true, false, false, true, false, true, false, false, false, false, true, true, false, true, false, false, false];
      {
        calc {
          [true, false, false, true, true, true, true, false, false, true, true, false, true, false, false, false, false, false, true, true, true, true, false, false, true, false, true, false, false, false, true, false];
          {
            pow_17759();
            of_pow(17792, false, true, false, false, false, true, false, true, false, false, true, true, true, true, false, false, false, false, false, true, false, true, true, false, false, true, true, true, true, false, false, true);
          }
          pow_mod_crc(17792);
        }
        calc {
          [false, true, true, false, true, false, false, true, true, true, false, false, true, true, true, true, false, false, true, false, true, false, false, false, false, true, true, false, true, false, false, false];
          {
            pow_8863();
            of_pow(8896, false, false, false, true, false, true, true, false, false, false, false, true, false, true, false, false, true, true, true, true, false, false, true, true, true, false, false, true, false, true, true, false);
          }
          pow_mod_crc(8896);
        }
      }
      pow_mod_crc(17792) + pow_mod_crc(8896);
    }
  }



  lemma lut_entry_139()
  ensures bits_of_int(lut[139] as int, 64)
      == pow_mod_crc(17920) + pow_mod_crc(8960)
  {
    calc {
      bits_of_int(lut[139] as int, 64);
      bits_of_int(17902623587072451612, 64);
      {
        lemma_bits_of_int_64_split(17902623587072451612);
      }
      bits_of_int(3741033500, 32) + bits_of_int(4168279372, 32);
      {
        unroll_bits_of_int_32_0xdefba41c();
        unroll_bits_of_int_32_0xf872e54c();
      }
      [false, false, true, true, true, false, false, false, false, false, true, false, false, true, false, true, true, true, false, true, true, true, true, true, false, true, true, true, true, false, true, true]+[false, false, true, true, false, false, true, false, true, false, true, false, false, true, true, true, false, true, false, false, true, true, true, false, false, false, false, true, true, true, true, true];
      {
        calc {
          [false, false, true, true, true, false, false, false, false, false, true, false, false, true, false, true, true, true, false, true, true, true, true, true, false, true, true, true, true, false, true, true];
          {
            pow_17887();
            of_pow(17920, true, true, false, true, true, true, true, false, true, true, true, true, true, false, true, true, true, false, true, false, false, true, false, false, false, false, false, true, true, true, false, false);
          }
          pow_mod_crc(17920);
        }
        calc {
          [false, false, true, true, false, false, true, false, true, false, true, false, false, true, true, true, false, true, false, false, true, true, true, false, false, false, false, true, true, true, true, true];
          {
            pow_8927();
            of_pow(8960, true, true, true, true, true, false, false, false, false, true, true, true, false, false, true, false, true, true, true, false, false, true, false, true, false, true, false, false, true, true, false, false);
          }
          pow_mod_crc(8960);
        }
      }
      pow_mod_crc(17920) + pow_mod_crc(8960);
    }
  }



  lemma lut_entry_140()
  ensures bits_of_int(lut[140] as int, 64)
      == pow_mod_crc(18048) + pow_mod_crc(9024)
  {
    calc {
      bits_of_int(lut[140] as int, 64);
      bits_of_int(11396802868116647569, 64);
      {
        lemma_bits_of_int_64_split(11396802868116647569);
      }
      bits_of_int(1631514257, 32) + bits_of_int(2653524947, 32);
      {
        unroll_bits_of_int_32_0x613eee91();
        unroll_bits_of_int_32_0x9e2993d3();
      }
      [true, false, false, false, true, false, false, true, false, true, true, true, false, true, true, true, false, true, true, true, true, true, false, false, true, false, false, false, false, true, true, false]+[true, true, false, false, true, false, true, true, true, true, false, false, true, false, false, true, true, false, false, true, false, true, false, false, false, true, true, true, true, false, false, true];
      {
        calc {
          [true, false, false, false, true, false, false, true, false, true, true, true, false, true, true, true, false, true, true, true, true, true, false, false, true, false, false, false, false, true, true, false];
          {
            pow_18015();
            of_pow(18048, false, true, true, false, false, false, false, true, false, false, true, true, true, true, true, false, true, true, true, false, true, true, true, false, true, false, false, true, false, false, false, true);
          }
          pow_mod_crc(18048);
        }
        calc {
          [true, true, false, false, true, false, true, true, true, true, false, false, true, false, false, true, true, false, false, true, false, true, false, false, false, true, true, true, true, false, false, true];
          {
            pow_8991();
            of_pow(9024, true, false, false, true, true, true, true, false, false, false, true, false, true, false, false, true, true, false, false, true, false, false, true, true, true, true, false, true, false, false, true, true);
          }
          pow_mod_crc(9024);
        }
      }
      pow_mod_crc(18048) + pow_mod_crc(9024);
    }
  }



  lemma lut_entry_141()
  ensures bits_of_int(lut[141] as int, 64)
      == pow_mod_crc(18176) + pow_mod_crc(9088)
  {
    calc {
      bits_of_int(lut[141] as int, 64);
      bits_of_int(2180280966884315412, 64);
      {
        lemma_bits_of_int_64_split(2180280966884315412);
      }
      bits_of_int(3719254292, 32) + bits_of_int(507636220, 32);
      {
        unroll_bits_of_int_32_0xddaf5114();
        unroll_bits_of_int_32_0x1e41e9fc();
      }
      [false, false, true, false, true, false, false, false, true, false, false, false, true, false, true, false, true, true, true, true, false, true, false, true, true, false, true, true, true, false, true, true]+[false, false, true, true, true, true, true, true, true, false, false, true, false, true, true, true, true, false, false, false, false, false, true, false, false, true, true, true, true, false, false, false];
      {
        calc {
          [false, false, true, false, true, false, false, false, true, false, false, false, true, false, true, false, true, true, true, true, false, true, false, true, true, false, true, true, true, false, true, true];
          {
            pow_18143();
            of_pow(18176, true, true, false, true, true, true, false, true, true, false, true, false, true, true, true, true, false, true, false, true, false, false, false, true, false, false, false, true, false, true, false, false);
          }
          pow_mod_crc(18176);
        }
        calc {
          [false, false, true, true, true, true, true, true, true, false, false, true, false, true, true, true, true, false, false, false, false, false, true, false, false, true, true, true, true, false, false, false];
          {
            pow_9055();
            of_pow(9088, false, false, false, true, true, true, true, false, false, true, false, false, false, false, false, true, true, true, true, false, true, false, false, true, true, true, true, true, true, true, false, false);
          }
          pow_mod_crc(9088);
        }
      }
      pow_mod_crc(18176) + pow_mod_crc(9088);
    }
  }



  lemma lut_entry_142()
  ensures bits_of_int(lut[142] as int, 64)
      == pow_mod_crc(18304) + pow_mod_crc(9152)
  {
    calc {
      bits_of_int(lut[142] as int, 64);
      bits_of_int(7776545834805350692, 64);
      {
        lemma_bits_of_int_64_split(7776545834805350692);
      }
      bits_of_int(522047780, 32) + bits_of_int(1810618172, 32);
      {
        unroll_bits_of_int_32_0x1f1dd124();
        unroll_bits_of_int_32_0x6bebd73c();
      }
      [false, false, true, false, false, true, false, false, true, false, false, false, true, false, true, true, true, false, true, true, true, false, false, false, true, true, true, true, true, false, false, false]+[false, false, true, true, true, true, false, false, true, true, true, false, true, false, true, true, true, true, false, true, false, true, true, true, true, true, false, true, false, true, true, false];
      {
        calc {
          [false, false, true, false, false, true, false, false, true, false, false, false, true, false, true, true, true, false, true, true, true, false, false, false, true, true, true, true, true, false, false, false];
          {
            pow_18271();
            of_pow(18304, false, false, false, true, true, true, true, true, false, false, false, true, true, true, false, true, true, true, false, true, false, false, false, true, false, false, true, false, false, true, false, false);
          }
          pow_mod_crc(18304);
        }
        calc {
          [false, false, true, true, true, true, false, false, true, true, true, false, true, false, true, true, true, true, false, true, false, true, true, true, true, true, false, true, false, true, true, false];
          {
            pow_9119();
            of_pow(9152, false, true, true, false, true, false, true, true, true, true, true, false, true, false, true, true, true, true, false, true, false, true, true, true, false, false, true, true, true, true, false, false);
          }
          pow_mod_crc(9152);
        }
      }
      pow_mod_crc(18304) + pow_mod_crc(9152);
    }
  }



  lemma lut_entry_143()
  ensures bits_of_int(lut[143] as int, 64)
      == pow_mod_crc(18432) + pow_mod_crc(9216)
  {
    calc {
      bits_of_int(lut[143] as int, 64);
      bits_of_int(9716767789848226721, 64);
      {
        lemma_bits_of_int_64_split(9716767789848226721);
      }
      bits_of_int(3202116513, 32) + bits_of_int(2262361298, 32);
      {
        unroll_bits_of_int_32_0xbedc6ba1();
        unroll_bits_of_int_32_0x86d8e4d2();
      }
      [true, false, false, false, false, true, false, true, true, true, false, true, false, true, true, false, false, false, true, true, true, false, true, true, false, true, true, true, true, true, false, true]+[false, true, false, false, true, false, true, true, false, false, true, false, false, true, true, true, false, false, false, true, true, false, true, true, false, true, true, false, false, false, false, true];
      {
        calc {
          [true, false, false, false, false, true, false, true, true, true, false, true, false, true, true, false, false, false, true, true, true, false, true, true, false, true, true, true, true, true, false, true];
          {
            pow_18399();
            of_pow(18432, true, false, true, true, true, true, true, false, true, true, false, true, true, true, false, false, false, true, true, false, true, false, true, true, true, false, true, false, false, false, false, true);
          }
          pow_mod_crc(18432);
        }
        calc {
          [false, true, false, false, true, false, true, true, false, false, true, false, false, true, true, true, false, false, false, true, true, false, true, true, false, true, true, false, false, false, false, true];
          {
            pow_9183();
            of_pow(9216, true, false, false, false, false, true, true, false, true, true, false, true, true, false, false, false, true, true, true, false, false, true, false, false, true, true, false, true, false, false, true, false);
          }
          pow_mod_crc(9216);
        }
      }
      pow_mod_crc(18432) + pow_mod_crc(9216);
    }
  }



  lemma lut_entry_144()
  ensures bits_of_int(lut[144] as int, 64)
      == pow_mod_crc(18560) + pow_mod_crc(9280)
  {
    calc {
      bits_of_int(lut[144] as int, 64);
      bits_of_int(7182838876700971006, 64);
      {
        lemma_bits_of_int_64_split(7182838876700971006);
      }
      bits_of_int(3969945598, 32) + bits_of_int(1672384998, 32);
      {
        unroll_bits_of_int_32_0xeca08ffe();
        unroll_bits_of_int_32_0x63ae91e6();
      }
      [false, true, true, true, true, true, true, true, true, true, true, true, false, false, false, true, false, false, false, false, false, true, false, true, false, false, true, true, false, true, true, true]+[false, true, true, false, false, true, true, true, true, false, false, false, true, false, false, true, false, true, true, true, false, true, false, true, true, true, false, false, false, true, true, false];
      {
        calc {
          [false, true, true, true, true, true, true, true, true, true, true, true, false, false, false, true, false, false, false, false, false, true, false, true, false, false, true, true, false, true, true, true];
          {
            pow_18527();
            of_pow(18560, true, true, true, false, true, true, false, false, true, false, true, false, false, false, false, false, true, false, false, false, true, true, true, true, true, true, true, true, true, true, true, false);
          }
          pow_mod_crc(18560);
        }
        calc {
          [false, true, true, false, false, true, true, true, true, false, false, false, true, false, false, true, false, true, true, true, false, true, false, true, true, true, false, false, false, true, true, false];
          {
            pow_9247();
            of_pow(9280, false, true, true, false, false, false, true, true, true, false, true, false, true, true, true, false, true, false, false, true, false, false, false, true, true, true, true, false, false, true, true, false);
          }
          pow_mod_crc(9280);
        }
      }
      pow_mod_crc(18560) + pow_mod_crc(9280);
    }
  }



  lemma lut_entry_145()
  ensures bits_of_int(lut[145] as int, 64)
      == pow_mod_crc(18688) + pow_mod_crc(9344)
  {
    calc {
      bits_of_int(lut[145] as int, 64);
      bits_of_int(7285656014213548149, 64);
      {
        lemma_bits_of_int_64_split(7285656014213548149);
      }
      bits_of_int(987957365, 32) + bits_of_int(1696323979, 32);
      {
        unroll_bits_of_int_32_0x3ae30875();
        unroll_bits_of_int_32_0x651bd98b();
      }
      [true, false, true, false, true, true, true, false, false, false, false, true, false, false, false, false, true, true, false, false, false, true, true, true, false, true, false, true, true, true, false, false]+[true, true, false, true, false, false, false, true, true, false, false, true, true, false, true, true, true, true, false, true, true, false, false, false, true, false, true, false, false, true, true, false];
      {
        calc {
          [true, false, true, false, true, true, true, false, false, false, false, true, false, false, false, false, true, true, false, false, false, true, true, true, false, true, false, true, true, true, false, false];
          {
            pow_18655();
            of_pow(18688, false, false, true, true, true, false, true, false, true, true, true, false, false, false, true, true, false, false, false, false, true, false, false, false, false, true, true, true, false, true, false, true);
          }
          pow_mod_crc(18688);
        }
        calc {
          [true, true, false, true, false, false, false, true, true, false, false, true, true, false, true, true, true, true, false, true, true, false, false, false, true, false, true, false, false, true, true, false];
          {
            pow_9311();
            of_pow(9344, false, true, true, false, false, true, false, true, false, false, false, true, true, false, true, true, true, true, false, true, true, false, false, true, true, false, false, false, true, false, true, true);
          }
          pow_mod_crc(9344);
        }
      }
      pow_mod_crc(18688) + pow_mod_crc(9344);
    }
  }



  lemma lut_entry_146()
  ensures bits_of_int(lut[146] as int, 64)
      == pow_mod_crc(18816) + pow_mod_crc(9408)
  {
    calc {
      bits_of_int(lut[146] as int, 64);
      bits_of_int(17927100009460879978, 64);
      {
        lemma_bits_of_int_64_split(17927100009460879978);
      }
      bits_of_int(215044714, 32) + bits_of_int(4173978234, 32);
      {
        unroll_bits_of_int_32_0x0cd1526a();
        unroll_bits_of_int_32_0xf8c9da7a();
      }
      [false, true, false, true, false, true, true, false, false, true, false, false, true, false, true, false, true, false, false, false, true, false, true, true, false, false, true, true, false, false, false, false]+[false, true, false, true, true, true, true, false, false, true, false, true, true, false, true, true, true, false, false, true, false, false, true, true, false, false, false, true, true, true, true, true];
      {
        calc {
          [false, true, false, true, false, true, true, false, false, true, false, false, true, false, true, false, true, false, false, false, true, false, true, true, false, false, true, true, false, false, false, false];
          {
            pow_18783();
            of_pow(18816, false, false, false, false, true, true, false, false, true, true, false, true, false, false, false, true, false, true, false, true, false, false, true, false, false, true, true, false, true, false, true, false);
          }
          pow_mod_crc(18816);
        }
        calc {
          [false, true, false, true, true, true, true, false, false, true, false, true, true, false, true, true, true, false, false, true, false, false, true, true, false, false, false, true, true, true, true, true];
          {
            pow_9375();
            of_pow(9408, true, true, true, true, true, false, false, false, true, true, false, false, true, false, false, true, true, true, false, true, true, false, true, false, false, true, true, true, true, false, true, false);
          }
          pow_mod_crc(9408);
        }
      }
      pow_mod_crc(18816) + pow_mod_crc(9408);
    }
  }



  lemma lut_entry_147()
  ensures bits_of_int(lut[147] as int, 64)
      == pow_mod_crc(18944) + pow_mod_crc(9472)
  {
    calc {
      bits_of_int(lut[147] as int, 64);
      bits_of_int(6609298245898407684, 64);
      {
        lemma_bits_of_int_64_split(6609298245898407684);
      }
      bits_of_int(2976059140, 32) + bits_of_int(1538847164, 32);
      {
        unroll_bits_of_int_32_0xb1630f04();
        unroll_bits_of_int_32_0x5bb8f1bc();
      }
      [false, false, true, false, false, false, false, false, true, true, true, true, false, false, false, false, true, true, false, false, false, true, true, false, true, false, false, false, true, true, false, true]+[false, false, true, true, true, true, false, true, true, false, false, false, true, true, true, true, false, false, false, true, true, true, false, true, true, true, false, true, true, false, true, false];
      {
        calc {
          [false, false, true, false, false, false, false, false, true, true, true, true, false, false, false, false, true, true, false, false, false, true, true, false, true, false, false, false, true, true, false, true];
          {
            pow_18911();
            of_pow(18944, true, false, true, true, false, false, false, true, false, true, true, false, false, false, true, true, false, false, false, false, true, true, true, true, false, false, false, false, false, true, false, false);
          }
          pow_mod_crc(18944);
        }
        calc {
          [false, false, true, true, true, true, false, true, true, false, false, false, true, true, true, true, false, false, false, true, true, true, false, true, true, true, false, true, true, false, true, false];
          {
            pow_9439();
            of_pow(9472, false, true, false, true, true, false, true, true, true, false, true, true, true, false, false, false, true, true, true, true, false, false, false, true, true, false, true, true, true, true, false, false);
          }
          pow_mod_crc(9472);
        }
      }
      pow_mod_crc(18944) + pow_mod_crc(9472);
    }
  }



  lemma lut_entry_148()
  ensures bits_of_int(lut[148] as int, 64)
      == pow_mod_crc(19072) + pow_mod_crc(9536)
  {
    calc {
      bits_of_int(lut[148] as int, 64);
      bits_of_int(10689884986519531899, 64);
      {
        lemma_bits_of_int_64_split(10689884986519531899);
      }
      bits_of_int(4282855803, 32) + bits_of_int(2488932801, 32);
      {
        unroll_bits_of_int_32_0xff47317b();
        unroll_bits_of_int_32_0x945a19c1();
      }
      [true, true, false, true, true, true, true, false, true, false, false, false, true, true, false, false, true, true, true, false, false, false, true, false, true, true, true, true, true, true, true, true]+[true, false, false, false, false, false, true, true, true, false, false, true, true, false, false, false, false, true, false, true, true, false, true, false, false, false, true, false, true, false, false, true];
      {
        calc {
          [true, true, false, true, true, true, true, false, true, false, false, false, true, true, false, false, true, true, true, false, false, false, true, false, true, true, true, true, true, true, true, true];
          {
            pow_19039();
            of_pow(19072, true, true, true, true, true, true, true, true, false, true, false, false, false, true, true, true, false, false, true, true, false, false, false, true, false, true, true, true, true, false, true, true);
          }
          pow_mod_crc(19072);
        }
        calc {
          [true, false, false, false, false, false, true, true, true, false, false, true, true, false, false, false, false, true, false, true, true, false, true, false, false, false, true, false, true, false, false, true];
          {
            pow_9503();
            of_pow(9536, true, false, false, true, false, true, false, false, false, true, false, true, true, false, true, false, false, false, false, true, true, false, false, true, true, true, false, false, false, false, false, true);
          }
          pow_mod_crc(9536);
        }
      }
      pow_mod_crc(19072) + pow_mod_crc(9536);
    }
  }



  lemma lut_entry_149()
  ensures bits_of_int(lut[149] as int, 64)
      == pow_mod_crc(19200) + pow_mod_crc(9600)
  {
    calc {
      bits_of_int(lut[149] as int, 64);
      bits_of_int(12182186942091470855, 64);
      {
        lemma_bits_of_int_64_split(12182186942091470855);
      }
      bits_of_int(3603146759, 32) + bits_of_int(2836386426, 32);
      {
        unroll_bits_of_int_32_0xd6c3a807();
        unroll_bits_of_int_32_0xa90fd27a();
      }
      [true, true, true, false, false, false, false, false, false, false, false, true, false, true, false, true, true, true, false, false, false, false, true, true, false, true, true, false, true, false, true, true]+[false, true, false, true, true, true, true, false, false, true, false, false, true, false, true, true, true, true, true, true, false, false, false, false, true, false, false, true, false, true, false, true];
      {
        calc {
          [true, true, true, false, false, false, false, false, false, false, false, true, false, true, false, true, true, true, false, false, false, false, true, true, false, true, true, false, true, false, true, true];
          {
            pow_19167();
            of_pow(19200, true, true, false, true, false, true, true, false, true, true, false, false, false, false, true, true, true, false, true, false, true, false, false, false, false, false, false, false, false, true, true, true);
          }
          pow_mod_crc(19200);
        }
        calc {
          [false, true, false, true, true, true, true, false, false, true, false, false, true, false, true, true, true, true, true, true, false, false, false, false, true, false, false, true, false, true, false, true];
          {
            pow_9567();
            of_pow(9600, true, false, true, false, true, false, false, true, false, false, false, false, true, true, true, true, true, true, false, true, false, false, true, false, false, true, true, true, true, false, true, false);
          }
          pow_mod_crc(9600);
        }
      }
      pow_mod_crc(19200) + pow_mod_crc(9600);
    }
  }



  lemma lut_entry_150()
  ensures bits_of_int(lut[150] as int, 64)
      == pow_mod_crc(19328) + pow_mod_crc(9664)
  {
    calc {
      bits_of_int(lut[150] as int, 64);
      bits_of_int(17186320807290700256, 64);
      {
        lemma_bits_of_int_64_split(17186320807290700256);
      }
      bits_of_int(2591523296, 32) + bits_of_int(4001502135, 32);
      {
        unroll_bits_of_int_32_0x9a7781e0();
        unroll_bits_of_int_32_0xee8213b7();
      }
      [false, false, false, false, false, true, true, true, true, false, false, false, false, false, false, true, true, true, true, false, true, true, true, false, false, true, false, true, true, false, false, true]+[true, true, true, false, true, true, false, true, true, true, false, false, true, false, false, false, false, true, false, false, false, false, false, true, false, true, true, true, false, true, true, true];
      {
        calc {
          [false, false, false, false, false, true, true, true, true, false, false, false, false, false, false, true, true, true, true, false, true, true, true, false, false, true, false, true, true, false, false, true];
          {
            pow_19295();
            of_pow(19328, true, false, false, true, true, false, true, false, false, true, true, true, false, true, true, true, true, false, false, false, false, false, false, true, true, true, true, false, false, false, false, false);
          }
          pow_mod_crc(19328);
        }
        calc {
          [true, true, true, false, true, true, false, true, true, true, false, false, true, false, false, false, false, true, false, false, false, false, false, true, false, true, true, true, false, true, true, true];
          {
            pow_9631();
            of_pow(9664, true, true, true, false, true, true, true, false, true, false, false, false, false, false, true, false, false, false, false, true, false, false, true, true, true, false, true, true, false, true, true, true);
          }
          pow_mod_crc(9664);
        }
      }
      pow_mod_crc(19328) + pow_mod_crc(9664);
    }
  }



  lemma lut_entry_151()
  ensures bits_of_int(lut[151] as int, 64)
      == pow_mod_crc(19456) + pow_mod_crc(9728)
  {
    calc {
      bits_of_int(lut[151] as int, 64);
      bits_of_int(12947575675955484649, 64);
      {
        lemma_bits_of_int_64_split(12947575675955484649);
      }
      bits_of_int(1674614761, 32) + bits_of_int(3014592378, 32);
      {
        unroll_bits_of_int_32_0x63d097e9();
        unroll_bits_of_int_32_0xb3af077a();
      }
      [true, false, false, true, false, true, true, true, true, true, true, false, true, false, false, true, false, false, false, false, true, false, true, true, true, true, false, false, false, true, true, false]+[false, true, false, true, true, true, true, false, true, true, true, false, false, false, false, false, true, true, true, true, false, true, false, true, true, true, false, false, true, true, false, true];
      {
        calc {
          [true, false, false, true, false, true, true, true, true, true, true, false, true, false, false, true, false, false, false, false, true, false, true, true, true, true, false, false, false, true, true, false];
          {
            pow_19423();
            of_pow(19456, false, true, true, false, false, false, true, true, true, true, false, true, false, false, false, false, true, false, false, true, false, true, true, true, true, true, true, false, true, false, false, true);
          }
          pow_mod_crc(19456);
        }
        calc {
          [false, true, false, true, true, true, true, false, true, true, true, false, false, false, false, false, true, true, true, true, false, true, false, true, true, true, false, false, true, true, false, true];
          {
            pow_9695();
            of_pow(9728, true, false, true, true, false, false, true, true, true, false, true, false, true, true, true, true, false, false, false, false, false, true, true, true, false, true, true, true, true, false, true, false);
          }
          pow_mod_crc(9728);
        }
      }
      pow_mod_crc(19456) + pow_mod_crc(9728);
    }
  }



  lemma lut_entry_152()
  ensures bits_of_int(lut[152] as int, 64)
      == pow_mod_crc(19584) + pow_mod_crc(9792)
  {
    calc {
      bits_of_int(lut[152] as int, 64);
      bits_of_int(10626276061806139231, 64);
      {
        lemma_bits_of_int_64_split(10626276061806139231);
      }
      bits_of_int(489756511, 32) + bits_of_int(2474122695, 32);
      {
        unroll_bits_of_int_32_0x1d31175f();
        unroll_bits_of_int_32_0x93781dc7();
      }
      [true, true, true, true, true, false, true, false, true, true, true, false, true, false, false, false, true, false, false, false, true, true, false, false, true, false, true, true, true, false, false, false]+[true, true, true, false, false, false, true, true, true, false, true, true, true, false, false, false, false, false, false, true, true, true, true, false, true, true, false, false, true, false, false, true];
      {
        calc {
          [true, true, true, true, true, false, true, false, true, true, true, false, true, false, false, false, true, false, false, false, true, true, false, false, true, false, true, true, true, false, false, false];
          {
            pow_19551();
            of_pow(19584, false, false, false, true, true, true, false, true, false, false, true, true, false, false, false, true, false, false, false, true, false, true, true, true, false, true, false, true, true, true, true, true);
          }
          pow_mod_crc(19584);
        }
        calc {
          [true, true, true, false, false, false, true, true, true, false, true, true, true, false, false, false, false, false, false, true, true, true, true, false, true, true, false, false, true, false, false, true];
          {
            pow_9759();
            of_pow(9792, true, false, false, true, false, false, true, true, false, true, true, true, true, false, false, false, false, false, false, true, true, true, false, true, true, true, false, false, false, true, true, true);
          }
          pow_mod_crc(9792);
        }
      }
      pow_mod_crc(19584) + pow_mod_crc(9792);
    }
  }



  lemma lut_entry_153()
  ensures bits_of_int(lut[153] as int, 64)
      == pow_mod_crc(19712) + pow_mod_crc(9856)
  {
    calc {
      bits_of_int(lut[153] as int, 64);
      bits_of_int(5297596017538704750, 64);
      {
        lemma_bits_of_int_64_split(5297596017538704750);
      }
      bits_of_int(2498438510, 32) + bits_of_int(1233442690, 32);
      {
        unroll_bits_of_int_32_0x94eb256e();
        unroll_bits_of_int_32_0x4984d782();
      }
      [false, true, true, true, false, true, true, false, true, false, true, false, false, true, false, false, true, true, false, true, false, true, true, true, false, false, true, false, true, false, false, true]+[false, true, false, false, false, false, false, true, true, true, true, false, true, false, true, true, false, false, true, false, false, false, false, true, true, false, false, true, false, false, true, false];
      {
        calc {
          [false, true, true, true, false, true, true, false, true, false, true, false, false, true, false, false, true, true, false, true, false, true, true, true, false, false, true, false, true, false, false, true];
          {
            pow_19679();
            of_pow(19712, true, false, false, true, false, true, false, false, true, true, true, false, true, false, true, true, false, false, true, false, false, true, false, true, false, true, true, false, true, true, true, false);
          }
          pow_mod_crc(19712);
        }
        calc {
          [false, true, false, false, false, false, false, true, true, true, true, false, true, false, true, true, false, false, true, false, false, false, false, true, true, false, false, true, false, false, true, false];
          {
            pow_9823();
            of_pow(9856, false, true, false, false, true, false, false, true, true, false, false, false, false, true, false, false, true, true, false, true, false, true, true, true, true, false, false, false, false, false, true, false);
          }
          pow_mod_crc(9856);
        }
      }
      pow_mod_crc(19712) + pow_mod_crc(9856);
    }
  }



  lemma lut_entry_154()
  ensures bits_of_int(lut[154] as int, 64)
      == pow_mod_crc(19840) + pow_mod_crc(9920)
  {
    calc {
      bits_of_int(lut[154] as int, 64);
      bits_of_int(14755096095433967177, 64);
      {
        lemma_bits_of_int_64_split(14755096095433967177);
      }
      bits_of_int(320357961, 32) + bits_of_int(3435438521, 32);
      {
        unroll_bits_of_int_32_0x13184649();
        unroll_bits_of_int_32_0xccc4a1b9();
      }
      [true, false, false, true, false, false, true, false, false, true, true, false, false, false, true, false, false, false, false, true, true, false, false, false, true, true, false, false, true, false, false, false]+[true, false, false, true, true, true, false, true, true, false, false, false, false, true, false, true, false, false, true, false, false, false, true, true, false, false, true, true, false, false, true, true];
      {
        calc {
          [true, false, false, true, false, false, true, false, false, true, true, false, false, false, true, false, false, false, false, true, true, false, false, false, true, true, false, false, true, false, false, false];
          {
            pow_19807();
            of_pow(19840, false, false, false, true, false, false, true, true, false, false, false, true, true, false, false, false, false, true, false, false, false, true, true, false, false, true, false, false, true, false, false, true);
          }
          pow_mod_crc(19840);
        }
        calc {
          [true, false, false, true, true, true, false, true, true, false, false, false, false, true, false, true, false, false, true, false, false, false, true, true, false, false, true, true, false, false, true, true];
          {
            pow_9887();
            of_pow(9920, true, true, false, false, true, true, false, false, true, true, false, false, false, true, false, false, true, false, true, false, false, false, false, true, true, false, true, true, true, false, false, true);
          }
          pow_mod_crc(9920);
        }
      }
      pow_mod_crc(19840) + pow_mod_crc(9920);
    }
  }



  lemma lut_entry_155()
  ensures bits_of_int(lut[155] as int, 64)
      == pow_mod_crc(19968) + pow_mod_crc(9984)
  {
    calc {
      bits_of_int(lut[155] as int, 64);
      bits_of_int(14586864164433034640, 64);
      {
        lemma_bits_of_int_64_split(14586864164433034640);
      }
      bits_of_int(1273494928, 32) + bits_of_int(3396268972, 32);
      {
        unroll_bits_of_int_32_0x4be7fd90();
        unroll_bits_of_int_32_0xca6ef3ac();
      }
      [false, false, false, false, true, false, false, true, true, false, true, true, true, true, true, true, true, true, true, false, false, true, true, true, true, true, false, true, false, false, true, false]+[false, false, true, true, false, true, false, true, true, true, false, false, true, true, true, true, false, true, true, true, false, true, true, false, false, true, false, true, false, false, true, true];
      {
        calc {
          [false, false, false, false, true, false, false, true, true, false, true, true, true, true, true, true, true, true, true, false, false, true, true, true, true, true, false, true, false, false, true, false];
          {
            pow_19935();
            of_pow(19968, false, true, false, false, true, false, true, true, true, true, true, false, false, true, true, true, true, true, true, true, true, true, false, true, true, false, false, true, false, false, false, false);
          }
          pow_mod_crc(19968);
        }
        calc {
          [false, false, true, true, false, true, false, true, true, true, false, false, true, true, true, true, false, true, true, true, false, true, true, false, false, true, false, true, false, false, true, true];
          {
            pow_9951();
            of_pow(9984, true, true, false, false, true, false, true, false, false, true, true, false, true, true, true, false, true, true, true, true, false, false, true, true, true, false, true, false, true, true, false, false);
          }
          pow_mod_crc(9984);
        }
      }
      pow_mod_crc(19968) + pow_mod_crc(9984);
    }
  }



  lemma lut_entry_156()
  ensures bits_of_int(lut[156] as int, 64)
      == pow_mod_crc(20096) + pow_mod_crc(10048)
  {
    calc {
      bits_of_int(lut[156] as int, 64);
      bits_of_int(11728175461083913572, 64);
      {
        lemma_bits_of_int_64_split(11728175461083913572);
      }
      bits_of_int(2103188836, 32) + bits_of_int(2730678641, 32);
      {
        unroll_bits_of_int_32_0x7d5c1d64();
        unroll_bits_of_int_32_0xa2c2d971();
      }
      [false, false, true, false, false, true, true, false, true, false, true, true, true, false, false, false, false, false, true, true, true, false, true, false, true, false, true, true, true, true, true, false]+[true, false, false, false, true, true, true, false, true, false, false, true, true, false, true, true, false, true, false, false, false, false, true, true, false, true, false, false, false, true, false, true];
      {
        calc {
          [false, false, true, false, false, true, true, false, true, false, true, true, true, false, false, false, false, false, true, true, true, false, true, false, true, false, true, true, true, true, true, false];
          {
            pow_20063();
            of_pow(20096, false, true, true, true, true, true, false, true, false, true, false, true, true, true, false, false, false, false, false, true, true, true, false, true, false, true, true, false, false, true, false, false);
          }
          pow_mod_crc(20096);
        }
        calc {
          [true, false, false, false, true, true, true, false, true, false, false, true, true, false, true, true, false, true, false, false, false, false, true, true, false, true, false, false, false, true, false, true];
          {
            pow_10015();
            of_pow(10048, true, false, true, false, false, false, true, false, true, true, false, false, false, false, true, false, true, true, false, true, true, false, false, true, false, true, true, true, false, false, false, true);
          }
          pow_mod_crc(10048);
        }
      }
      pow_mod_crc(20096) + pow_mod_crc(10048);
    }
  }



  lemma lut_entry_157()
  ensures bits_of_int(lut[157] as int, 64)
      == pow_mod_crc(20224) + pow_mod_crc(10112)
  {
    calc {
      bits_of_int(lut[157] as int, 64);
      bits_of_int(2543983099507279258, 64);
      {
        lemma_bits_of_int_64_split(2543983099507279258);
      }
      bits_of_int(2159707546, 32) + bits_of_int(592317222, 32);
      {
        unroll_bits_of_int_32_0x80ba859a();
        unroll_bits_of_int_32_0x234e0b26();
      }
      [false, true, false, true, true, false, false, true, true, false, true, false, false, false, false, true, false, true, false, true, true, true, false, true, false, false, false, false, false, false, false, true]+[false, true, true, false, false, true, false, false, true, true, false, true, false, false, false, false, false, true, true, true, false, false, true, false, true, true, false, false, false, true, false, false];
      {
        calc {
          [false, true, false, true, true, false, false, true, true, false, true, false, false, false, false, true, false, true, false, true, true, true, false, true, false, false, false, false, false, false, false, true];
          {
            pow_20191();
            of_pow(20224, true, false, false, false, false, false, false, false, true, false, true, true, true, false, true, false, true, false, false, false, false, true, false, true, true, false, false, true, true, false, true, false);
          }
          pow_mod_crc(20224);
        }
        calc {
          [false, true, true, false, false, true, false, false, true, true, false, true, false, false, false, false, false, true, true, true, false, false, true, false, true, true, false, false, false, true, false, false];
          {
            pow_10079();
            of_pow(10112, false, false, true, false, false, false, true, true, false, true, false, false, true, true, true, false, false, false, false, false, true, false, true, true, false, false, true, false, false, true, true, false);
          }
          pow_mod_crc(10112);
        }
      }
      pow_mod_crc(20224) + pow_mod_crc(10112);
    }
  }



  lemma lut_entry_158()
  ensures bits_of_int(lut[158] as int, 64)
      == pow_mod_crc(20352) + pow_mod_crc(10176)
  {
    calc {
      bits_of_int(lut[158] as int, 64);
      bits_of_int(2066382924872077769, 64);
      {
        lemma_bits_of_int_64_split(2066382924872077769);
      }
      bits_of_int(1861145033, 32) + bits_of_int(481117266, 32);
      {
        unroll_bits_of_int_32_0x6eeed1c9();
        unroll_bits_of_int_32_0x1cad4452();
      }
      [true, false, false, true, false, false, true, true, true, false, false, false, true, false, true, true, false, true, true, true, false, true, true, true, false, true, true, true, false, true, true, false]+[false, true, false, false, true, false, true, false, false, false, true, false, false, false, true, false, true, false, true, true, false, true, false, true, false, false, true, true, true, false, false, false];
      {
        calc {
          [true, false, false, true, false, false, true, true, true, false, false, false, true, false, true, true, false, true, true, true, false, true, true, true, false, true, true, true, false, true, true, false];
          {
            pow_20319();
            of_pow(20352, false, true, true, false, true, true, true, false, true, true, true, false, true, true, true, false, true, true, false, true, false, false, false, true, true, true, false, false, true, false, false, true);
          }
          pow_mod_crc(20352);
        }
        calc {
          [false, true, false, false, true, false, true, false, false, false, true, false, false, false, true, false, true, false, true, true, false, true, false, true, false, false, true, true, true, false, false, false];
          {
            pow_10143();
            of_pow(10176, false, false, false, true, true, true, false, false, true, false, true, false, true, true, false, true, false, true, false, false, false, true, false, false, false, true, false, true, false, false, true, false);
          }
          pow_mod_crc(10176);
        }
      }
      pow_mod_crc(20352) + pow_mod_crc(10176);
    }
  }



  lemma lut_entry_159()
  ensures bits_of_int(lut[159] as int, 64)
      == pow_mod_crc(20480) + pow_mod_crc(10240)
  {
    calc {
      bits_of_int(lut[159] as int, 64);
      bits_of_int(15953662734609119647, 64);
      {
        lemma_bits_of_int_64_split(15953662734609119647);
      }
      bits_of_int(583235999, 32) + bits_of_int(3714501563, 32);
      {
        unroll_bits_of_int_32_0x22c3799f();
        unroll_bits_of_int_32_0xdd66cbbb();
      }
      [true, true, true, true, true, false, false, true, true, false, false, true, true, true, true, false, true, true, false, false, false, false, true, true, false, true, false, false, false, true, false, false]+[true, true, false, true, true, true, false, true, true, true, false, true, false, false, true, true, false, true, true, false, false, true, true, false, true, false, true, true, true, false, true, true];
      {
        calc {
          [true, true, true, true, true, false, false, true, true, false, false, true, true, true, true, false, true, true, false, false, false, false, true, true, false, true, false, false, false, true, false, false];
          {
            pow_20447();
            of_pow(20480, false, false, true, false, false, false, true, false, true, true, false, false, false, false, true, true, false, true, true, true, true, false, false, true, true, false, false, true, true, true, true, true);
          }
          pow_mod_crc(20480);
        }
        calc {
          [true, true, false, true, true, true, false, true, true, true, false, true, false, false, true, true, false, true, true, false, false, true, true, false, true, false, true, true, true, false, true, true];
          {
            pow_10207();
            of_pow(10240, true, true, false, true, true, true, false, true, false, true, true, false, false, true, true, false, true, true, false, false, true, false, true, true, true, false, true, true, true, false, true, true);
          }
          pow_mod_crc(10240);
        }
      }
      pow_mod_crc(20480) + pow_mod_crc(10240);
    }
  }



  lemma lut_entry_160()
  ensures bits_of_int(lut[160] as int, 64)
      == pow_mod_crc(20608) + pow_mod_crc(10304)
  {
    calc {
      bits_of_int(lut[160] as int, 64);
      bits_of_int(8399818044375614840, 64);
      {
        lemma_bits_of_int_64_split(8399818044375614840);
      }
      bits_of_int(3639395704, 32) + bits_of_int(1955735041, 32);
      {
        unroll_bits_of_int_32_0xd8ecc578();
        unroll_bits_of_int_32_0x74922601();
      }
      [false, false, false, true, true, true, true, false, true, false, true, false, false, false, true, true, false, false, true, true, false, true, true, true, false, false, false, true, true, false, true, true]+[true, false, false, false, false, false, false, false, false, true, true, false, false, true, false, false, false, true, false, false, true, false, false, true, false, false, true, false, true, true, true, false];
      {
        calc {
          [false, false, false, true, true, true, true, false, true, false, true, false, false, false, true, true, false, false, true, true, false, true, true, true, false, false, false, true, true, false, true, true];
          {
            pow_20575();
            of_pow(20608, true, true, false, true, true, false, false, false, true, true, true, false, true, true, false, false, true, true, false, false, false, true, false, true, false, true, true, true, true, false, false, false);
          }
          pow_mod_crc(20608);
        }
        calc {
          [true, false, false, false, false, false, false, false, false, true, true, false, false, true, false, false, false, true, false, false, true, false, false, true, false, false, true, false, true, true, true, false];
          {
            pow_10271();
            of_pow(10304, false, true, true, true, false, true, false, false, true, false, false, true, false, false, true, false, false, false, true, false, false, true, true, false, false, false, false, false, false, false, false, true);
          }
          pow_mod_crc(10304);
        }
      }
      pow_mod_crc(20608) + pow_mod_crc(10304);
    }
  }



  lemma lut_entry_161()
  ensures bits_of_int(lut[161] as int, 64)
      == pow_mod_crc(20736) + pow_mod_crc(10368)
  {
    calc {
      bits_of_int(lut[161] as int, 64);
      bits_of_int(5014553034683243156, 64);
      {
        lemma_bits_of_int_64_split(5014553034683243156);
      }
      bits_of_int(3014056596, 32) + bits_of_int(1167541610, 32);
      {
        unroll_bits_of_int_32_0xb3a6da94();
        unroll_bits_of_int_32_0x4597456a();
      }
      [false, false, true, false, true, false, false, true, false, true, false, true, true, false, true, true, false, true, true, false, false, true, false, true, true, true, false, false, true, true, false, true]+[false, true, false, true, false, true, true, false, true, false, true, false, false, false, true, false, true, true, true, false, true, false, false, true, true, false, true, false, false, false, true, false];
      {
        calc {
          [false, false, true, false, true, false, false, true, false, true, false, true, true, false, true, true, false, true, true, false, false, true, false, true, true, true, false, false, true, true, false, true];
          {
            pow_20703();
            of_pow(20736, true, false, true, true, false, false, true, true, true, false, true, false, false, true, true, false, true, true, false, true, true, false, true, false, true, false, false, true, false, true, false, false);
          }
          pow_mod_crc(20736);
        }
        calc {
          [false, true, false, true, false, true, true, false, true, false, true, false, false, false, true, false, true, true, true, false, true, false, false, true, true, false, true, false, false, false, true, false];
          {
            pow_10335();
            of_pow(10368, false, true, false, false, false, true, false, true, true, false, false, true, false, true, true, true, false, true, false, false, false, true, false, true, false, true, true, false, true, false, true, false);
          }
          pow_mod_crc(10368);
        }
      }
      pow_mod_crc(20736) + pow_mod_crc(10368);
    }
  }



  lemma lut_entry_162()
  ensures bits_of_int(lut[162] as int, 64)
      == pow_mod_crc(20864) + pow_mod_crc(10432)
  {
    calc {
      bits_of_int(lut[162] as int, 64);
      bits_of_int(14222225424569152510, 64);
      {
        lemma_bits_of_int_64_split(14222225424569152510);
      }
      bits_of_int(3405329406, 32) + bits_of_int(3311369899, 32);
      {
        unroll_bits_of_int_32_0xcaf933fe();
        unroll_bits_of_int_32_0xc55f7eab();
      }
      [false, true, true, true, true, true, true, true, true, true, false, false, true, true, false, false, true, false, false, true, true, true, true, true, false, true, false, true, false, false, true, true]+[true, true, false, true, false, true, false, true, false, true, true, true, true, true, true, false, true, true, true, true, true, false, true, false, true, false, true, false, false, false, true, true];
      {
        calc {
          [false, true, true, true, true, true, true, true, true, true, false, false, true, true, false, false, true, false, false, true, true, true, true, true, false, true, false, true, false, false, true, true];
          {
            pow_20831();
            of_pow(20864, true, true, false, false, true, false, true, false, true, true, true, true, true, false, false, true, false, false, true, true, false, false, true, true, true, true, true, true, true, true, true, false);
          }
          pow_mod_crc(20864);
        }
        calc {
          [true, true, false, true, false, true, false, true, false, true, true, true, true, true, true, false, true, true, true, true, true, false, true, false, true, false, true, false, false, false, true, true];
          {
            pow_10399();
            of_pow(10432, true, true, false, false, false, true, false, true, false, true, false, true, true, true, true, true, false, true, true, true, true, true, true, false, true, false, true, false, true, false, true, true);
          }
          pow_mod_crc(10432);
        }
      }
      pow_mod_crc(20864) + pow_mod_crc(10432);
    }
  }



  lemma lut_entry_163()
  ensures bits_of_int(lut[163] as int, 64)
      == pow_mod_crc(20992) + pow_mod_crc(10496)
  {
    calc {
      bits_of_int(lut[163] as int, 64);
      bits_of_int(16853189660673813214, 64);
      {
        lemma_bits_of_int_64_split(16853189660673813214);
      }
      bits_of_int(1354738398, 32) + bits_of_int(3923938996, 32);
      {
        unroll_bits_of_int_32_0x50bfaade();
        unroll_bits_of_int_32_0xe9e28eb4();
      }
      [false, true, true, true, true, false, true, true, false, true, false, true, false, true, false, true, true, true, true, true, true, true, false, true, false, false, false, false, true, false, true, false]+[false, false, true, false, true, true, false, true, false, true, true, true, false, false, false, true, false, true, false, false, false, true, true, true, true, false, false, true, false, true, true, true];
      {
        calc {
          [false, true, true, true, true, false, true, true, false, true, false, true, false, true, false, true, true, true, true, true, true, true, false, true, false, false, false, false, true, false, true, false];
          {
            pow_20959();
            of_pow(20992, false, true, false, true, false, false, false, false, true, false, true, true, true, true, true, true, true, false, true, false, true, false, true, false, true, true, false, true, true, true, true, false);
          }
          pow_mod_crc(20992);
        }
        calc {
          [false, false, true, false, true, true, false, true, false, true, true, true, false, false, false, true, false, true, false, false, false, true, true, true, true, false, false, true, false, true, true, true];
          {
            pow_10463();
            of_pow(10496, true, true, true, false, true, false, false, true, true, true, true, false, false, false, true, false, true, false, false, false, true, true, true, false, true, false, true, true, false, true, false, false);
          }
          pow_mod_crc(10496);
        }
      }
      pow_mod_crc(20992) + pow_mod_crc(10496);
    }
  }



  lemma lut_entry_164()
  ensures bits_of_int(lut[164] as int, 64)
      == pow_mod_crc(21120) + pow_mod_crc(10560)
  {
    calc {
      bits_of_int(lut[164] as int, 64);
      bits_of_int(11643532546393575847, 64);
      {
        lemma_bits_of_int_64_split(11643532546393575847);
      }
      bits_of_int(779948455, 32) + bits_of_int(2710971177, 32);
      {
        unroll_bits_of_int_32_0x2e7d11a7();
        unroll_bits_of_int_32_0xa1962329();
      }
      [true, true, true, false, false, true, false, true, true, false, false, false, true, false, false, false, true, false, true, true, true, true, true, false, false, true, true, true, false, true, false, false]+[true, false, false, true, false, true, false, false, true, true, false, false, false, true, false, false, false, true, true, false, true, false, false, true, true, false, false, false, false, true, false, true];
      {
        calc {
          [true, true, true, false, false, true, false, true, true, false, false, false, true, false, false, false, true, false, true, true, true, true, true, false, false, true, true, true, false, true, false, false];
          {
            pow_21087();
            of_pow(21120, false, false, true, false, true, true, true, false, false, true, true, true, true, true, false, true, false, false, false, true, false, false, false, true, true, false, true, false, false, true, true, true);
          }
          pow_mod_crc(21120);
        }
        calc {
          [true, false, false, true, false, true, false, false, true, true, false, false, false, true, false, false, false, true, true, false, true, false, false, true, true, false, false, false, false, true, false, true];
          {
            pow_10527();
            of_pow(10560, true, false, true, false, false, false, false, true, true, false, false, true, false, true, true, false, false, false, true, false, false, false, true, true, false, false, true, false, true, false, false, true);
          }
          pow_mod_crc(10560);
        }
      }
      pow_mod_crc(21120) + pow_mod_crc(10560);
    }
  }



  lemma lut_entry_165()
  ensures bits_of_int(lut[165] as int, 64)
      == pow_mod_crc(21248) + pow_mod_crc(10624)
  {
    calc {
      bits_of_int(lut[165] as int, 64);
      bits_of_int(8881086896631215247, 64);
      {
        lemma_bits_of_int_64_split(8881086896631215247);
      }
      bits_of_int(2098492559, 32) + bits_of_int(2067789178, 32);
      {
        unroll_bits_of_int_32_0x7d14748f();
        unroll_bits_of_int_32_0x7b3ff57a();
      }
      [true, true, true, true, false, false, false, true, false, false, true, false, true, true, true, false, false, false, true, false, true, false, false, false, true, false, true, true, true, true, true, false]+[false, true, false, true, true, true, true, false, true, false, true, false, true, true, true, true, true, true, true, true, true, true, false, false, true, true, false, true, true, true, true, false];
      {
        calc {
          [true, true, true, true, false, false, false, true, false, false, true, false, true, true, true, false, false, false, true, false, true, false, false, false, true, false, true, true, true, true, true, false];
          {
            pow_21215();
            of_pow(21248, false, true, true, true, true, true, false, true, false, false, false, true, false, true, false, false, false, true, true, true, false, true, false, false, true, false, false, false, true, true, true, true);
          }
          pow_mod_crc(21248);
        }
        calc {
          [false, true, false, true, true, true, true, false, true, false, true, false, true, true, true, true, true, true, true, true, true, true, false, false, true, true, false, true, true, true, true, false];
          {
            pow_10591();
            of_pow(10624, false, true, true, true, true, false, true, true, false, false, true, true, true, true, true, true, true, true, true, true, false, true, false, true, false, true, true, true, true, false, true, false);
          }
          pow_mod_crc(10624);
        }
      }
      pow_mod_crc(21248) + pow_mod_crc(10624);
    }
  }



  lemma lut_entry_166()
  ensures bits_of_int(lut[166] as int, 64)
      == pow_mod_crc(21376) + pow_mod_crc(10688)
  {
    calc {
      bits_of_int(lut[166] as int, 64);
      bits_of_int(3258080866392867868, 64);
      {
        lemma_bits_of_int_64_split(3258080866392867868);
      }
      bits_of_int(853017628, 32) + bits_of_int(758581065, 32);
      {
        unroll_bits_of_int_32_0x32d8041c();
        unroll_bits_of_int_32_0x2d370749();
      }
      [false, false, true, true, true, false, false, false, false, false, true, false, false, false, false, false, false, false, false, true, true, false, true, true, false, true, false, false, true, true, false, false]+[true, false, false, true, false, false, true, false, true, true, true, false, false, false, false, false, true, true, true, false, true, true, false, false, true, false, true, true, false, true, false, false];
      {
        calc {
          [false, false, true, true, true, false, false, false, false, false, true, false, false, false, false, false, false, false, false, true, true, false, true, true, false, true, false, false, true, true, false, false];
          {
            pow_21343();
            of_pow(21376, false, false, true, true, false, false, true, false, true, true, false, true, true, false, false, false, false, false, false, false, false, true, false, false, false, false, false, true, true, true, false, false);
          }
          pow_mod_crc(21376);
        }
        calc {
          [true, false, false, true, false, false, true, false, true, true, true, false, false, false, false, false, true, true, true, false, true, true, false, false, true, false, true, true, false, true, false, false];
          {
            pow_10655();
            of_pow(10688, false, false, true, false, true, true, false, true, false, false, true, true, false, true, true, true, false, false, false, false, false, true, true, true, false, true, false, false, true, false, false, true);
          }
          pow_mod_crc(10688);
        }
      }
      pow_mod_crc(21376) + pow_mod_crc(10688);
    }
  }



  lemma lut_entry_167()
  ensures bits_of_int(lut[167] as int, 64)
      == pow_mod_crc(21504) + pow_mod_crc(10752)
  {
    calc {
      bits_of_int(lut[167] as int, 64);
      bits_of_int(14540073168230905057, 64);
      {
        lemma_bits_of_int_64_split(14540073168230905057);
      }
      bits_of_int(2291627233, 32) + bits_of_int(3385374594, 32);
      {
        unroll_bits_of_int_32_0x889774e1();
        unroll_bits_of_int_32_0xc9c8b782();
      }
      [true, false, false, false, false, true, true, true, false, false, true, false, true, true, true, false, true, true, true, false, true, false, false, true, false, false, false, true, false, false, false, true]+[false, true, false, false, false, false, false, true, true, true, true, false, true, true, false, true, false, false, false, true, false, false, true, true, true, false, false, true, false, false, true, true];
      {
        calc {
          [true, false, false, false, false, true, true, true, false, false, true, false, true, true, true, false, true, true, true, false, true, false, false, true, false, false, false, true, false, false, false, true];
          {
            pow_21471();
            of_pow(21504, true, false, false, false, true, false, false, false, true, false, false, true, false, true, true, true, false, true, true, true, false, true, false, false, true, true, true, false, false, false, false, true);
          }
          pow_mod_crc(21504);
        }
        calc {
          [false, true, false, false, false, false, false, true, true, true, true, false, true, true, false, true, false, false, false, true, false, false, true, true, true, false, false, true, false, false, true, true];
          {
            pow_10719();
            of_pow(10752, true, true, false, false, true, false, false, true, true, true, false, false, true, false, false, false, true, false, true, true, false, true, true, true, true, false, false, false, false, false, true, false);
          }
          pow_mod_crc(10752);
        }
      }
      pow_mod_crc(21504) + pow_mod_crc(10752);
    }
  }



  lemma lut_entry_168()
  ensures bits_of_int(lut[168] as int, 64)
      == pow_mod_crc(21632) + pow_mod_crc(10816)
  {
    calc {
      bits_of_int(lut[168] as int, 64);
      bits_of_int(4142613061100413183, 64);
      {
        lemma_bits_of_int_64_split(4142613061100413183);
      }
      bits_of_int(1825087743, 32) + bits_of_int(964527265, 32);
      {
        unroll_bits_of_int_32_0x6cc8a0ff();
        unroll_bits_of_int_32_0x397d84a1();
      }
      [true, true, true, true, true, true, true, true, false, false, false, false, false, true, false, true, false, false, false, true, false, false, true, true, false, false, true, true, false, true, true, false]+[true, false, false, false, false, true, false, true, false, false, true, false, false, false, false, true, true, false, true, true, true, true, true, false, true, false, false, true, true, true, false, false];
      {
        calc {
          [true, true, true, true, true, true, true, true, false, false, false, false, false, true, false, true, false, false, false, true, false, false, true, true, false, false, true, true, false, true, true, false];
          {
            pow_21599();
            of_pow(21632, false, true, true, false, true, true, false, false, true, true, false, false, true, false, false, false, true, false, true, false, false, false, false, false, true, true, true, true, true, true, true, true);
          }
          pow_mod_crc(21632);
        }
        calc {
          [true, false, false, false, false, true, false, true, false, false, true, false, false, false, false, true, true, false, true, true, true, true, true, false, true, false, false, true, true, true, false, false];
          {
            pow_10783();
            of_pow(10816, false, false, true, true, true, false, false, true, false, true, true, true, true, true, false, true, true, false, false, false, false, true, false, false, true, false, true, false, false, false, false, true);
          }
          pow_mod_crc(10816);
        }
      }
      pow_mod_crc(21632) + pow_mod_crc(10816);
    }
  }



  lemma lut_entry_169()
  ensures bits_of_int(lut[169] as int, 64)
      == pow_mod_crc(21760) + pow_mod_crc(10880)
  {
    calc {
      bits_of_int(lut[169] as int, 64);
      bits_of_int(4571378400415052751, 64);
      {
        lemma_bits_of_int_64_split(4571378400415052751);
      }
      bits_of_int(1520563151, 32) + bits_of_int(1064356975, 32);
      {
        unroll_bits_of_int_32_0x5aa1f3cf();
        unroll_bits_of_int_32_0x3f70cc6f();
      }
      [true, true, true, true, false, false, true, true, true, true, false, false, true, true, true, true, true, false, false, false, false, true, false, true, false, true, false, true, true, false, true, false]+[true, true, true, true, false, true, true, false, false, false, true, true, false, false, true, true, false, false, false, false, true, true, true, false, true, true, true, true, true, true, false, false];
      {
        calc {
          [true, true, true, true, false, false, true, true, true, true, false, false, true, true, true, true, true, false, false, false, false, true, false, true, false, true, false, true, true, false, true, false];
          {
            pow_21727();
            of_pow(21760, false, true, false, true, true, false, true, false, true, false, true, false, false, false, false, true, true, true, true, true, false, false, true, true, true, true, false, false, true, true, true, true);
          }
          pow_mod_crc(21760);
        }
        calc {
          [true, true, true, true, false, true, true, false, false, false, true, true, false, false, true, true, false, false, false, false, true, true, true, false, true, true, true, true, true, true, false, false];
          {
            pow_10847();
            of_pow(10880, false, false, true, true, true, true, true, true, false, true, true, true, false, false, false, false, true, true, false, false, true, true, false, false, false, true, true, false, true, true, true, true);
          }
          pow_mod_crc(10880);
        }
      }
      pow_mod_crc(21760) + pow_mod_crc(10880);
    }
  }



  lemma lut_entry_170()
  ensures bits_of_int(lut[170] as int, 64)
      == pow_mod_crc(21888) + pow_mod_crc(10944)
  {
    calc {
      bits_of_int(lut[170] as int, 64);
      bits_of_int(8723809412126818322, 64);
      {
        lemma_bits_of_int_64_split(8723809412126818322);
      }
      bits_of_int(2315730962, 32) + bits_of_int(2031170160, 32);
      {
        unroll_bits_of_int_32_0x8a074012();
        unroll_bits_of_int_32_0x79113270();
      }
      [false, true, false, false, true, false, false, false, false, false, false, false, false, false, true, false, true, true, true, false, false, false, false, false, false, true, false, true, false, false, false, true]+[false, false, false, false, true, true, true, false, false, true, false, false, true, true, false, false, true, false, false, false, true, false, false, false, true, false, false, true, true, true, true, false];
      {
        calc {
          [false, true, false, false, true, false, false, false, false, false, false, false, false, false, true, false, true, true, true, false, false, false, false, false, false, true, false, true, false, false, false, true];
          {
            pow_21855();
            of_pow(21888, true, false, false, false, true, false, true, false, false, false, false, false, false, true, true, true, false, true, false, false, false, false, false, false, false, false, false, true, false, false, true, false);
          }
          pow_mod_crc(21888);
        }
        calc {
          [false, false, false, false, true, true, true, false, false, true, false, false, true, true, false, false, true, false, false, false, true, false, false, false, true, false, false, true, true, true, true, false];
          {
            pow_10911();
            of_pow(10944, false, true, true, true, true, false, false, true, false, false, false, true, false, false, false, true, false, false, true, true, false, false, true, false, false, true, true, true, false, false, false, false);
          }
          pow_mod_crc(10944);
        }
      }
      pow_mod_crc(21888) + pow_mod_crc(10944);
    }
  }



  lemma lut_entry_171()
  ensures bits_of_int(lut[171] as int, 64)
      == pow_mod_crc(22016) + pow_mod_crc(11008)
  {
    calc {
      bits_of_int(lut[171] as int, 64);
      bits_of_int(10655805495647688883, 64);
      {
        lemma_bits_of_int_64_split(10655805495647688883);
      }
      bits_of_int(867981491, 32) + bits_of_int(2480998052, 32);
      {
        unroll_bits_of_int_32_0x33bc58b3();
        unroll_bits_of_int_32_0x93e106a4();
      }
      [true, true, false, false, true, true, false, true, false, false, false, true, true, false, true, false, false, false, true, true, true, true, false, true, true, true, false, false, true, true, false, false]+[false, false, true, false, false, true, false, true, false, true, true, false, false, false, false, false, true, false, false, false, false, true, true, true, true, true, false, false, true, false, false, true];
      {
        calc {
          [true, true, false, false, true, true, false, true, false, false, false, true, true, false, true, false, false, false, true, true, true, true, false, true, true, true, false, false, true, true, false, false];
          {
            pow_21983();
            of_pow(22016, false, false, true, true, false, false, true, true, true, false, true, true, true, true, false, false, false, true, false, true, true, false, false, false, true, false, true, true, false, false, true, true);
          }
          pow_mod_crc(22016);
        }
        calc {
          [false, false, true, false, false, true, false, true, false, true, true, false, false, false, false, false, true, false, false, false, false, true, true, true, true, true, false, false, true, false, false, true];
          {
            pow_10975();
            of_pow(11008, true, false, false, true, false, false, true, true, true, true, true, false, false, false, false, true, false, false, false, false, false, true, true, false, true, false, true, false, false, true, false, false);
          }
          pow_mod_crc(11008);
        }
      }
      pow_mod_crc(22016) + pow_mod_crc(11008);
    }
  }



  lemma lut_entry_172()
  ensures bits_of_int(lut[172] as int, 64)
      == pow_mod_crc(22144) + pow_mod_crc(11072)
  {
    calc {
      bits_of_int(lut[172] as int, 64);
      bits_of_int(13583269908076757034, 64);
      {
        lemma_bits_of_int_64_split(13583269908076757034);
      }
      bits_of_int(2670395434, 32) + bits_of_int(3162601475, 32);
      {
        unroll_bits_of_int_32_0x9f2b002a();
        unroll_bits_of_int_32_0xbc817803();
      }
      [false, true, false, true, false, true, false, false, false, false, false, false, false, false, false, false, true, true, false, true, false, true, false, false, true, true, true, true, true, false, false, true]+[true, true, false, false, false, false, false, false, false, false, false, true, true, true, true, false, true, false, false, false, false, false, false, true, false, false, true, true, true, true, false, true];
      {
        calc {
          [false, true, false, true, false, true, false, false, false, false, false, false, false, false, false, false, true, true, false, true, false, true, false, false, true, true, true, true, true, false, false, true];
          {
            pow_22111();
            of_pow(22144, true, false, false, true, true, true, true, true, false, false, true, false, true, false, true, true, false, false, false, false, false, false, false, false, false, false, true, false, true, false, true, false);
          }
          pow_mod_crc(22144);
        }
        calc {
          [true, true, false, false, false, false, false, false, false, false, false, true, true, true, true, false, true, false, false, false, false, false, false, true, false, false, true, true, true, true, false, true];
          {
            pow_11039();
            of_pow(11072, true, false, true, true, true, true, false, false, true, false, false, false, false, false, false, true, false, true, true, true, true, false, false, false, false, false, false, false, false, false, true, true);
          }
          pow_mod_crc(11072);
        }
      }
      pow_mod_crc(22144) + pow_mod_crc(11072);
    }
  }



  lemma lut_entry_173()
  ensures bits_of_int(lut[173] as int, 64)
      == pow_mod_crc(22272) + pow_mod_crc(11136)
  {
    calc {
      bits_of_int(lut[173] as int, 64);
      bits_of_int(7128191528799547999, 64);
      {
        lemma_bits_of_int_64_split(7128191528799547999);
      }
      bits_of_int(3171660383, 32) + bits_of_int(1659661421, 32);
      {
        unroll_bits_of_int_32_0xbd0bb25f();
        unroll_bits_of_int_32_0x62ec6c6d();
      }
      [true, true, true, true, true, false, true, false, false, true, false, false, true, true, false, true, true, true, false, true, false, false, false, false, true, false, true, true, true, true, false, true]+[true, false, true, true, false, true, true, false, false, false, true, true, false, true, true, false, false, false, true, true, false, true, true, true, false, true, false, false, false, true, true, false];
      {
        calc {
          [true, true, true, true, true, false, true, false, false, true, false, false, true, true, false, true, true, true, false, true, false, false, false, false, true, false, true, true, true, true, false, true];
          {
            pow_22239();
            of_pow(22272, true, false, true, true, true, true, false, true, false, false, false, false, true, false, true, true, true, false, true, true, false, false, true, false, false, true, false, true, true, true, true, true);
          }
          pow_mod_crc(22272);
        }
        calc {
          [true, false, true, true, false, true, true, false, false, false, true, true, false, true, true, false, false, false, true, true, false, true, true, true, false, true, false, false, false, true, true, false];
          {
            pow_11103();
            of_pow(11136, false, true, true, false, false, false, true, false, true, true, true, false, true, true, false, false, false, true, true, false, true, true, false, false, false, true, true, false, true, true, false, true);
          }
          pow_mod_crc(11136);
        }
      }
      pow_mod_crc(22272) + pow_mod_crc(11136);
    }
  }



  lemma lut_entry_174()
  ensures bits_of_int(lut[174] as int, 64)
      == pow_mod_crc(22400) + pow_mod_crc(11200)
  {
    calc {
      bits_of_int(lut[174] as int, 64);
      bits_of_int(9866045411070773866, 64);
      {
        lemma_bits_of_int_64_split(9866045411070773866);
      }
      bits_of_int(1623132778, 32) + bits_of_int(2297117703, 32);
      {
        unroll_bits_of_int_32_0x60bf0a6a();
        unroll_bits_of_int_32_0x88eb3c07();
      }
      [false, true, false, true, false, true, true, false, false, true, false, true, false, false, false, false, true, true, true, true, true, true, false, true, false, false, false, false, false, true, true, false]+[true, true, true, false, false, false, false, false, false, false, true, true, true, true, false, false, true, true, false, true, false, true, true, true, false, false, false, true, false, false, false, true];
      {
        calc {
          [false, true, false, true, false, true, true, false, false, true, false, true, false, false, false, false, true, true, true, true, true, true, false, true, false, false, false, false, false, true, true, false];
          {
            pow_22367();
            of_pow(22400, false, true, true, false, false, false, false, false, true, false, true, true, true, true, true, true, false, false, false, false, true, false, true, false, false, true, true, false, true, false, true, false);
          }
          pow_mod_crc(22400);
        }
        calc {
          [true, true, true, false, false, false, false, false, false, false, true, true, true, true, false, false, true, true, false, true, false, true, true, true, false, false, false, true, false, false, false, true];
          {
            pow_11167();
            of_pow(11200, true, false, false, false, true, false, false, false, true, true, true, false, true, false, true, true, false, false, true, true, true, true, false, false, false, false, false, false, false, true, true, true);
          }
          pow_mod_crc(11200);
        }
      }
      pow_mod_crc(22400) + pow_mod_crc(11200);
    }
  }



  lemma lut_entry_175()
  ensures bits_of_int(lut[175] as int, 64)
      == pow_mod_crc(22528) + pow_mod_crc(11264)
  {
    calc {
      bits_of_int(lut[175] as int, 64);
      bits_of_int(15569985310477893759, 64);
      {
        lemma_bits_of_int_64_split(15569985310477893759);
      }
      bits_of_int(2232795263, 32) + bits_of_int(3625169701, 32);
      {
        unroll_bits_of_int_32_0x8515c07f();
        unroll_bits_of_int_32_0xd813b325();
      }
      [true, true, true, true, true, true, true, false, false, false, false, false, false, false, true, true, true, false, true, false, true, false, false, false, true, false, true, false, false, false, false, true]+[true, false, true, false, false, true, false, false, true, true, false, false, true, true, false, true, true, true, false, false, true, false, false, false, false, false, false, true, true, false, true, true];
      {
        calc {
          [true, true, true, true, true, true, true, false, false, false, false, false, false, false, true, true, true, false, true, false, true, false, false, false, true, false, true, false, false, false, false, true];
          {
            pow_22495();
            of_pow(22528, true, false, false, false, false, true, false, true, false, false, false, true, false, true, false, true, true, true, false, false, false, false, false, false, false, true, true, true, true, true, true, true);
          }
          pow_mod_crc(22528);
        }
        calc {
          [true, false, true, false, false, true, false, false, true, true, false, false, true, true, false, true, true, true, false, false, true, false, false, false, false, false, false, true, true, false, true, true];
          {
            pow_11231();
            of_pow(11264, true, true, false, true, true, false, false, false, false, false, false, true, false, false, true, true, true, false, true, true, false, false, true, true, false, false, true, false, false, true, false, true);
          }
          pow_mod_crc(11264);
        }
      }
      pow_mod_crc(22528) + pow_mod_crc(11264);
    }
  }



  lemma lut_entry_176()
  ensures bits_of_int(lut[176] as int, 64)
      == pow_mod_crc(22656) + pow_mod_crc(11328)
  {
    calc {
      bits_of_int(lut[176] as int, 64);
      bits_of_int(7947927760681549979, 64);
      {
        lemma_bits_of_int_64_split(7947927760681549979);
      }
      bits_of_int(1004781723, 32) + bits_of_int(1850521136, 32);
      {
        unroll_bits_of_int_32_0x3be3c09b();
        unroll_bits_of_int_32_0x6e4cb630();
      }
      [true, true, false, true, true, false, false, true, false, false, false, false, false, false, true, true, true, true, false, false, false, true, true, true, true, true, false, true, true, true, false, false]+[false, false, false, false, true, true, false, false, false, true, true, false, true, true, false, true, false, false, true, true, false, false, true, false, false, true, true, true, false, true, true, false];
      {
        calc {
          [true, true, false, true, true, false, false, true, false, false, false, false, false, false, true, true, true, true, false, false, false, true, true, true, true, true, false, true, true, true, false, false];
          {
            pow_22623();
            of_pow(22656, false, false, true, true, true, false, true, true, true, true, true, false, false, false, true, true, true, true, false, false, false, false, false, false, true, false, false, true, true, false, true, true);
          }
          pow_mod_crc(22656);
        }
        calc {
          [false, false, false, false, true, true, false, false, false, true, true, false, true, true, false, true, false, false, true, true, false, false, true, false, false, true, true, true, false, true, true, false];
          {
            pow_11295();
            of_pow(11328, false, true, true, false, true, true, true, false, false, true, false, false, true, true, false, false, true, false, true, true, false, true, true, false, false, false, true, true, false, false, false, false);
          }
          pow_mod_crc(11328);
        }
      }
      pow_mod_crc(22656) + pow_mod_crc(11328);
    }
  }



  lemma lut_entry_177()
  ensures bits_of_int(lut[177] as int, 64)
      == pow_mod_crc(22784) + pow_mod_crc(11392)
  {
    calc {
      bits_of_int(lut[177] as int, 64);
      bits_of_int(1004380236101715237, 64);
      {
        lemma_bits_of_int_64_split(1004380236101715237);
      }
      bits_of_int(3628336421, 32) + bits_of_int(233850496, 32);
      {
        unroll_bits_of_int_32_0xd8440525();
        unroll_bits_of_int_32_0x0df04680();
      }
      [true, false, true, false, false, true, false, false, true, false, true, false, false, false, false, false, false, false, true, false, false, false, true, false, false, false, false, true, true, false, true, true]+[false, false, false, false, false, false, false, true, false, true, true, false, false, false, true, false, false, false, false, false, true, true, true, true, true, false, true, true, false, false, false, false];
      {
        calc {
          [true, false, true, false, false, true, false, false, true, false, true, false, false, false, false, false, false, false, true, false, false, false, true, false, false, false, false, true, true, false, true, true];
          {
            pow_22751();
            of_pow(22784, true, true, false, true, true, false, false, false, false, true, false, false, false, true, false, false, false, false, false, false, false, true, false, true, false, false, true, false, false, true, false, true);
          }
          pow_mod_crc(22784);
        }
        calc {
          [false, false, false, false, false, false, false, true, false, true, true, false, false, false, true, false, false, false, false, false, true, true, true, true, true, false, true, true, false, false, false, false];
          {
            pow_11359();
            of_pow(11392, false, false, false, false, true, true, false, true, true, true, true, true, false, false, false, false, false, true, false, false, false, true, true, false, true, false, false, false, false, false, false, false);
          }
          pow_mod_crc(11392);
        }
      }
      pow_mod_crc(22784) + pow_mod_crc(11392);
    }
  }



  lemma lut_entry_178()
  ensures bits_of_int(lut[178] as int, 64)
      == pow_mod_crc(22912) + pow_mod_crc(11456)
  {
    calc {
      bits_of_int(lut[178] as int, 64);
      bits_of_int(8185043130491144285, 64);
      {
        lemma_bits_of_int_64_split(8185043130491144285);
      }
      bits_of_int(1747781725, 32) + bits_of_int(1905728860, 32);
      {
        unroll_bits_of_int_32_0x682d085d();
        unroll_bits_of_int_32_0x71971d5c();
      }
      [true, false, true, true, true, false, true, false, false, false, false, true, false, false, false, false, true, false, true, true, false, true, false, false, false, false, false, true, false, true, true, false]+[false, false, true, true, true, false, true, false, true, false, true, true, true, false, false, false, true, true, true, false, true, false, false, true, true, false, false, false, true, true, true, false];
      {
        calc {
          [true, false, true, true, true, false, true, false, false, false, false, true, false, false, false, false, true, false, true, true, false, true, false, false, false, false, false, true, false, true, true, false];
          {
            pow_22879();
            of_pow(22912, false, true, true, false, true, false, false, false, false, false, true, false, true, true, false, true, false, false, false, false, true, false, false, false, false, true, false, true, true, true, false, true);
          }
          pow_mod_crc(22912);
        }
        calc {
          [false, false, true, true, true, false, true, false, true, false, true, true, true, false, false, false, true, true, true, false, true, false, false, true, true, false, false, false, true, true, true, false];
          {
            pow_11423();
            of_pow(11456, false, true, true, true, false, false, false, true, true, false, false, true, false, true, true, true, false, false, false, true, true, true, false, true, false, true, false, true, true, true, false, false);
          }
          pow_mod_crc(11456);
        }
      }
      pow_mod_crc(22912) + pow_mod_crc(11456);
    }
  }



  lemma lut_entry_179()
  ensures bits_of_int(lut[179] as int, 64)
      == pow_mod_crc(23040) + pow_mod_crc(11520)
  {
    calc {
      bits_of_int(lut[179] as int, 64);
      bits_of_int(2540593269819723502, 64);
      {
        lemma_bits_of_int_64_split(2540593269819723502);
      }
      bits_of_int(1180323566, 32) + bits_of_int(591527966, 32);
      {
        unroll_bits_of_int_32_0x465a4eee();
        unroll_bits_of_int_32_0x2342001e();
      }
      [false, true, true, true, false, true, true, true, false, true, true, true, false, false, true, false, false, true, false, true, true, false, true, false, false, true, true, false, false, false, true, false]+[false, true, true, true, true, false, false, false, false, false, false, false, false, false, false, false, false, true, false, false, false, false, true, false, true, true, false, false, false, true, false, false];
      {
        calc {
          [false, true, true, true, false, true, true, true, false, true, true, true, false, false, true, false, false, true, false, true, true, false, true, false, false, true, true, false, false, false, true, false];
          {
            pow_23007();
            of_pow(23040, false, true, false, false, false, true, true, false, false, true, false, true, true, false, true, false, false, true, false, false, true, true, true, false, true, true, true, false, true, true, true, false);
          }
          pow_mod_crc(23040);
        }
        calc {
          [false, true, true, true, true, false, false, false, false, false, false, false, false, false, false, false, false, true, false, false, false, false, true, false, true, true, false, false, false, true, false, false];
          {
            pow_11487();
            of_pow(11520, false, false, true, false, false, false, true, true, false, true, false, false, false, false, true, false, false, false, false, false, false, false, false, false, false, false, false, true, true, true, true, false);
          }
          pow_mod_crc(11520);
        }
      }
      pow_mod_crc(23040) + pow_mod_crc(11520);
    }
  }



  lemma lut_entry_180()
  ensures bits_of_int(lut[180] as int, 64)
      == pow_mod_crc(23168) + pow_mod_crc(11584)
  {
    calc {
      bits_of_int(lut[180] as int, 64);
      bits_of_int(17526756058045210242, 64);
      {
        lemma_bits_of_int_64_split(17526756058045210242);
      }
      bits_of_int(683007618, 32) + bits_of_int(4080765894, 32);
      {
        unroll_bits_of_int_32_0x28b5de82();
        unroll_bits_of_int_32_0xf33b8bc6();
      }
      [false, true, false, false, false, false, false, true, false, true, true, true, true, false, true, true, true, false, true, false, true, true, false, true, false, false, false, true, false, true, false, false]+[false, true, true, false, false, false, true, true, true, true, false, true, false, false, false, true, true, true, false, true, true, true, false, false, true, true, false, false, true, true, true, true];
      {
        calc {
          [false, true, false, false, false, false, false, true, false, true, true, true, true, false, true, true, true, false, true, false, true, true, false, true, false, false, false, true, false, true, false, false];
          {
            pow_23135();
            of_pow(23168, false, false, true, false, true, false, false, false, true, false, true, true, false, true, false, true, true, true, false, true, true, true, true, false, true, false, false, false, false, false, true, false);
          }
          pow_mod_crc(23168);
        }
        calc {
          [false, true, true, false, false, false, true, true, true, true, false, true, false, false, false, true, true, true, false, true, true, true, false, false, true, true, false, false, true, true, true, true];
          {
            pow_11551();
            of_pow(11584, true, true, true, true, false, false, true, true, false, false, true, true, true, false, true, true, true, false, false, false, true, false, true, true, true, true, false, false, false, true, true, false);
          }
          pow_mod_crc(11584);
        }
      }
      pow_mod_crc(23168) + pow_mod_crc(11584);
    }
  }



  lemma lut_entry_181()
  ensures bits_of_int(lut[181] as int, 64)
      == pow_mod_crc(23296) + pow_mod_crc(11648)
  {
    calc {
      bits_of_int(lut[181] as int, 64);
      bits_of_int(732553461832176864, 64);
      {
        lemma_bits_of_int_64_split(732553461832176864);
      }
      bits_of_int(125654240, 32) + bits_of_int(170560894, 32);
      {
        unroll_bits_of_int_32_0x077d54e0();
        unroll_bits_of_int_32_0x0a2a8d7e();
      }
      [false, false, false, false, false, true, true, true, false, false, true, false, true, false, true, false, true, false, true, true, true, true, true, false, true, true, true, false, false, false, false, false]+[false, true, true, true, true, true, true, false, true, false, true, true, false, false, false, true, false, true, false, true, false, true, false, false, false, true, false, true, false, false, false, false];
      {
        calc {
          [false, false, false, false, false, true, true, true, false, false, true, false, true, false, true, false, true, false, true, true, true, true, true, false, true, true, true, false, false, false, false, false];
          {
            pow_23263();
            of_pow(23296, false, false, false, false, false, true, true, true, false, true, true, true, true, true, false, true, false, true, false, true, false, true, false, false, true, true, true, false, false, false, false, false);
          }
          pow_mod_crc(23296);
        }
        calc {
          [false, true, true, true, true, true, true, false, true, false, true, true, false, false, false, true, false, true, false, true, false, true, false, false, false, true, false, true, false, false, false, false];
          {
            pow_11615();
            of_pow(11648, false, false, false, false, true, false, true, false, false, false, true, false, true, false, true, false, true, false, false, false, true, true, false, true, false, true, true, true, true, true, true, false);
          }
          pow_mod_crc(11648);
        }
      }
      pow_mod_crc(23296) + pow_mod_crc(11648);
    }
  }



  lemma lut_entry_182()
  ensures bits_of_int(lut[182] as int, 64)
      == pow_mod_crc(23424) + pow_mod_crc(11712)
  {
    calc {
      bits_of_int(lut[182] as int, 64);
      bits_of_int(11507747906947857548, 64);
      {
        lemma_bits_of_int_64_split(11507747906947857548);
      }
      bits_of_int(777993356, 32) + bits_of_int(2679356352, 32);
      {
        unroll_bits_of_int_32_0x2e5f3c8c();
        unroll_bits_of_int_32_0x9fb3bbc0();
      }
      [false, false, true, true, false, false, false, true, false, false, true, true, true, true, false, false, true, true, true, true, true, false, true, false, false, true, true, true, false, true, false, false]+[false, false, false, false, false, false, true, true, true, true, false, true, true, true, false, true, true, true, false, false, true, true, false, true, true, true, true, true, true, false, false, true];
      {
        calc {
          [false, false, true, true, false, false, false, true, false, false, true, true, true, true, false, false, true, true, true, true, true, false, true, false, false, true, true, true, false, true, false, false];
          {
            pow_23391();
            of_pow(23424, false, false, true, false, true, true, true, false, false, true, false, true, true, true, true, true, false, false, true, true, true, true, false, false, true, false, false, false, true, true, false, false);
          }
          pow_mod_crc(23424);
        }
        calc {
          [false, false, false, false, false, false, true, true, true, true, false, true, true, true, false, true, true, true, false, false, true, true, false, true, true, true, true, true, true, false, false, true];
          {
            pow_11679();
            of_pow(11712, true, false, false, true, true, true, true, true, true, false, true, true, false, false, true, true, true, false, true, true, true, false, true, true, true, true, false, false, false, false, false, false);
          }
          pow_mod_crc(11712);
        }
      }
      pow_mod_crc(23424) + pow_mod_crc(11712);
    }
  }



  lemma lut_entry_183()
  ensures bits_of_int(lut[183] as int, 64)
      == pow_mod_crc(23552) + pow_mod_crc(11776)
  {
    calc {
      bits_of_int(lut[183] as int, 64);
      bits_of_int(7897705537780707968, 64);
      {
        lemma_bits_of_int_64_split(7897705537780707968);
      }
      bits_of_int(3222139520, 32) + bits_of_int(1838827863, 32);
      {
        unroll_bits_of_int_32_0xc00df280();
        unroll_bits_of_int_32_0x6d9a4957();
      }
      [false, false, false, false, false, false, false, true, false, true, false, false, true, true, true, true, true, false, true, true, false, false, false, false, false, false, false, false, false, false, true, true]+[true, true, true, false, true, false, true, false, true, false, false, true, false, false, true, false, false, true, false, true, true, false, false, true, true, false, true, true, false, true, true, false];
      {
        calc {
          [false, false, false, false, false, false, false, true, false, true, false, false, true, true, true, true, true, false, true, true, false, false, false, false, false, false, false, false, false, false, true, true];
          {
            pow_23519();
            of_pow(23552, true, true, false, false, false, false, false, false, false, false, false, false, true, true, false, true, true, true, true, true, false, false, true, false, true, false, false, false, false, false, false, false);
          }
          pow_mod_crc(23552);
        }
        calc {
          [true, true, true, false, true, false, true, false, true, false, false, true, false, false, true, false, false, true, false, true, true, false, false, true, true, false, true, true, false, true, true, false];
          {
            pow_11743();
            of_pow(11776, false, true, true, false, true, true, false, true, true, false, false, true, true, false, true, false, false, true, false, false, true, false, false, true, false, true, false, true, false, true, true, true);
          }
          pow_mod_crc(11776);
        }
      }
      pow_mod_crc(23552) + pow_mod_crc(11776);
    }
  }



  lemma lut_entry_184()
  ensures bits_of_int(lut[184] as int, 64)
      == pow_mod_crc(23680) + pow_mod_crc(11840)
  {
    calc {
      bits_of_int(lut[184] as int, 64);
      bits_of_int(7994499721360277315, 64);
      {
        lemma_bits_of_int_64_split(7994499721360277315);
      }
      bits_of_int(3500375875, 32) + bits_of_int(1861364515, 32);
      {
        unroll_bits_of_int_32_0xd0a37f43();
        unroll_bits_of_int_32_0x6ef22b23();
      }
      [true, true, false, false, false, false, true, false, true, true, true, true, true, true, true, false, true, true, false, false, false, true, false, true, false, false, false, false, true, false, true, true]+[true, true, false, false, false, true, false, false, true, true, false, true, false, true, false, false, false, true, false, false, true, true, true, true, false, true, true, true, false, true, true, false];
      {
        calc {
          [true, true, false, false, false, false, true, false, true, true, true, true, true, true, true, false, true, true, false, false, false, true, false, true, false, false, false, false, true, false, true, true];
          {
            pow_23647();
            of_pow(23680, true, true, false, true, false, false, false, false, true, false, true, false, false, false, true, true, false, true, true, true, true, true, true, true, false, true, false, false, false, false, true, true);
          }
          pow_mod_crc(23680);
        }
        calc {
          [true, true, false, false, false, true, false, false, true, true, false, true, false, true, false, false, false, true, false, false, true, true, true, true, false, true, true, true, false, true, true, false];
          {
            pow_11807();
            of_pow(11840, false, true, true, false, true, true, true, false, true, true, true, true, false, false, true, false, false, false, true, false, true, false, true, true, false, false, true, false, false, false, true, true);
          }
          pow_mod_crc(11840);
        }
      }
      pow_mod_crc(23680) + pow_mod_crc(11840);
    }
  }



  lemma lut_entry_185()
  ensures bits_of_int(lut[185] as int, 64)
      == pow_mod_crc(23808) + pow_mod_crc(11904)
  {
    calc {
      bits_of_int(lut[185] as int, 64);
      bits_of_int(16768650235960318188, 64);
      {
        lemma_bits_of_int_64_split(16768650235960318188);
      }
      bits_of_int(2771343596, 32) + bits_of_int(3904255627, 32);
      {
        unroll_bits_of_int_32_0xa52f58ec();
        unroll_bits_of_int_32_0xe8b6368b();
      }
      [false, false, true, true, false, true, true, true, false, false, false, true, true, false, true, false, true, true, true, true, false, true, false, false, true, false, true, false, false, true, false, true]+[true, true, false, true, false, false, false, true, false, true, true, false, true, true, false, false, false, true, true, false, true, true, false, true, false, false, false, true, false, true, true, true];
      {
        calc {
          [false, false, true, true, false, true, true, true, false, false, false, true, true, false, true, false, true, true, true, true, false, true, false, false, true, false, true, false, false, true, false, true];
          {
            pow_23775();
            of_pow(23808, true, false, true, false, false, true, false, true, false, false, true, false, true, true, true, true, false, true, false, true, true, false, false, false, true, true, true, false, true, true, false, false);
          }
          pow_mod_crc(23808);
        }
        calc {
          [true, true, false, true, false, false, false, true, false, true, true, false, true, true, false, false, false, true, true, false, true, true, false, true, false, false, false, true, false, true, true, true];
          {
            pow_11871();
            of_pow(11904, true, true, true, false, true, false, false, false, true, false, true, true, false, true, true, false, false, false, true, true, false, true, true, false, true, false, false, false, true, false, true, true);
          }
          pow_mod_crc(11904);
        }
      }
      pow_mod_crc(23808) + pow_mod_crc(11904);
    }
  }



  lemma lut_entry_186()
  ensures bits_of_int(lut[186] as int, 64)
      == pow_mod_crc(23936) + pow_mod_crc(11968)
  {
    calc {
      bits_of_int(lut[186] as int, 64);
      bits_of_int(14856802771821211270, 64);
      {
        lemma_bits_of_int_64_split(14856802771821211270);
      }
      bits_of_int(7417478, 32) + bits_of_int(3459118952, 32);
      {
        unroll_bits_of_int_32_0x00712e86();
        unroll_bits_of_int_32_0xce2df768();
      }
      [false, true, true, false, false, false, false, true, false, true, true, true, false, true, false, false, true, false, false, false, true, true, true, false, false, false, false, false, false, false, false, false]+[false, false, false, true, false, true, true, false, true, true, true, false, true, true, true, true, true, false, true, true, false, true, false, false, false, true, true, true, false, false, true, true];
      {
        calc {
          [false, true, true, false, false, false, false, true, false, true, true, true, false, true, false, false, true, false, false, false, true, true, true, false, false, false, false, false, false, false, false, false];
          {
            pow_23903();
            of_pow(23936, false, false, false, false, false, false, false, false, false, true, true, true, false, false, false, true, false, false, true, false, true, true, true, false, true, false, false, false, false, true, true, false);
          }
          pow_mod_crc(23936);
        }
        calc {
          [false, false, false, true, false, true, true, false, true, true, true, false, true, true, true, true, true, false, true, true, false, true, false, false, false, true, true, true, false, false, true, true];
          {
            pow_11935();
            of_pow(11968, true, true, false, false, true, true, true, false, false, false, true, false, true, true, false, true, true, true, true, true, false, true, true, true, false, true, true, false, true, false, false, false);
          }
          pow_mod_crc(11968);
        }
      }
      pow_mod_crc(23936) + pow_mod_crc(11968);
    }
  }



  lemma lut_entry_187()
  ensures bits_of_int(lut[187] as int, 64)
      == pow_mod_crc(24064) + pow_mod_crc(12032)
  {
    calc {
      bits_of_int(lut[187] as int, 64);
      bits_of_int(15187243067946339970, 64);
      {
        lemma_bits_of_int_64_split(15187243067946339970);
      }
      bits_of_int(3597962882, 32) + bits_of_int(3536055578, 32);
      {
        unroll_bits_of_int_32_0xd6748e82();
        unroll_bits_of_int_32_0xd2c3ed1a();
      }
      [false, true, false, false, false, false, false, true, false, true, true, true, false, false, false, true, false, false, true, false, true, true, true, false, false, true, true, false, true, false, true, true]+[false, true, false, true, true, false, false, false, true, false, true, true, false, true, true, true, true, true, false, false, false, false, true, true, false, true, false, false, true, false, true, true];
      {
        calc {
          [false, true, false, false, false, false, false, true, false, true, true, true, false, false, false, true, false, false, true, false, true, true, true, false, false, true, true, false, true, false, true, true];
          {
            pow_24031();
            of_pow(24064, true, true, false, true, false, true, true, false, false, true, true, true, false, true, false, false, true, false, false, false, true, true, true, false, true, false, false, false, false, false, true, false);
          }
          pow_mod_crc(24064);
        }
        calc {
          [false, true, false, true, true, false, false, false, true, false, true, true, false, true, true, true, true, true, false, false, false, false, true, true, false, true, false, false, true, false, true, true];
          {
            pow_11999();
            of_pow(12032, true, true, false, true, false, false, true, false, true, true, false, false, false, false, true, true, true, true, true, false, true, true, false, true, false, false, false, true, true, false, true, false);
          }
          pow_mod_crc(12032);
        }
      }
      pow_mod_crc(24064) + pow_mod_crc(12032);
    }
  }



  lemma lut_entry_188()
  ensures bits_of_int(lut[188] as int, 64)
      == pow_mod_crc(24192) + pow_mod_crc(12096)
  {
    calc {
      bits_of_int(lut[188] as int, 64);
      bits_of_int(16517602300652888320, 64);
      {
        lemma_bits_of_int_64_split(16517602300652888320);
      }
      bits_of_int(1201086720, 32) + bits_of_int(3845803975, 32);
      {
        unroll_bits_of_int_32_0x47972100();
        unroll_bits_of_int_32_0xe53a4fc7();
      }
      [false, false, false, false, false, false, false, false, true, false, false, false, false, true, false, false, true, true, true, false, true, false, false, true, true, true, true, false, false, false, true, false]+[true, true, true, false, false, false, true, true, true, true, true, true, false, false, true, false, false, true, false, true, true, true, false, false, true, false, true, false, false, true, true, true];
      {
        calc {
          [false, false, false, false, false, false, false, false, true, false, false, false, false, true, false, false, true, true, true, false, true, false, false, true, true, true, true, false, false, false, true, false];
          {
            pow_24159();
            of_pow(24192, false, true, false, false, false, true, true, true, true, false, false, true, false, true, true, true, false, false, true, false, false, false, false, true, false, false, false, false, false, false, false, false);
          }
          pow_mod_crc(24192);
        }
        calc {
          [true, true, true, false, false, false, true, true, true, true, true, true, false, false, true, false, false, true, false, true, true, true, false, false, true, false, true, false, false, true, true, true];
          {
            pow_12063();
            of_pow(12096, true, true, true, false, false, true, false, true, false, false, true, true, true, false, true, false, false, true, false, false, true, true, true, true, true, true, false, false, false, true, true, true);
          }
          pow_mod_crc(12096);
        }
      }
      pow_mod_crc(24192) + pow_mod_crc(12096);
    }
  }



  lemma lut_entry_189()
  ensures bits_of_int(lut[189] as int, 64)
      == pow_mod_crc(24320) + pow_mod_crc(12160)
  {
    calc {
      bits_of_int(lut[189] as int, 64);
      bits_of_int(11050240449207791462, 64);
      {
        lemma_bits_of_int_64_split(11050240449207791462);
      }
      bits_of_int(1370419046, 32) + bits_of_int(2572834596, 32);
      {
        unroll_bits_of_int_32_0x51aeef66();
        unroll_bits_of_int_32_0x995a5724();
      }
      [false, true, true, false, false, true, true, false, true, true, true, true, false, true, true, true, false, true, true, true, false, true, false, true, true, false, false, false, true, false, true, false]+[false, false, true, false, false, true, false, false, true, true, true, false, true, false, true, false, false, true, false, true, true, false, true, false, true, false, false, true, true, false, false, true];
      {
        calc {
          [false, true, true, false, false, true, true, false, true, true, true, true, false, true, true, true, false, true, true, true, false, true, false, true, true, false, false, false, true, false, true, false];
          {
            pow_24287();
            of_pow(24320, false, true, false, true, false, false, false, true, true, false, true, false, true, true, true, false, true, true, true, false, true, true, true, true, false, true, true, false, false, true, true, false);
          }
          pow_mod_crc(24320);
        }
        calc {
          [false, false, true, false, false, true, false, false, true, true, true, false, true, false, true, false, false, true, false, true, true, false, true, false, true, false, false, true, true, false, false, true];
          {
            pow_12127();
            of_pow(12160, true, false, false, true, true, false, false, true, false, true, false, true, true, false, true, false, false, true, false, true, false, true, true, true, false, false, true, false, false, true, false, false);
          }
          pow_mod_crc(12160);
        }
      }
      pow_mod_crc(24320) + pow_mod_crc(12160);
    }
  }



  lemma lut_entry_190()
  ensures bits_of_int(lut[190] as int, 64)
      == pow_mod_crc(24448) + pow_mod_crc(12224)
  {
    calc {
      bits_of_int(lut[190] as int, 64);
      bits_of_int(13718150396010039058, 64);
      {
        lemma_bits_of_int_64_split(13718150396010039058);
      }
      bits_of_int(1905264402, 32) + bits_of_int(3194005786, 32);
      {
        unroll_bits_of_int_32_0x71900712();
        unroll_bits_of_int_32_0xbe60a91a();
      }
      [false, true, false, false, true, false, false, false, true, true, true, false, false, false, false, false, false, false, false, false, true, false, false, true, true, false, false, false, true, true, true, false]+[false, true, false, true, true, false, false, false, true, false, false, true, false, true, false, true, false, false, false, false, false, true, true, false, false, true, true, true, true, true, false, true];
      {
        calc {
          [false, true, false, false, true, false, false, false, true, true, true, false, false, false, false, false, false, false, false, false, true, false, false, true, true, false, false, false, true, true, true, false];
          {
            pow_24415();
            of_pow(24448, false, true, true, true, false, false, false, true, true, false, false, true, false, false, false, false, false, false, false, false, false, true, true, true, false, false, false, true, false, false, true, false);
          }
          pow_mod_crc(24448);
        }
        calc {
          [false, true, false, true, true, false, false, false, true, false, false, true, false, true, false, true, false, false, false, false, false, true, true, false, false, true, true, true, true, true, false, true];
          {
            pow_12191();
            of_pow(12224, true, false, true, true, true, true, true, false, false, true, true, false, false, false, false, false, true, false, true, false, true, false, false, true, false, false, false, true, true, false, true, false);
          }
          pow_mod_crc(12224);
        }
      }
      pow_mod_crc(24448) + pow_mod_crc(12224);
    }
  }



  lemma lut_entry_191()
  ensures bits_of_int(lut[191] as int, 64)
      == pow_mod_crc(24576) + pow_mod_crc(12288)
  {
    calc {
      bits_of_int(lut[191] as int, 64);
      bits_of_int(11454497961935271159, 64);
      {
        lemma_bits_of_int_64_split(11454497961935271159);
      }
      bits_of_int(899052791, 32) + bits_of_int(2666958133, 32);
      {
        unroll_bits_of_int_32_0x359674f7();
        unroll_bits_of_int_32_0x9ef68d35();
      }
      [true, true, true, false, true, true, true, true, false, false, true, false, true, true, true, false, false, true, true, false, true, false, false, true, true, false, true, false, true, true, false, false]+[true, false, true, false, true, true, false, false, true, false, true, true, false, false, false, true, false, true, true, false, true, true, true, true, false, true, true, true, true, false, false, true];
      {
        calc {
          [true, true, true, false, true, true, true, true, false, false, true, false, true, true, true, false, false, true, true, false, true, false, false, true, true, false, true, false, true, true, false, false];
          {
            pow_24543();
            of_pow(24576, false, false, true, true, false, true, false, true, true, false, false, true, false, true, true, false, false, true, true, true, false, true, false, false, true, true, true, true, false, true, true, true);
          }
          pow_mod_crc(24576);
        }
        calc {
          [true, false, true, false, true, true, false, false, true, false, true, true, false, false, false, true, false, true, true, false, true, true, true, true, false, true, true, true, true, false, false, true];
          {
            pow_12255();
            of_pow(12288, true, false, false, true, true, true, true, false, true, true, true, true, false, true, true, false, true, false, false, false, true, true, false, true, false, false, true, true, false, true, false, true);
          }
          pow_mod_crc(12288);
        }
      }
      pow_mod_crc(24576) + pow_mod_crc(12288);
    }
  }



  lemma lut_entry_192()
  ensures bits_of_int(lut[192] as int, 64)
      == pow_mod_crc(24704) + pow_mod_crc(12352)
  {
    calc {
      bits_of_int(lut[192] as int, 64);
      bits_of_int(2160050058274258197, 64);
      {
        lemma_bits_of_int_64_split(2160050058274258197);
      }
      bits_of_int(1686093077, 32) + bits_of_int(502925845, 32);
      {
        unroll_bits_of_int_32_0x647fbd15();
        unroll_bits_of_int_32_0x1dfa0a15();
      }
      [true, false, true, false, true, false, false, false, true, false, true, true, true, true, false, true, true, true, true, true, true, true, true, false, false, false, true, false, false, true, true, false]+[true, false, true, false, true, false, false, false, false, true, false, true, false, false, false, false, false, true, false, true, true, true, true, true, true, false, true, true, true, false, false, false];
      {
        calc {
          [true, false, true, false, true, false, false, false, true, false, true, true, true, true, false, true, true, true, true, true, true, true, true, false, false, false, true, false, false, true, true, false];
          {
            pow_24671();
            of_pow(24704, false, true, true, false, false, true, false, false, false, true, true, true, true, true, true, true, true, false, true, true, true, true, false, true, false, false, false, true, false, true, false, true);
          }
          pow_mod_crc(24704);
        }
        calc {
          [true, false, true, false, true, false, false, false, false, true, false, true, false, false, false, false, false, true, false, true, true, true, true, true, true, false, true, true, true, false, false, false];
          {
            pow_12319();
            of_pow(12352, false, false, false, true, true, true, false, true, true, true, true, true, true, false, true, false, false, false, false, false, true, false, true, false, false, false, false, true, false, true, false, true);
          }
          pow_mod_crc(12352);
        }
      }
      pow_mod_crc(24704) + pow_mod_crc(12352);
    }
  }



  lemma lut_entry_193()
  ensures bits_of_int(lut[193] as int, 64)
      == pow_mod_crc(24832) + pow_mod_crc(12416)
  {
    calc {
      bits_of_int(lut[193] as int, 64);
      bits_of_int(870209788232509449, 64);
      {
        lemma_bits_of_int_64_split(870209788232509449);
      }
      bits_of_int(464168969, 32) + bits_of_int(202611505, 32);
      {
        unroll_bits_of_int_32_0x1baaa809();
        unroll_bits_of_int_32_0x0c139b31();
      }
      [true, false, false, true, false, false, false, false, false, false, false, true, false, true, false, true, false, true, false, true, false, true, false, true, true, true, false, true, true, false, false, false]+[true, false, false, false, true, true, false, false, true, true, false, true, true, false, false, true, true, true, false, false, true, false, false, false, false, false, true, true, false, false, false, false];
      {
        calc {
          [true, false, false, true, false, false, false, false, false, false, false, true, false, true, false, true, false, true, false, true, false, true, false, true, true, true, false, true, true, false, false, false];
          {
            pow_24799();
            of_pow(24832, false, false, false, true, true, false, true, true, true, false, true, false, true, false, true, false, true, false, true, false, true, false, false, false, false, false, false, false, true, false, false, true);
          }
          pow_mod_crc(24832);
        }
        calc {
          [true, false, false, false, true, true, false, false, true, true, false, true, true, false, false, true, true, true, false, false, true, false, false, false, false, false, true, true, false, false, false, false];
          {
            pow_12383();
            of_pow(12416, false, false, false, false, true, true, false, false, false, false, false, true, false, false, true, true, true, false, false, true, true, false, true, true, false, false, true, true, false, false, false, true);
          }
          pow_mod_crc(12416);
        }
      }
      pow_mod_crc(24832) + pow_mod_crc(12416);
    }
  }



  lemma lut_entry_194()
  ensures bits_of_int(lut[194] as int, 64)
      == pow_mod_crc(24960) + pow_mod_crc(12480)
  {
    calc {
      bits_of_int(lut[194] as int, 64);
      bits_of_int(10287668052134391686, 64);
      {
        lemma_bits_of_int_64_split(10287668052134391686);
      }
      bits_of_int(1184558982, 32) + bits_of_int(2395284374, 32);
      {
        unroll_bits_of_int_32_0x469aef86();
        unroll_bits_of_int_32_0x8ec52396();
      }
      [false, true, true, false, false, false, false, true, true, true, true, true, false, true, true, true, false, true, false, true, true, false, false, true, false, true, true, false, false, false, true, false]+[false, true, true, false, true, false, false, true, true, true, false, false, false, true, false, false, true, false, true, false, false, false, true, true, false, true, true, true, false, false, false, true];
      {
        calc {
          [false, true, true, false, false, false, false, true, true, true, true, true, false, true, true, true, false, true, false, true, true, false, false, true, false, true, true, false, false, false, true, false];
          {
            pow_24927();
            of_pow(24960, false, true, false, false, false, true, true, false, true, false, false, true, true, false, true, false, true, true, true, false, true, true, true, true, true, false, false, false, false, true, true, false);
          }
          pow_mod_crc(24960);
        }
        calc {
          [false, true, true, false, true, false, false, true, true, true, false, false, false, true, false, false, true, false, true, false, false, false, true, true, false, true, true, true, false, false, false, true];
          {
            pow_12447();
            of_pow(12480, true, false, false, false, true, true, true, false, true, true, false, false, false, true, false, true, false, false, true, false, false, false, true, true, true, false, false, true, false, true, true, false);
          }
          pow_mod_crc(12480);
        }
      }
      pow_mod_crc(24960) + pow_mod_crc(12480);
    }
  }



  lemma lut_entry_195()
  ensures bits_of_int(lut[195] as int, 64)
      == pow_mod_crc(25088) + pow_mod_crc(12544)
  {
    calc {
      bits_of_int(lut[195] as int, 64);
      bits_of_int(17448948681198021894, 64);
      {
        lemma_bits_of_int_64_split(17448948681198021894);
      }
      bits_of_int(2262052102, 32) + bits_of_int(4062649952, 32);
      {
        unroll_bits_of_int_32_0x86d42d06();
        unroll_bits_of_int_32_0xf2271e60();
      }
      [false, true, true, false, false, false, false, false, true, false, true, true, false, true, false, false, false, false, true, false, true, false, true, true, false, true, true, false, false, false, false, true]+[false, false, false, false, false, true, true, false, false, true, true, true, true, false, false, false, true, true, true, false, false, true, false, false, false, true, false, false, true, true, true, true];
      {
        calc {
          [false, true, true, false, false, false, false, false, true, false, true, true, false, true, false, false, false, false, true, false, true, false, true, true, false, true, true, false, false, false, false, true];
          {
            pow_25055();
            of_pow(25088, true, false, false, false, false, true, true, false, true, true, false, true, false, true, false, false, false, false, true, false, true, true, false, true, false, false, false, false, false, true, true, false);
          }
          pow_mod_crc(25088);
        }
        calc {
          [false, false, false, false, false, true, true, false, false, true, true, true, true, false, false, false, true, true, true, false, false, true, false, false, false, true, false, false, true, true, true, true];
          {
            pow_12511();
            of_pow(12544, true, true, true, true, false, false, true, false, false, false, true, false, false, true, true, true, false, false, false, true, true, true, true, false, false, true, true, false, false, false, false, false);
          }
          pow_mod_crc(12544);
        }
      }
      pow_mod_crc(25088) + pow_mod_crc(12544);
    }
  }



  lemma lut_entry_196()
  ensures bits_of_int(lut[196] as int, 64)
      == pow_mod_crc(25216) + pow_mod_crc(12608)
  {
    calc {
      bits_of_int(lut[196] as int, 64);
      bits_of_int(1042138085795173488, 64);
      {
        lemma_bits_of_int_64_split(1042138085795173488);
      }
      bits_of_int(1253708912, 32) + bits_of_int(242641681, 32);
      {
        unroll_bits_of_int_32_0x4aba1470();
        unroll_bits_of_int_32_0x0e766b11();
      }
      [false, false, false, false, true, true, true, false, false, false, true, false, true, false, false, false, false, true, false, true, true, true, false, true, false, true, false, true, false, false, true, false]+[true, false, false, false, true, false, false, false, true, true, false, true, false, true, true, false, false, true, true, false, true, true, true, false, false, true, true, true, false, false, false, false];
      {
        calc {
          [false, false, false, false, true, true, true, false, false, false, true, false, true, false, false, false, false, true, false, true, true, true, false, true, false, true, false, true, false, false, true, false];
          {
            pow_25183();
            of_pow(25216, false, true, false, false, true, false, true, false, true, false, true, true, true, false, true, false, false, false, false, true, false, true, false, false, false, true, true, true, false, false, false, false);
          }
          pow_mod_crc(25216);
        }
        calc {
          [true, false, false, false, true, false, false, false, true, true, false, true, false, true, true, false, false, true, true, false, true, true, true, false, false, true, true, true, false, false, false, false];
          {
            pow_12575();
            of_pow(12608, false, false, false, false, true, true, true, false, false, true, true, true, false, true, true, false, false, true, true, false, true, false, true, true, false, false, false, true, false, false, false, true);
          }
          pow_mod_crc(12608);
        }
      }
      pow_mod_crc(25216) + pow_mod_crc(12608);
    }
  }



  lemma lut_entry_197()
  ensures bits_of_int(lut[197] as int, 64)
      == pow_mod_crc(25344) + pow_mod_crc(12672)
  {
    calc {
      bits_of_int(lut[197] as int, 64);
      bits_of_int(796003306100805130, 64);
      {
        lemma_bits_of_int_64_split(796003306100805130);
      }
      bits_of_int(472698378, 32) + bits_of_int(185333962, 32);
      {
        unroll_bits_of_int_32_0x1c2cce0a();
        unroll_bits_of_int_32_0x0b0bf8ca();
      }
      [false, true, false, true, false, false, false, false, false, true, true, true, false, false, true, true, false, false, true, true, false, true, false, false, false, false, true, true, true, false, false, false]+[false, true, false, true, false, false, true, true, false, false, false, true, true, true, true, true, true, true, false, true, false, false, false, false, true, true, false, true, false, false, false, false];
      {
        calc {
          [false, true, false, true, false, false, false, false, false, true, true, true, false, false, true, true, false, false, true, true, false, true, false, false, false, false, true, true, true, false, false, false];
          {
            pow_25311();
            of_pow(25344, false, false, false, true, true, true, false, false, false, false, true, false, true, true, false, false, true, true, false, false, true, true, true, false, false, false, false, false, true, false, true, false);
          }
          pow_mod_crc(25344);
        }
        calc {
          [false, true, false, true, false, false, true, true, false, false, false, true, true, true, true, true, true, true, false, true, false, false, false, false, true, true, false, true, false, false, false, false];
          {
            pow_12639();
            of_pow(12672, false, false, false, false, true, false, true, true, false, false, false, false, true, false, true, true, true, true, true, true, true, false, false, false, true, true, false, false, true, false, true, false);
          }
          pow_mod_crc(12672);
        }
      }
      pow_mod_crc(25344) + pow_mod_crc(12672);
    }
  }



  lemma lut_entry_198()
  ensures bits_of_int(lut[198] as int, 64)
      == pow_mod_crc(25472) + pow_mod_crc(12736)
  {
    calc {
      bits_of_int(lut[198] as int, 64);
      bits_of_int(5140936647684969171, 64);
      {
        lemma_bits_of_int_64_split(5140936647684969171);
      }
      bits_of_int(2852967123, 32) + bits_of_int(1196967588, 32);
      {
        unroll_bits_of_int_32_0xaa0cd2d3();
        unroll_bits_of_int_32_0x475846a4();
      }
      [true, true, false, false, true, false, true, true, false, true, false, false, true, false, true, true, false, false, true, true, false, false, false, false, false, true, false, true, false, true, false, true]+[false, false, true, false, false, true, false, true, false, true, true, false, false, false, true, false, false, false, false, true, true, false, true, false, true, true, true, false, false, false, true, false];
      {
        calc {
          [true, true, false, false, true, false, true, true, false, true, false, false, true, false, true, true, false, false, true, true, false, false, false, false, false, true, false, true, false, true, false, true];
          {
            pow_25439();
            of_pow(25472, true, false, true, false, true, false, true, false, false, false, false, false, true, true, false, false, true, true, false, true, false, false, true, false, true, true, false, true, false, false, true, true);
          }
          pow_mod_crc(25472);
        }
        calc {
          [false, false, true, false, false, true, false, true, false, true, true, false, false, false, true, false, false, false, false, true, true, false, true, false, true, true, true, false, false, false, true, false];
          {
            pow_12703();
            of_pow(12736, false, true, false, false, false, true, true, true, false, true, false, true, true, false, false, false, false, true, false, false, false, true, true, false, true, false, true, false, false, true, false, false);
          }
          pow_mod_crc(12736);
        }
      }
      pow_mod_crc(25472) + pow_mod_crc(12736);
    }
  }



  lemma lut_entry_199()
  ensures bits_of_int(lut[199] as int, 64)
      == pow_mod_crc(25600) + pow_mod_crc(12800)
  {
    calc {
      bits_of_int(lut[199] as int, 64);
      bits_of_int(2766614848719849024, 64);
      {
        lemma_bits_of_int_64_split(2766614848719849024);
      }
      bits_of_int(4165240384, 32) + bits_of_int(644152715, 32);
      {
        unroll_bits_of_int_32_0xf8448640();
        unroll_bits_of_int_32_0x2664fd8b();
      }
      [false, false, false, false, false, false, true, false, false, true, true, false, false, false, false, true, false, false, true, false, false, false, true, false, false, false, false, true, true, true, true, true]+[true, true, false, true, false, false, false, true, true, false, true, true, true, true, true, true, false, false, true, false, false, true, true, false, false, true, true, false, false, true, false, false];
      {
        calc {
          [false, false, false, false, false, false, true, false, false, true, true, false, false, false, false, true, false, false, true, false, false, false, true, false, false, false, false, true, true, true, true, true];
          {
            pow_25567();
            of_pow(25600, true, true, true, true, true, false, false, false, false, true, false, false, false, true, false, false, true, false, false, false, false, true, true, false, false, true, false, false, false, false, false, false);
          }
          pow_mod_crc(25600);
        }
        calc {
          [true, true, false, true, false, false, false, true, true, false, true, true, true, true, true, true, false, false, true, false, false, true, true, false, false, true, true, false, false, true, false, false];
          {
            pow_12767();
            of_pow(12800, false, false, true, false, false, true, true, false, false, true, true, false, false, true, false, false, true, true, true, true, true, true, false, true, true, false, false, false, true, false, true, true);
          }
          pow_mod_crc(12800);
        }
      }
      pow_mod_crc(25600) + pow_mod_crc(12800);
    }
  }



  lemma lut_entry_200()
  ensures bits_of_int(lut[200] as int, 64)
      == pow_mod_crc(25728) + pow_mod_crc(12864)
  {
    calc {
      bits_of_int(lut[200] as int, 64);
      bits_of_int(12872378066903485932, 64);
      {
        lemma_bits_of_int_64_split(12872378066903485932);
      }
      bits_of_int(2890911212, 32) + bits_of_int(2997084070, 32);
      {
        unroll_bits_of_int_32_0xac4fcdec();
        unroll_bits_of_int_32_0xb2a3dfa6();
      }
      [false, false, true, true, false, true, true, true, true, false, true, true, false, false, true, true, true, true, true, true, false, false, true, false, false, false, true, true, false, true, false, true]+[false, true, true, false, false, true, false, true, true, true, true, true, true, false, true, true, true, true, false, false, false, true, false, true, false, true, false, false, true, true, false, true];
      {
        calc {
          [false, false, true, true, false, true, true, true, true, false, true, true, false, false, true, true, true, true, true, true, false, false, true, false, false, false, true, true, false, true, false, true];
          {
            pow_25695();
            of_pow(25728, true, false, true, false, true, true, false, false, false, true, false, false, true, true, true, true, true, true, false, false, true, true, false, true, true, true, true, false, true, true, false, false);
          }
          pow_mod_crc(25728);
        }
        calc {
          [false, true, true, false, false, true, false, true, true, true, true, true, true, false, true, true, true, true, false, false, false, true, false, true, false, true, false, false, true, true, false, true];
          {
            pow_12831();
            of_pow(12864, true, false, true, true, false, false, true, false, true, false, true, false, false, false, true, true, true, true, false, true, true, true, true, true, true, false, true, false, false, true, true, false);
          }
          pow_mod_crc(12864);
        }
      }
      pow_mod_crc(25728) + pow_mod_crc(12864);
    }
  }



  lemma lut_entry_201()
  ensures bits_of_int(lut[201] as int, 64)
      == pow_mod_crc(25856) + pow_mod_crc(12928)
  {
    calc {
      bits_of_int(lut[201] as int, 64);
      bits_of_int(17105939318827708756, 64);
      {
        lemma_bits_of_int_64_split(17105939318827708756);
      }
      bits_of_int(3894210900, 32) + bits_of_int(3982786861, 32);
      {
        unroll_bits_of_int_32_0xe81cf154();
        unroll_bits_of_int_32_0xed64812d();
      }
      [false, false, true, false, true, false, true, false, true, false, false, false, true, true, true, true, false, false, true, true, true, false, false, false, false, false, false, true, false, true, true, true]+[true, false, true, true, false, true, false, false, true, false, false, false, false, false, false, true, false, false, true, false, false, true, true, false, true, false, true, true, false, true, true, true];
      {
        calc {
          [false, false, true, false, true, false, true, false, true, false, false, false, true, true, true, true, false, false, true, true, true, false, false, false, false, false, false, true, false, true, true, true];
          {
            pow_25823();
            of_pow(25856, true, true, true, false, true, false, false, false, false, false, false, true, true, true, false, false, true, true, true, true, false, false, false, true, false, true, false, true, false, true, false, false);
          }
          pow_mod_crc(25856);
        }
        calc {
          [true, false, true, true, false, true, false, false, true, false, false, false, false, false, false, true, false, false, true, false, false, true, true, false, true, false, true, true, false, true, true, true];
          {
            pow_12895();
            of_pow(12928, true, true, true, false, true, true, false, true, false, true, true, false, false, true, false, false, true, false, false, false, false, false, false, true, false, false, true, false, true, true, false, true);
          }
          pow_mod_crc(12928);
        }
      }
      pow_mod_crc(25856) + pow_mod_crc(12928);
    }
  }



  lemma lut_entry_202()
  ensures bits_of_int(lut[202] as int, 64)
      == pow_mod_crc(25984) + pow_mod_crc(12992)
  {
    calc {
      bits_of_int(lut[202] as int, 64);
      bits_of_int(15860013281801877596, 64);
      {
        lemma_bits_of_int_64_split(15860013281801877596);
      }
      bits_of_int(3267835996, 32) + bits_of_int(3692697100, 32);
      {
        unroll_bits_of_int_32_0xc2c7385c();
        unroll_bits_of_int_32_0xdc1a160c();
      }
      [false, false, true, true, true, false, true, false, false, false, false, true, true, true, false, false, true, true, true, false, false, false, true, true, false, true, false, false, false, false, true, true]+[false, false, true, true, false, false, false, false, false, true, true, false, true, false, false, false, false, true, false, true, true, false, false, false, false, false, true, true, true, false, true, true];
      {
        calc {
          [false, false, true, true, true, false, true, false, false, false, false, true, true, true, false, false, true, true, true, false, false, false, true, true, false, true, false, false, false, false, true, true];
          {
            pow_25951();
            of_pow(25984, true, true, false, false, false, false, true, false, true, true, false, false, false, true, true, true, false, false, true, true, true, false, false, false, false, true, false, true, true, true, false, false);
          }
          pow_mod_crc(25984);
        }
        calc {
          [false, false, true, true, false, false, false, false, false, true, true, false, true, false, false, false, false, true, false, true, true, false, false, false, false, false, true, true, true, false, true, true];
          {
            pow_12959();
            of_pow(12992, true, true, false, true, true, true, false, false, false, false, false, true, true, false, true, false, false, false, false, true, false, true, true, false, false, false, false, false, true, true, false, false);
          }
          pow_mod_crc(12992);
        }
      }
      pow_mod_crc(25984) + pow_mod_crc(12992);
    }
  }



  lemma lut_entry_203()
  ensures bits_of_int(lut[203] as int, 64)
      == pow_mod_crc(26112) + pow_mod_crc(13056)
  {
    calc {
      bits_of_int(lut[203] as int, 64);
      bits_of_int(211110298088626140, 64);
      {
        lemma_bits_of_int_64_split(211110298088626140);
      }
      bits_of_int(2516572124, 32) + bits_of_int(49152946, 32);
      {
        unroll_bits_of_int_32_0x95ffd7dc();
        unroll_bits_of_int_32_0x02ee03b2();
      }
      [false, false, true, true, true, false, true, true, true, true, true, false, true, false, true, true, true, true, true, true, true, true, true, true, true, false, true, false, true, false, false, true]+[false, true, false, false, true, true, false, true, true, true, false, false, false, false, false, false, false, true, true, true, false, true, true, true, false, true, false, false, false, false, false, false];
      {
        calc {
          [false, false, true, true, true, false, true, true, true, true, true, false, true, false, true, true, true, true, true, true, true, true, true, true, true, false, true, false, true, false, false, true];
          {
            pow_26079();
            of_pow(26112, true, false, false, true, false, true, false, true, true, true, true, true, true, true, true, true, true, true, false, true, false, true, true, true, true, true, false, true, true, true, false, false);
          }
          pow_mod_crc(26112);
        }
        calc {
          [false, true, false, false, true, true, false, true, true, true, false, false, false, false, false, false, false, true, true, true, false, true, true, true, false, true, false, false, false, false, false, false];
          {
            pow_13023();
            of_pow(13056, false, false, false, false, false, false, true, false, true, true, true, false, true, true, true, false, false, false, false, false, false, false, true, true, true, false, true, true, false, false, true, false);
          }
          pow_mod_crc(13056);
        }
      }
      pow_mod_crc(26112) + pow_mod_crc(13056);
    }
  }



  lemma lut_entry_204()
  ensures bits_of_int(lut[204] as int, 64)
      == pow_mod_crc(26240) + pow_mod_crc(13120)
  {
    calc {
      bits_of_int(lut[204] as int, 64);
      bits_of_int(8768472313312993654, 64);
      {
        lemma_bits_of_int_64_split(8768472313312993654);
      }
      bits_of_int(2447270262, 32) + bits_of_int(2041569052, 32);
      {
        unroll_bits_of_int_32_0x91de6176();
        unroll_bits_of_int_32_0x79afdf1c();
      }
      [false, true, true, false, true, true, true, false, true, false, false, false, false, true, true, false, false, true, true, true, true, false, true, true, true, false, false, false, true, false, false, true]+[false, false, true, true, true, false, false, false, true, true, true, true, true, false, true, true, true, true, true, true, false, true, false, true, true, false, false, true, true, true, true, false];
      {
        calc {
          [false, true, true, false, true, true, true, false, true, false, false, false, false, true, true, false, false, true, true, true, true, false, true, true, true, false, false, false, true, false, false, true];
          {
            pow_26207();
            of_pow(26240, true, false, false, true, false, false, false, true, true, true, false, true, true, true, true, false, false, true, true, false, false, false, false, true, false, true, true, true, false, true, true, false);
          }
          pow_mod_crc(26240);
        }
        calc {
          [false, false, true, true, true, false, false, false, true, true, true, true, true, false, true, true, true, true, true, true, false, true, false, true, true, false, false, true, true, true, true, false];
          {
            pow_13087();
            of_pow(13120, false, true, true, true, true, false, false, true, true, false, true, false, true, true, true, true, true, true, false, true, true, true, true, true, false, false, false, true, true, true, false, false);
          }
          pow_mod_crc(13120);
        }
      }
      pow_mod_crc(26240) + pow_mod_crc(13120);
    }
  }



  lemma lut_entry_205()
  ensures bits_of_int(lut[205] as int, 64)
      == pow_mod_crc(26368) + pow_mod_crc(13184)
  {
    calc {
      bits_of_int(lut[205] as int, 64);
      bits_of_int(9657034882667153836, 64);
      {
        lemma_bits_of_int_64_split(9657034882667153836);
      }
      bits_of_int(2230225324, 32) + bits_of_int(2248453647, 32);
      {
        unroll_bits_of_int_32_0x84ee89ac();
        unroll_bits_of_int_32_0x8604ae0f();
      }
      [false, false, true, true, false, true, false, true, true, false, false, true, false, false, false, true, false, true, true, true, false, true, true, true, false, false, true, false, false, false, false, true]+[true, true, true, true, false, false, false, false, false, true, true, true, false, true, false, true, false, false, true, false, false, false, false, false, false, true, true, false, false, false, false, true];
      {
        calc {
          [false, false, true, true, false, true, false, true, true, false, false, true, false, false, false, true, false, true, true, true, false, true, true, true, false, false, true, false, false, false, false, true];
          {
            pow_26335();
            of_pow(26368, true, false, false, false, false, true, false, false, true, true, true, false, true, true, true, false, true, false, false, false, true, false, false, true, true, false, true, false, true, true, false, false);
          }
          pow_mod_crc(26368);
        }
        calc {
          [true, true, true, true, false, false, false, false, false, true, true, true, false, true, false, true, false, false, true, false, false, false, false, false, false, true, true, false, false, false, false, true];
          {
            pow_13151();
            of_pow(13184, true, false, false, false, false, true, true, false, false, false, false, false, false, true, false, false, true, false, true, false, true, true, true, false, false, false, false, false, true, true, true, true);
          }
          pow_mod_crc(13184);
        }
      }
      pow_mod_crc(26368) + pow_mod_crc(13184);
    }
  }



  lemma lut_entry_206()
  ensures bits_of_int(lut[206] as int, 64)
      == pow_mod_crc(26496) + pow_mod_crc(13248)
  {
    calc {
      bits_of_int(lut[206] as int, 64);
      bits_of_int(552938102583079053, 64);
      {
        lemma_bits_of_int_64_split(552938102583079053);
      }
      bits_of_int(1396584589, 32) + bits_of_int(128740934, 32);
      {
        unroll_bits_of_int_32_0x533e308d();
        unroll_bits_of_int_32_0x07ac6e46();
      }
      [true, false, true, true, false, false, false, true, false, false, false, false, true, true, false, false, false, true, true, true, true, true, false, false, true, true, false, false, true, false, true, false]+[false, true, true, false, false, false, true, false, false, true, true, true, false, true, true, false, false, false, true, true, false, true, false, true, true, true, true, false, false, false, false, false];
      {
        calc {
          [true, false, true, true, false, false, false, true, false, false, false, false, true, true, false, false, false, true, true, true, true, true, false, false, true, true, false, false, true, false, true, false];
          {
            pow_26463();
            of_pow(26496, false, true, false, true, false, false, true, true, false, false, true, true, true, true, true, false, false, false, true, true, false, false, false, false, true, false, false, false, true, true, false, true);
          }
          pow_mod_crc(26496);
        }
        calc {
          [false, true, true, false, false, false, true, false, false, true, true, true, false, true, true, false, false, false, true, true, false, true, false, true, true, true, true, false, false, false, false, false];
          {
            pow_13215();
            of_pow(13248, false, false, false, false, false, true, true, true, true, false, true, false, true, true, false, false, false, true, true, false, true, true, true, false, false, true, false, false, false, true, true, false);
          }
          pow_mod_crc(13248);
        }
      }
      pow_mod_crc(26496) + pow_mod_crc(13248);
    }
  }



  lemma lut_entry_207()
  ensures bits_of_int(lut[207] as int, 64)
      == pow_mod_crc(26624) + pow_mod_crc(13312)
  {
    calc {
      bits_of_int(lut[207] as int, 64);
      bits_of_int(3907953167556281400, 64);
      {
        lemma_bits_of_int_64_split(3907953167556281400);
      }
      bits_of_int(1594754104, 32) + bits_of_int(909891251, 32);
      {
        unroll_bits_of_int_32_0x5f0e0438();
        unroll_bits_of_int_32_0x363bd6b3();
      }
      [false, false, false, true, true, true, false, false, false, false, true, false, false, false, false, false, false, true, true, true, false, false, false, false, true, true, true, true, true, false, true, false]+[true, true, false, false, true, true, false, true, false, true, true, false, true, false, true, true, true, true, false, true, true, true, false, false, false, true, true, false, true, true, false, false];
      {
        calc {
          [false, false, false, true, true, true, false, false, false, false, true, false, false, false, false, false, false, true, true, true, false, false, false, false, true, true, true, true, true, false, true, false];
          {
            pow_26591();
            of_pow(26624, false, true, false, true, true, true, true, true, false, false, false, false, true, true, true, false, false, false, false, false, false, true, false, false, false, false, true, true, true, false, false, false);
          }
          pow_mod_crc(26624);
        }
        calc {
          [true, true, false, false, true, true, false, true, false, true, true, false, true, false, true, true, true, true, false, true, true, true, false, false, false, true, true, false, true, true, false, false];
          {
            pow_13279();
            of_pow(13312, false, false, true, true, false, true, true, false, false, false, true, true, true, false, true, true, true, true, false, true, false, true, true, false, true, false, true, true, false, false, true, true);
          }
          pow_mod_crc(13312);
        }
      }
      pow_mod_crc(26624) + pow_mod_crc(13312);
    }
  }



  lemma lut_entry_208()
  ensures bits_of_int(lut[208] as int, 64)
      == pow_mod_crc(26752) + pow_mod_crc(13376)
  {
    calc {
      bits_of_int(lut[208] as int, 64);
      bits_of_int(1583105787072179721, 64);
      {
        lemma_bits_of_int_64_split(1583105787072179721);
      }
      bits_of_int(1615687177, 32) + bits_of_int(368595539, 32);
      {
        unroll_bits_of_int_32_0x604d6e09();
        unroll_bits_of_int_32_0x15f85253();
      }
      [true, false, false, true, false, false, false, false, false, true, true, true, false, true, true, false, true, false, true, true, false, false, true, false, false, false, false, false, false, true, true, false]+[true, true, false, false, true, false, true, false, false, true, false, false, true, false, true, false, false, false, false, true, true, true, true, true, true, false, true, false, true, false, false, false];
      {
        calc {
          [true, false, false, true, false, false, false, false, false, true, true, true, false, true, true, false, true, false, true, true, false, false, true, false, false, false, false, false, false, true, true, false];
          {
            pow_26719();
            of_pow(26752, false, true, true, false, false, false, false, false, false, true, false, false, true, true, false, true, false, true, true, false, true, true, true, false, false, false, false, false, true, false, false, true);
          }
          pow_mod_crc(26752);
        }
        calc {
          [true, true, false, false, true, false, true, false, false, true, false, false, true, false, true, false, false, false, false, true, true, true, true, true, true, false, true, false, true, false, false, false];
          {
            pow_13343();
            of_pow(13376, false, false, false, true, false, true, false, true, true, true, true, true, true, false, false, false, false, true, false, true, false, false, true, false, false, true, false, true, false, false, true, true);
          }
          pow_mod_crc(13376);
        }
      }
      pow_mod_crc(26752) + pow_mod_crc(13376);
    }
  }



  lemma lut_entry_209()
  ensures bits_of_int(lut[209] as int, 64)
      == pow_mod_crc(26880) + pow_mod_crc(13440)
  {
    calc {
      bits_of_int(lut[209] as int, 64);
      bits_of_int(1395135110159001122, 64);
      {
        lemma_bits_of_int_64_split(1395135110159001122);
      }
      bits_of_int(2931025442, 32) + bits_of_int(324830205, 32);
      {
        unroll_bits_of_int_32_0xaeb3e622();
        unroll_bits_of_int_32_0x135c83fd();
      }
      [false, true, false, false, false, true, false, false, false, true, true, false, false, true, true, true, true, true, false, false, true, true, false, true, false, true, true, true, false, true, false, true]+[true, false, true, true, true, true, true, true, true, true, false, false, false, false, false, true, false, false, true, true, true, false, true, false, true, true, false, false, true, false, false, false];
      {
        calc {
          [false, true, false, false, false, true, false, false, false, true, true, false, false, true, true, true, true, true, false, false, true, true, false, true, false, true, true, true, false, true, false, true];
          {
            pow_26847();
            of_pow(26880, true, false, true, false, true, true, true, false, true, false, true, true, false, false, true, true, true, true, true, false, false, true, true, false, false, false, true, false, false, false, true, false);
          }
          pow_mod_crc(26880);
        }
        calc {
          [true, false, true, true, true, true, true, true, true, true, false, false, false, false, false, true, false, false, true, true, true, false, true, false, true, true, false, false, true, false, false, false];
          {
            pow_13407();
            of_pow(13440, false, false, false, true, false, false, true, true, false, true, false, true, true, true, false, false, true, false, false, false, false, false, true, true, true, true, true, true, true, true, false, true);
          }
          pow_mod_crc(13440);
        }
      }
      pow_mod_crc(26880) + pow_mod_crc(13440);
    }
  }



  lemma lut_entry_210()
  ensures bits_of_int(lut[210] as int, 64)
      == pow_mod_crc(27008) + pow_mod_crc(13504)
  {
    calc {
      bits_of_int(lut[210] as int, 64);
      bits_of_int(2012023666247985924, 64);
      {
        lemma_bits_of_int_64_split(2012023666247985924);
      }
      bits_of_int(1113844484, 32) + bits_of_int(468460765, 32);
      {
        unroll_bits_of_int_32_0x4263eb04();
        unroll_bits_of_int_32_0x1bec24dd();
      }
      [false, false, true, false, false, false, false, false, true, true, false, true, false, true, true, true, true, true, false, false, false, true, true, false, false, true, false, false, false, false, true, false]+[true, false, true, true, true, false, true, true, false, false, true, false, false, true, false, false, false, false, true, true, false, true, true, true, true, true, false, true, true, false, false, false];
      {
        calc {
          [false, false, true, false, false, false, false, false, true, true, false, true, false, true, true, true, true, true, false, false, false, true, true, false, false, true, false, false, false, false, true, false];
          {
            pow_26975();
            of_pow(27008, false, true, false, false, false, false, true, false, false, true, true, false, false, false, true, true, true, true, true, false, true, false, true, true, false, false, false, false, false, true, false, false);
          }
          pow_mod_crc(27008);
        }
        calc {
          [true, false, true, true, true, false, true, true, false, false, true, false, false, true, false, false, false, false, true, true, false, true, true, true, true, true, false, true, true, false, false, false];
          {
            pow_13471();
            of_pow(13504, false, false, false, true, true, false, true, true, true, true, true, false, true, true, false, false, false, false, true, false, false, true, false, false, true, true, false, true, true, true, false, true);
          }
          pow_mod_crc(13504);
        }
      }
      pow_mod_crc(27008) + pow_mod_crc(13504);
    }
  }



  lemma lut_entry_211()
  ensures bits_of_int(lut[211] as int, 64)
      == pow_mod_crc(27136) + pow_mod_crc(13568)
  {
    calc {
      bits_of_int(lut[211] as int, 64);
      bits_of_int(6893857024686344982, 64);
      {
        lemma_bits_of_int_64_split(6893857024686344982);
      }
      bits_of_int(1354943254, 32) + bits_of_int(1605101168, 32);
      {
        unroll_bits_of_int_32_0x50c2cb16();
        unroll_bits_of_int_32_0x5fabe670();
      }
      [false, true, true, false, true, false, false, false, true, true, false, true, false, false, true, true, false, true, false, false, false, false, true, true, false, false, false, false, true, false, true, false]+[false, false, false, false, true, true, true, false, false, true, true, false, false, true, true, true, true, true, false, true, false, true, false, true, true, true, true, true, true, false, true, false];
      {
        calc {
          [false, true, true, false, true, false, false, false, true, true, false, true, false, false, true, true, false, true, false, false, false, false, true, true, false, false, false, false, true, false, true, false];
          {
            pow_27103();
            of_pow(27136, false, true, false, true, false, false, false, false, true, true, false, false, false, false, true, false, true, true, false, false, true, false, true, true, false, false, false, true, false, true, true, false);
          }
          pow_mod_crc(27136);
        }
        calc {
          [false, false, false, false, true, true, true, false, false, true, true, false, false, true, true, true, true, true, false, true, false, true, false, true, true, true, true, true, true, false, true, false];
          {
            pow_13535();
            of_pow(13568, false, true, false, true, true, true, true, true, true, false, true, false, true, false, true, true, true, true, true, false, false, true, true, false, false, true, true, true, false, false, false, false);
          }
          pow_mod_crc(13568);
        }
      }
      pow_mod_crc(27136) + pow_mod_crc(13568);
    }
  }



  lemma lut_entry_212()
  ensures bits_of_int(lut[212] as int, 64)
      == pow_mod_crc(27264) + pow_mod_crc(13632)
  {
    calc {
      bits_of_int(lut[212] as int, 64);
      bits_of_int(5491802588068687847, 64);
      {
        lemma_bits_of_int_64_split(5491802588068687847);
      }
      bits_of_int(1718071271, 32) + bits_of_int(1278659931, 32);
      {
        unroll_bits_of_int_32_0x6667afe7();
        unroll_bits_of_int_32_0x4c36cd5b();
      }
      [true, true, true, false, false, true, true, true, true, true, true, true, false, true, false, true, true, true, true, false, false, true, true, false, false, true, true, false, false, true, true, false]+[true, true, false, true, true, false, true, false, true, false, true, true, false, false, true, true, false, true, true, false, true, true, false, false, false, false, true, true, false, false, true, false];
      {
        calc {
          [true, true, true, false, false, true, true, true, true, true, true, true, false, true, false, true, true, true, true, false, false, true, true, false, false, true, true, false, false, true, true, false];
          {
            pow_27231();
            of_pow(27264, false, true, true, false, false, true, true, false, false, true, true, false, false, true, true, true, true, false, true, false, true, true, true, true, true, true, true, false, false, true, true, true);
          }
          pow_mod_crc(27264);
        }
        calc {
          [true, true, false, true, true, false, true, false, true, false, true, true, false, false, true, true, false, true, true, false, true, true, false, false, false, false, true, true, false, false, true, false];
          {
            pow_13599();
            of_pow(13632, false, true, false, false, true, true, false, false, false, false, true, true, false, true, true, false, true, true, false, false, true, true, false, true, false, true, false, true, true, false, true, true);
          }
          pow_mod_crc(13632);
        }
      }
      pow_mod_crc(27264) + pow_mod_crc(13632);
    }
  }



  lemma lut_entry_213()
  ensures bits_of_int(lut[213] as int, 64)
      == pow_mod_crc(27392) + pow_mod_crc(13696)
  {
    calc {
      bits_of_int(lut[213] as int, 64);
      bits_of_int(3885536074229385656, 64);
      {
        lemma_bits_of_int_64_split(3885536074229385656);
      }
      bits_of_int(443058616, 32) + bits_of_int(904671865, 32);
      {
        unroll_bits_of_int_32_0x1a6889b8();
        unroll_bits_of_int_32_0x35ec3279();
      }
      [false, false, false, true, true, true, false, true, true, false, false, true, false, false, false, true, false, false, false, true, false, true, true, false, false, true, false, true, true, false, false, false]+[true, false, false, true, true, true, true, false, false, true, false, false, true, true, false, false, false, false, true, true, false, true, true, true, true, false, true, false, true, true, false, false];
      {
        calc {
          [false, false, false, true, true, true, false, true, true, false, false, true, false, false, false, true, false, false, false, true, false, true, true, false, false, true, false, true, true, false, false, false];
          {
            pow_27359();
            of_pow(27392, false, false, false, true, true, false, true, false, false, true, true, false, true, false, false, false, true, false, false, false, true, false, false, true, true, false, true, true, true, false, false, false);
          }
          pow_mod_crc(27392);
        }
        calc {
          [true, false, false, true, true, true, true, false, false, true, false, false, true, true, false, false, false, false, true, true, false, true, true, true, true, false, true, false, true, true, false, false];
          {
            pow_13663();
            of_pow(13696, false, false, true, true, false, true, false, true, true, true, true, false, true, true, false, false, false, false, true, true, false, false, true, false, false, true, true, true, true, false, false, true);
          }
          pow_mod_crc(13696);
        }
      }
      pow_mod_crc(27392) + pow_mod_crc(13696);
    }
  }



  lemma lut_entry_214()
  ensures bits_of_int(lut[214] as int, 64)
      == pow_mod_crc(27520) + pow_mod_crc(13760)
  {
    calc {
      bits_of_int(lut[214] as int, 64);
      bits_of_int(16186550768080439594, 64);
      {
        lemma_bits_of_int_64_split(16186550768080439594);
      }
      bits_of_int(3728918826, 32) + bits_of_int(3768725033, 32);
      {
        unroll_bits_of_int_32_0xde42c92a();
        unroll_bits_of_int_32_0xe0a22e29();
      }
      [false, true, false, true, false, true, false, false, true, false, false, true, false, false, true, true, false, true, false, false, false, false, true, false, false, true, true, true, true, false, true, true]+[true, false, false, true, false, true, false, false, false, true, true, true, false, true, false, false, false, true, false, false, false, true, false, true, false, false, false, false, false, true, true, true];
      {
        calc {
          [false, true, false, true, false, true, false, false, true, false, false, true, false, false, true, true, false, true, false, false, false, false, true, false, false, true, true, true, true, false, true, true];
          {
            pow_27487();
            of_pow(27520, true, true, false, true, true, true, true, false, false, true, false, false, false, false, true, false, true, true, false, false, true, false, false, true, false, false, true, false, true, false, true, false);
          }
          pow_mod_crc(27520);
        }
        calc {
          [true, false, false, true, false, true, false, false, false, true, true, true, false, true, false, false, false, true, false, false, false, true, false, true, false, false, false, false, false, true, true, true];
          {
            pow_13727();
            of_pow(13760, true, true, true, false, false, false, false, false, true, false, true, false, false, false, true, false, false, false, true, false, true, true, true, false, false, false, true, false, true, false, false, true);
          }
          pow_mod_crc(13760);
        }
      }
      pow_mod_crc(27520) + pow_mod_crc(13760);
    }
  }



  lemma lut_entry_215()
  ensures bits_of_int(lut[215] as int, 64)
      == pow_mod_crc(27648) + pow_mod_crc(13824)
  {
    calc {
      bits_of_int(lut[215] as int, 64);
      bits_of_int(53187734667740733, 64);
      {
        lemma_bits_of_int_64_split(53187734667740733);
      }
      bits_of_int(2135377469, 32) + bits_of_int(12383734, 32);
      {
        unroll_bits_of_int_32_0x7f47463d();
        unroll_bits_of_int_32_0x00bcf5f6();
      }
      [true, false, true, true, true, true, false, false, false, true, true, false, false, false, true, false, true, true, true, false, false, false, true, false, true, true, true, true, true, true, true, false]+[false, true, true, false, true, true, true, true, true, false, true, false, true, true, true, true, false, false, true, true, true, true, false, true, false, false, false, false, false, false, false, false];
      {
        calc {
          [true, false, true, true, true, true, false, false, false, true, true, false, false, false, true, false, true, true, true, false, false, false, true, false, true, true, true, true, true, true, true, false];
          {
            pow_27615();
            of_pow(27648, false, true, true, true, true, true, true, true, false, true, false, false, false, true, true, true, false, true, false, false, false, true, true, false, false, false, true, true, true, true, false, true);
          }
          pow_mod_crc(27648);
        }
        calc {
          [false, true, true, false, true, true, true, true, true, false, true, false, true, true, true, true, false, false, true, true, true, true, false, true, false, false, false, false, false, false, false, false];
          {
            pow_13791();
            of_pow(13824, false, false, false, false, false, false, false, false, true, false, true, true, true, true, false, false, true, true, true, true, false, true, false, true, true, true, true, true, false, true, true, false);
          }
          pow_mod_crc(13824);
        }
      }
      pow_mod_crc(27648) + pow_mod_crc(13824);
    }
  }



  lemma lut_entry_216()
  ensures bits_of_int(lut[216] as int, 64)
      == pow_mod_crc(27776) + pow_mod_crc(13888)
  {
    calc {
      bits_of_int(lut[216] as int, 64);
      bits_of_int(8947366966078431360, 64);
      {
        lemma_bits_of_int_64_split(8947366966078431360);
      }
      bits_of_int(3089850496, 32) + bits_of_int(2083221209, 32);
      {
        unroll_bits_of_int_32_0xb82b6080();
        unroll_bits_of_int_32_0x7c2b6ed9();
      }
      [false, false, false, false, false, false, false, true, false, false, false, false, false, true, true, false, true, true, false, true, false, true, false, false, false, false, false, true, true, true, false, true]+[true, false, false, true, true, false, true, true, false, true, true, true, false, true, true, false, true, true, false, true, false, true, false, false, false, false, true, true, true, true, true, false];
      {
        calc {
          [false, false, false, false, false, false, false, true, false, false, false, false, false, true, true, false, true, true, false, true, false, true, false, false, false, false, false, true, true, true, false, true];
          {
            pow_27743();
            of_pow(27776, true, false, true, true, true, false, false, false, false, false, true, false, true, false, true, true, false, true, true, false, false, false, false, false, true, false, false, false, false, false, false, false);
          }
          pow_mod_crc(27776);
        }
        calc {
          [true, false, false, true, true, false, true, true, false, true, true, true, false, true, true, false, true, true, false, true, false, true, false, false, false, false, true, true, true, true, true, false];
          {
            pow_13855();
            of_pow(13888, false, true, true, true, true, true, false, false, false, false, true, false, true, false, true, true, false, true, true, false, true, true, true, false, true, true, false, true, true, false, false, true);
          }
          pow_mod_crc(13888);
        }
      }
      pow_mod_crc(27776) + pow_mod_crc(13888);
    }
  }



  lemma lut_entry_217()
  ensures bits_of_int(lut[217] as int, 64)
      == pow_mod_crc(27904) + pow_mod_crc(13952)
  {
    calc {
      bits_of_int(lut[217] as int, 64);
      bits_of_int(10007005559687828747, 64);
      {
        lemma_bits_of_int_64_split(10007005559687828747);
      }
      bits_of_int(2190300427, 32) + bits_of_int(2329937545, 32);
      {
        unroll_bits_of_int_32_0x828d550b();
        unroll_bits_of_int_32_0x8ae00689();
      }
      [true, true, false, true, false, false, false, false, true, false, true, false, true, false, true, false, true, false, true, true, false, false, false, true, false, true, false, false, false, false, false, true]+[true, false, false, true, false, false, false, true, false, true, true, false, false, false, false, false, false, false, false, false, false, true, true, true, false, true, false, true, false, false, false, true];
      {
        calc {
          [true, true, false, true, false, false, false, false, true, false, true, false, true, false, true, false, true, false, true, true, false, false, false, true, false, true, false, false, false, false, false, true];
          {
            pow_27871();
            of_pow(27904, true, false, false, false, false, false, true, false, true, false, false, false, true, true, false, true, false, true, false, true, false, true, false, true, false, false, false, false, true, false, true, true);
          }
          pow_mod_crc(27904);
        }
        calc {
          [true, false, false, true, false, false, false, true, false, true, true, false, false, false, false, false, false, false, false, false, false, true, true, true, false, true, false, true, false, false, false, true];
          {
            pow_13919();
            of_pow(13952, true, false, false, false, true, false, true, false, true, true, true, false, false, false, false, false, false, false, false, false, false, true, true, false, true, false, false, false, true, false, false, true);
          }
          pow_mod_crc(13952);
        }
      }
      pow_mod_crc(27904) + pow_mod_crc(13952);
    }
  }



  lemma lut_entry_218()
  ensures bits_of_int(lut[218] as int, 64)
      == pow_mod_crc(28032) + pow_mod_crc(14016)
  {
    calc {
      bits_of_int(lut[218] as int, 64);
      bits_of_int(504272307198538970, 64);
      {
        lemma_bits_of_int_64_split(504272307198538970);
      }
      bits_of_int(3701650650, 32) + bits_of_int(117410045, 32);
      {
        unroll_bits_of_int_32_0xdca2b4da();
        unroll_bits_of_int_32_0x06ff88fd();
      }
      [false, true, false, true, true, false, true, true, false, false, true, false, true, true, false, true, false, true, false, false, false, true, false, true, false, false, true, true, true, false, true, true]+[true, false, true, true, true, true, true, true, false, false, false, true, false, false, false, true, true, true, true, true, true, true, true, true, false, true, true, false, false, false, false, false];
      {
        calc {
          [false, true, false, true, true, false, true, true, false, false, true, false, true, true, false, true, false, true, false, false, false, true, false, true, false, false, true, true, true, false, true, true];
          {
            pow_27999();
            of_pow(28032, true, true, false, true, true, true, false, false, true, false, true, false, false, false, true, false, true, false, true, true, false, true, false, false, true, true, false, true, true, false, true, false);
          }
          pow_mod_crc(28032);
        }
        calc {
          [true, false, true, true, true, true, true, true, false, false, false, true, false, false, false, true, true, true, true, true, true, true, true, true, false, true, true, false, false, false, false, false];
          {
            pow_13983();
            of_pow(14016, false, false, false, false, false, true, true, false, true, true, true, true, true, true, true, true, true, false, false, false, true, false, false, false, true, true, true, true, true, true, false, true);
          }
          pow_mod_crc(14016);
        }
      }
      pow_mod_crc(28032) + pow_mod_crc(14016);
    }
  }



  lemma lut_entry_219()
  ensures bits_of_int(lut[219] as int, 64)
      == pow_mod_crc(28160) + pow_mod_crc(14080)
  {
    calc {
      bits_of_int(lut[219] as int, 64);
      bits_of_int(1725572003697993451, 64);
      {
        lemma_bits_of_int_64_split(1725572003697993451);
      }
      bits_of_int(1254565611, 32) + bits_of_int(401766040, 32);
      {
        unroll_bits_of_int_32_0x4ac726eb();
        unroll_bits_of_int_32_0x17f27698();
      }
      [true, true, false, true, false, true, true, true, false, true, true, false, false, true, false, false, true, true, true, false, false, false, true, true, false, true, false, true, false, false, true, false]+[false, false, false, true, true, false, false, true, false, true, true, false, true, true, true, false, false, true, false, false, true, true, true, true, true, true, true, false, true, false, false, false];
      {
        calc {
          [true, true, false, true, false, true, true, true, false, true, true, false, false, true, false, false, true, true, true, false, false, false, true, true, false, true, false, true, false, false, true, false];
          {
            pow_28127();
            of_pow(28160, false, true, false, false, true, false, true, false, true, true, false, false, false, true, true, true, false, false, true, false, false, true, true, false, true, true, true, false, true, false, true, true);
          }
          pow_mod_crc(28160);
        }
        calc {
          [false, false, false, true, true, false, false, true, false, true, true, false, true, true, true, false, false, true, false, false, true, true, true, true, true, true, true, false, true, false, false, false];
          {
            pow_14047();
            of_pow(14080, false, false, false, true, false, true, true, true, true, true, true, true, false, false, true, false, false, true, true, true, false, true, true, false, true, false, false, true, true, false, false, false);
          }
          pow_mod_crc(14080);
        }
      }
      pow_mod_crc(28160) + pow_mod_crc(14080);
    }
  }



  lemma lut_entry_220()
  ensures bits_of_int(lut[220] as int, 64)
      == pow_mod_crc(28288) + pow_mod_crc(14144)
  {
    calc {
      bits_of_int(lut[220] as int, 64);
      bits_of_int(17812155372846355942, 64);
      {
        lemma_bits_of_int_64_split(17812155372846355942);
      }
      bits_of_int(1385338342, 32) + bits_of_int(4147215600, 32);
      {
        unroll_bits_of_int_32_0x529295e6();
        unroll_bits_of_int_32_0xf7317cf0();
      }
      [false, true, true, false, false, true, true, true, true, false, true, false, true, false, false, true, false, true, false, false, true, false, false, true, false, true, false, false, true, false, true, false]+[false, false, false, false, true, true, true, true, false, false, true, true, true, true, true, false, true, false, false, false, true, true, false, false, true, true, true, false, true, true, true, true];
      {
        calc {
          [false, true, true, false, false, true, true, true, true, false, true, false, true, false, false, true, false, true, false, false, true, false, false, true, false, true, false, false, true, false, true, false];
          {
            pow_28255();
            of_pow(28288, false, true, false, true, false, false, true, false, true, false, false, true, false, false, true, false, true, false, false, true, false, true, false, true, true, true, true, false, false, true, true, false);
          }
          pow_mod_crc(28288);
        }
        calc {
          [false, false, false, false, true, true, true, true, false, false, true, true, true, true, true, false, true, false, false, false, true, true, false, false, true, true, true, false, true, true, true, true];
          {
            pow_14111();
            of_pow(14144, true, true, true, true, false, true, true, true, false, false, true, true, false, false, false, true, false, true, true, true, true, true, false, false, true, true, true, true, false, false, false, false);
          }
          pow_mod_crc(14144);
        }
      }
      pow_mod_crc(28288) + pow_mod_crc(14144);
    }
  }



  lemma lut_entry_221()
  ensures bits_of_int(lut[221] as int, 64)
      == pow_mod_crc(28416) + pow_mod_crc(14208)
  {
    calc {
      bits_of_int(lut[221] as int, 64);
      bits_of_int(6398030675825338603, 64);
      {
        lemma_bits_of_int_64_split(6398030675825338603);
      }
      bits_of_int(1587489003, 32) + bits_of_int(1489657600, 32);
      {
        unroll_bits_of_int_32_0x5e9f28eb();
        unroll_bits_of_int_32_0x58ca5f00();
      }
      [true, true, false, true, false, true, true, true, false, false, false, true, false, true, false, false, true, true, true, true, true, false, false, true, false, true, true, true, true, false, true, false]+[false, false, false, false, false, false, false, false, true, true, true, true, true, false, true, false, false, true, false, true, false, false, true, true, false, false, false, true, true, false, true, false];
      {
        calc {
          [true, true, false, true, false, true, true, true, false, false, false, true, false, true, false, false, true, true, true, true, true, false, false, true, false, true, true, true, true, false, true, false];
          {
            pow_28383();
            of_pow(28416, false, true, false, true, true, true, true, false, true, false, false, true, true, true, true, true, false, false, true, false, true, false, false, false, true, true, true, false, true, false, true, true);
          }
          pow_mod_crc(28416);
        }
        calc {
          [false, false, false, false, false, false, false, false, true, true, true, true, true, false, true, false, false, true, false, true, false, false, true, true, false, false, false, true, true, false, true, false];
          {
            pow_14175();
            of_pow(14208, false, true, false, true, true, false, false, false, true, true, false, false, true, false, true, false, false, true, false, true, true, true, true, true, false, false, false, false, false, false, false, false);
          }
          pow_mod_crc(14208);
        }
      }
      pow_mod_crc(28416) + pow_mod_crc(14208);
    }
  }



  lemma lut_entry_222()
  ensures bits_of_int(lut[222] as int, 64)
      == pow_mod_crc(28544) + pow_mod_crc(14272)
  {
    calc {
      bits_of_int(lut[222] as int, 64);
      bits_of_int(7041065804422533119, 64);
      {
        lemma_bits_of_int_64_split(7041065804422533119);
      }
      bits_of_int(1086410751, 32) + bits_of_int(1639375883, 32);
      {
        unroll_bits_of_int_32_0x40c14fff();
        unroll_bits_of_int_32_0x61b6e40b();
      }
      [true, true, true, true, true, true, true, true, true, true, true, true, false, false, true, false, true, false, false, false, false, false, true, true, false, false, false, false, false, false, true, false]+[true, true, false, true, false, false, false, false, false, false, true, false, false, true, true, true, false, true, true, false, true, true, false, true, true, false, false, false, false, true, true, false];
      {
        calc {
          [true, true, true, true, true, true, true, true, true, true, true, true, false, false, true, false, true, false, false, false, false, false, true, true, false, false, false, false, false, false, true, false];
          {
            pow_28511();
            of_pow(28544, false, true, false, false, false, false, false, false, true, true, false, false, false, false, false, true, false, true, false, false, true, true, true, true, true, true, true, true, true, true, true, true);
          }
          pow_mod_crc(28544);
        }
        calc {
          [true, true, false, true, false, false, false, false, false, false, true, false, false, true, true, true, false, true, true, false, true, true, false, true, true, false, false, false, false, true, true, false];
          {
            pow_14239();
            of_pow(14272, false, true, true, false, false, false, false, true, true, false, true, true, false, true, true, false, true, true, true, false, false, true, false, false, false, false, false, false, true, false, true, true);
          }
          pow_mod_crc(14272);
        }
      }
      pow_mod_crc(28544) + pow_mod_crc(14272);
    }
  }



  lemma lut_entry_223()
  ensures bits_of_int(lut[223] as int, 64)
      == pow_mod_crc(28672) + pow_mod_crc(14336)
  {
    calc {
      bits_of_int(lut[223] as int, 64);
      bits_of_int(12284828941333688731, 64);
      {
        lemma_bits_of_int_64_split(12284828941333688731);
      }
      bits_of_int(2527195547, 32) + bits_of_int(2860284629, 32);
      {
        unroll_bits_of_int_32_0x96a1f19b();
        unroll_bits_of_int_32_0xaa7c7ad5();
      }
      [true, true, false, true, true, false, false, true, true, false, false, false, true, true, true, true, true, false, false, false, false, true, false, true, false, true, true, false, true, false, false, true]+[true, false, true, false, true, false, true, true, false, true, false, true, true, true, true, false, false, false, true, true, true, true, true, false, false, true, false, true, false, true, false, true];
      {
        calc {
          [true, true, false, true, true, false, false, true, true, false, false, false, true, true, true, true, true, false, false, false, false, true, false, true, false, true, true, false, true, false, false, true];
          {
            pow_28639();
            of_pow(28672, true, false, false, true, false, true, true, false, true, false, true, false, false, false, false, true, true, true, true, true, false, false, false, true, true, false, false, true, true, false, true, true);
          }
          pow_mod_crc(28672);
        }
        calc {
          [true, false, true, false, true, false, true, true, false, true, false, true, true, true, true, false, false, false, true, true, true, true, true, false, false, true, false, true, false, true, false, true];
          {
            pow_14303();
            of_pow(14336, true, false, true, false, true, false, true, false, false, true, true, true, true, true, false, false, false, true, true, true, true, false, true, false, true, true, false, true, false, true, false, true);
          }
          pow_mod_crc(14336);
        }
      }
      pow_mod_crc(28672) + pow_mod_crc(14336);
    }
  }



  lemma lut_entry_224()
  ensures bits_of_int(lut[224] as int, 64)
      == pow_mod_crc(28800) + pow_mod_crc(14400)
  {
    calc {
      bits_of_int(lut[224] as int, 64);
      bits_of_int(16035796517188098017, 64);
      {
        lemma_bits_of_int_64_split(16035796517188098017);
      }
      bits_of_int(2574342113, 32) + bits_of_int(3733624824, 32);
      {
        unroll_bits_of_int_32_0x997157e1();
        unroll_bits_of_int_32_0xde8a97f8();
      }
      [true, false, false, false, false, true, true, true, true, true, true, false, true, false, true, false, true, false, false, false, true, true, true, false, true, false, false, true, true, false, false, true]+[false, false, false, true, true, true, true, true, true, true, true, false, true, false, false, true, false, true, false, true, false, false, false, true, false, true, true, true, true, false, true, true];
      {
        calc {
          [true, false, false, false, false, true, true, true, true, true, true, false, true, false, true, false, true, false, false, false, true, true, true, false, true, false, false, true, true, false, false, true];
          {
            pow_28767();
            of_pow(28800, true, false, false, true, true, false, false, true, false, true, true, true, false, false, false, true, false, true, false, true, false, true, true, true, true, true, true, false, false, false, false, true);
          }
          pow_mod_crc(28800);
        }
        calc {
          [false, false, false, true, true, true, true, true, true, true, true, false, true, false, false, true, false, true, false, true, false, false, false, true, false, true, true, true, true, false, true, true];
          {
            pow_14367();
            of_pow(14400, true, true, false, true, true, true, true, false, true, false, false, false, true, false, true, false, true, false, false, true, false, true, true, true, true, true, true, true, true, false, false, false);
          }
          pow_mod_crc(14400);
        }
      }
      pow_mod_crc(28800) + pow_mod_crc(14400);
    }
  }



  lemma lut_entry_225()
  ensures bits_of_int(lut[225] as int, 64)
      == pow_mod_crc(28928) + pow_mod_crc(14464)
  {
    calc {
      bits_of_int(lut[225] as int, 64);
      bits_of_int(13100912117159920022, 64);
      {
        lemma_bits_of_int_64_split(13100912117159920022);
      }
      bits_of_int(2968355222, 32) + bits_of_int(3050293800, 32);
      {
        unroll_bits_of_int_32_0xb0ed8196();
        unroll_bits_of_int_32_0xb5cfca28();
      }
      [false, true, true, false, true, false, false, true, true, false, false, false, false, false, false, true, true, false, true, true, false, true, true, true, false, false, false, false, true, true, false, true]+[false, false, false, true, false, true, false, false, false, true, false, true, false, false, true, true, true, true, true, true, false, false, true, true, true, false, true, false, true, true, false, true];
      {
        calc {
          [false, true, true, false, true, false, false, true, true, false, false, false, false, false, false, true, true, false, true, true, false, true, true, true, false, false, false, false, true, true, false, true];
          {
            pow_28895();
            of_pow(28928, true, false, true, true, false, false, false, false, true, true, true, false, true, true, false, true, true, false, false, false, false, false, false, true, true, false, false, true, false, true, true, false);
          }
          pow_mod_crc(28928);
        }
        calc {
          [false, false, false, true, false, true, false, false, false, true, false, true, false, false, true, true, true, true, true, true, false, false, true, true, true, false, true, false, true, true, false, true];
          {
            pow_14431();
            of_pow(14464, true, false, true, true, false, true, false, true, true, true, false, false, true, true, true, true, true, true, false, false, true, false, true, false, false, false, true, false, true, false, false, false);
          }
          pow_mod_crc(14464);
        }
      }
      pow_mod_crc(28928) + pow_mod_crc(14464);
    }
  }



  lemma lut_entry_226()
  ensures bits_of_int(lut[226] as int, 64)
      == pow_mod_crc(29056) + pow_mod_crc(14528)
  {
    calc {
      bits_of_int(lut[226] as int, 64);
      bits_of_int(9869097920173588966, 64);
      {
        lemma_bits_of_int_64_split(9869097920173588966);
      }
      bits_of_int(159269350, 32) + bits_of_int(2297828421, 32);
      {
        unroll_bits_of_int_32_0x097e41e6();
        unroll_bits_of_int_32_0x88f61445();
      }
      [false, true, true, false, false, true, true, true, true, false, false, false, false, false, true, false, false, true, true, true, true, true, true, false, true, false, false, true, false, false, false, false]+[true, false, true, false, false, false, true, false, false, false, true, false, true, false, false, false, false, true, true, false, true, true, true, true, false, false, false, true, false, false, false, true];
      {
        calc {
          [false, true, true, false, false, true, true, true, true, false, false, false, false, false, true, false, false, true, true, true, true, true, true, false, true, false, false, true, false, false, false, false];
          {
            pow_29023();
            of_pow(29056, false, false, false, false, true, false, false, true, false, true, true, true, true, true, true, false, false, true, false, false, false, false, false, true, true, true, true, false, false, true, true, false);
          }
          pow_mod_crc(29056);
        }
        calc {
          [true, false, true, false, false, false, true, false, false, false, true, false, true, false, false, false, false, true, true, false, true, true, true, true, false, false, false, true, false, false, false, true];
          {
            pow_14495();
            of_pow(14528, true, false, false, false, true, false, false, false, true, true, true, true, false, true, true, false, false, false, false, true, false, true, false, false, false, true, false, false, false, true, false, true);
          }
          pow_mod_crc(14528);
        }
      }
      pow_mod_crc(29056) + pow_mod_crc(14528);
    }
  }



  lemma lut_entry_227()
  ensures bits_of_int(lut[227] as int, 64)
      == pow_mod_crc(29184) + pow_mod_crc(14592)
  {
    calc {
      bits_of_int(lut[227] as int, 64);
      bits_of_int(16056046221552828389, 64);
      {
        lemma_bits_of_int_64_split(16056046221552828389);
      }
      bits_of_int(1290321893, 32) + bits_of_int(3738339576, 32);
      {
        unroll_bits_of_int_32_0x4ce8bfe5();
        unroll_bits_of_int_32_0xded288f8();
      }
      [true, false, true, false, false, true, true, true, true, true, true, true, true, true, false, true, false, false, false, true, false, true, true, true, false, false, true, true, false, false, true, false]+[false, false, false, true, true, true, true, true, false, false, false, true, false, false, false, true, false, true, false, false, true, false, true, true, false, true, true, true, true, false, true, true];
      {
        calc {
          [true, false, true, false, false, true, true, true, true, true, true, true, true, true, false, true, false, false, false, true, false, true, true, true, false, false, true, true, false, false, true, false];
          {
            pow_29151();
            of_pow(29184, false, true, false, false, true, true, false, false, true, true, true, false, true, false, false, false, true, false, true, true, true, true, true, true, true, true, true, false, false, true, false, true);
          }
          pow_mod_crc(29184);
        }
        calc {
          [false, false, false, true, true, true, true, true, false, false, false, true, false, false, false, true, false, true, false, false, true, false, true, true, false, true, true, true, true, false, true, true];
          {
            pow_14559();
            of_pow(14592, true, true, false, true, true, true, true, false, true, true, false, true, false, false, true, false, true, false, false, false, true, false, false, false, true, true, true, true, true, false, false, false);
          }
          pow_mod_crc(14592);
        }
      }
      pow_mod_crc(29184) + pow_mod_crc(14592);
    }
  }



  lemma lut_entry_228()
  ensures bits_of_int(lut[228] as int, 64)
      == pow_mod_crc(29312) + pow_mod_crc(14656)
  {
    calc {
      bits_of_int(lut[228] as int, 64);
      bits_of_int(15299306959713878445, 64);
      {
        lemma_bits_of_int_64_split(15299306959713878445);
      }
      bits_of_int(3815260589, 32) + bits_of_int(3562147486, 32);
      {
        unroll_bits_of_int_32_0xe36841ad();
        unroll_bits_of_int_32_0xd4520e9e();
      }
      [true, false, true, true, false, true, false, true, true, false, false, false, false, false, true, false, false, false, false, true, false, true, true, false, true, true, false, false, false, true, true, true]+[false, true, true, true, true, false, false, true, false, true, true, true, false, false, false, false, false, true, false, false, true, false, true, false, false, false, true, false, true, false, true, true];
      {
        calc {
          [true, false, true, true, false, true, false, true, true, false, false, false, false, false, true, false, false, false, false, true, false, true, true, false, true, true, false, false, false, true, true, true];
          {
            pow_29279();
            of_pow(29312, true, true, true, false, false, false, true, true, false, true, true, false, true, false, false, false, false, true, false, false, false, false, false, true, true, false, true, false, true, true, false, true);
          }
          pow_mod_crc(29312);
        }
        calc {
          [false, true, true, true, true, false, false, true, false, true, true, true, false, false, false, false, false, true, false, false, true, false, true, false, false, false, true, false, true, false, true, true];
          {
            pow_14623();
            of_pow(14656, true, true, false, true, false, true, false, false, false, true, false, true, false, false, true, false, false, false, false, false, true, true, true, false, true, false, false, true, true, true, true, false);
          }
          pow_mod_crc(14656);
        }
      }
      pow_mod_crc(29312) + pow_mod_crc(14656);
    }
  }



  lemma lut_entry_229()
  ensures bits_of_int(lut[229] as int, 64)
      == pow_mod_crc(29440) + pow_mod_crc(14720)
  {
    calc {
      bits_of_int(lut[229] as int, 64);
      bits_of_int(6481288704687686268, 64);
      {
        lemma_bits_of_int_64_split(6481288704687686268);
      }
      bits_of_int(3517530748, 32) + bits_of_int(1509042620, 32);
      {
        unroll_bits_of_int_32_0xd1a9427c();
        unroll_bits_of_int_32_0x59f229bc();
      }
      [false, false, true, true, true, true, true, false, false, true, false, false, false, false, true, false, true, false, false, true, false, true, false, true, true, false, false, false, true, false, true, true]+[false, false, true, true, true, true, false, true, true, false, false, true, false, true, false, false, false, true, false, false, true, true, true, true, true, false, false, true, true, false, true, false];
      {
        calc {
          [false, false, true, true, true, true, true, false, false, true, false, false, false, false, true, false, true, false, false, true, false, true, false, true, true, false, false, false, true, false, true, true];
          {
            pow_29407();
            of_pow(29440, true, true, false, true, false, false, false, true, true, false, true, false, true, false, false, true, false, true, false, false, false, false, true, false, false, true, true, true, true, true, false, false);
          }
          pow_mod_crc(29440);
        }
        calc {
          [false, false, true, true, true, true, false, true, true, false, false, true, false, true, false, false, false, true, false, false, true, true, true, true, true, false, false, true, true, false, true, false];
          {
            pow_14687();
            of_pow(14720, false, true, false, true, true, false, false, true, true, true, true, true, false, false, true, false, false, false, true, false, true, false, false, true, true, false, true, true, true, true, false, false);
          }
          pow_mod_crc(14720);
        }
      }
      pow_mod_crc(29440) + pow_mod_crc(14720);
    }
  }



  lemma lut_entry_230()
  ensures bits_of_int(lut[230] as int, 64)
      == pow_mod_crc(29568) + pow_mod_crc(14784)
  {
    calc {
      bits_of_int(lut[230] as int, 64);
      bits_of_int(889790597692600732, 64);
      {
        lemma_bits_of_int_64_split(889790597692600732);
      }
      bits_of_int(2482188700, 32) + bits_of_int(207170517, 32);
      {
        unroll_bits_of_int_32_0x93f3319c();
        unroll_bits_of_int_32_0x0c592bd5();
      }
      [false, false, true, true, true, false, false, true, true, false, false, false, true, true, false, false, true, true, false, false, true, true, true, true, true, true, false, false, true, false, false, true]+[true, false, true, false, true, false, true, true, true, true, false, true, false, true, false, false, true, false, false, true, true, false, true, false, false, false, true, true, false, false, false, false];
      {
        calc {
          [false, false, true, true, true, false, false, true, true, false, false, false, true, true, false, false, true, true, false, false, true, true, true, true, true, true, false, false, true, false, false, true];
          {
            pow_29535();
            of_pow(29568, true, false, false, true, false, false, true, true, true, true, true, true, false, false, true, true, false, false, true, true, false, false, false, true, true, false, false, true, true, true, false, false);
          }
          pow_mod_crc(29568);
        }
        calc {
          [true, false, true, false, true, false, true, true, true, true, false, true, false, true, false, false, true, false, false, true, true, false, true, false, false, false, true, true, false, false, false, false];
          {
            pow_14751();
            of_pow(14784, false, false, false, false, true, true, false, false, false, true, false, true, true, false, false, true, false, false, true, false, true, false, true, true, true, true, false, true, false, true, false, true);
          }
          pow_mod_crc(14784);
        }
      }
      pow_mod_crc(29568) + pow_mod_crc(14784);
    }
  }



  lemma lut_entry_231()
  ensures bits_of_int(lut[231] as int, 64)
      == pow_mod_crc(29696) + pow_mod_crc(14848)
  {
    calc {
      bits_of_int(lut[231] as int, 64);
      bits_of_int(7870337134115866366, 64);
      {
        lemma_bits_of_int_64_split(7870337134115866366);
      }
      bits_of_int(3045771006, 32) + bits_of_int(1832455660, 32);
      {
        unroll_bits_of_int_32_0xb58ac6fe();
        unroll_bits_of_int_32_0x6d390dec();
      }
      [false, true, true, true, true, true, true, true, false, true, true, false, false, false, true, true, false, true, false, true, false, false, false, true, true, false, true, false, true, true, false, true]+[false, false, true, true, false, true, true, true, true, false, true, true, false, false, false, false, true, false, false, true, true, true, false, false, true, false, true, true, false, true, true, false];
      {
        calc {
          [false, true, true, true, true, true, true, true, false, true, true, false, false, false, true, true, false, true, false, true, false, false, false, true, true, false, true, false, true, true, false, true];
          {
            pow_29663();
            of_pow(29696, true, false, true, true, false, true, false, true, true, false, false, false, true, false, true, false, true, true, false, false, false, true, true, false, true, true, true, true, true, true, true, false);
          }
          pow_mod_crc(29696);
        }
        calc {
          [false, false, true, true, false, true, true, true, true, false, true, true, false, false, false, false, true, false, false, true, true, true, false, false, true, false, true, true, false, true, true, false];
          {
            pow_14815();
            of_pow(14848, false, true, true, false, true, true, false, true, false, false, true, true, true, false, false, true, false, false, false, false, true, true, false, true, true, true, true, false, true, true, false, false);
          }
          pow_mod_crc(14848);
        }
      }
      pow_mod_crc(29696) + pow_mod_crc(14848);
    }
  }



  lemma lut_entry_232()
  ensures bits_of_int(lut[232] as int, 64)
      == pow_mod_crc(29824) + pow_mod_crc(14912)
  {
    calc {
      bits_of_int(lut[232] as int, 64);
      bits_of_int(4102210761005240897, 64);
      {
        lemma_bits_of_int_64_split(4102210761005240897);
      }
      bits_of_int(3816854081, 32) + bits_of_int(955120371, 32);
      {
        unroll_bits_of_int_32_0xe3809241();
        unroll_bits_of_int_32_0x38edfaf3();
      }
      [true, false, false, false, false, false, true, false, false, true, false, false, true, false, false, true, false, false, false, false, false, false, false, true, true, true, false, false, false, true, true, true]+[true, true, false, false, true, true, true, true, false, true, false, true, true, true, true, true, true, false, true, true, false, true, true, true, false, false, false, true, true, true, false, false];
      {
        calc {
          [true, false, false, false, false, false, true, false, false, true, false, false, true, false, false, true, false, false, false, false, false, false, false, true, true, true, false, false, false, true, true, true];
          {
            pow_29791();
            of_pow(29824, true, true, true, false, false, false, true, true, true, false, false, false, false, false, false, false, true, false, false, true, false, false, true, false, false, true, false, false, false, false, false, true);
          }
          pow_mod_crc(29824);
        }
        calc {
          [true, true, false, false, true, true, true, true, false, true, false, true, true, true, true, true, true, false, true, true, false, true, true, true, false, false, false, true, true, true, false, false];
          {
            pow_14879();
            of_pow(14912, false, false, true, true, true, false, false, false, true, true, true, false, true, true, false, true, true, true, true, true, true, false, true, false, true, true, true, true, false, false, true, true);
          }
          pow_mod_crc(14912);
        }
      }
      pow_mod_crc(29824) + pow_mod_crc(14912);
    }
  }



  lemma lut_entry_233()
  ensures bits_of_int(lut[233] as int, 64)
      == pow_mod_crc(29952) + pow_mod_crc(14976)
  {
    calc {
      bits_of_int(lut[233] as int, 64);
      bits_of_int(3969645517623776226, 64);
      {
        lemma_bits_of_int_64_split(3969645517623776226);
      }
      bits_of_int(4063220706, 32) + bits_of_int(924255120, 32);
      {
        unroll_bits_of_int_32_0xf22fd3e2();
        unroll_bits_of_int_32_0x37170390();
      }
      [false, true, false, false, false, true, true, true, true, true, false, false, true, false, true, true, true, true, true, true, false, true, false, false, false, true, false, false, true, true, true, true]+[false, false, false, false, true, false, false, true, true, true, false, false, false, false, false, false, true, true, true, false, true, false, false, false, true, true, true, false, true, true, false, false];
      {
        calc {
          [false, true, false, false, false, true, true, true, true, true, false, false, true, false, true, true, true, true, true, true, false, true, false, false, false, true, false, false, true, true, true, true];
          {
            pow_29919();
            of_pow(29952, true, true, true, true, false, false, true, false, false, false, true, false, true, true, true, true, true, true, false, true, false, false, true, true, true, true, true, false, false, false, true, false);
          }
          pow_mod_crc(29952);
        }
        calc {
          [false, false, false, false, true, false, false, true, true, true, false, false, false, false, false, false, true, true, true, false, true, false, false, false, true, true, true, false, true, true, false, false];
          {
            pow_14943();
            of_pow(14976, false, false, true, true, false, true, true, true, false, false, false, true, false, true, true, true, false, false, false, false, false, false, true, true, true, false, false, true, false, false, false, false);
          }
          pow_mod_crc(14976);
        }
      }
      pow_mod_crc(29952) + pow_mod_crc(14976);
    }
  }



  lemma lut_entry_234()
  ensures bits_of_int(lut[234] as int, 64)
      == pow_mod_crc(30080) + pow_mod_crc(15040)
  {
    calc {
      bits_of_int(lut[234] as int, 64);
      bits_of_int(8271983160334671752, 64);
      {
        lemma_bits_of_int_64_split(8271983160334671752);
      }
      bits_of_int(2210586504, 32) + bits_of_int(1925971163, 32);
      {
        unroll_bits_of_int_32_0x83c2df88();
        unroll_bits_of_int_32_0x72cbfcdb();
      }
      [false, false, false, true, false, false, false, true, true, true, true, true, true, false, true, true, false, true, false, false, false, false, true, true, true, true, false, false, false, false, false, true]+[true, true, false, true, true, false, true, true, false, false, true, true, true, true, true, true, true, true, false, true, false, false, true, true, false, true, false, false, true, true, true, false];
      {
        calc {
          [false, false, false, true, false, false, false, true, true, true, true, true, true, false, true, true, false, true, false, false, false, false, true, true, true, true, false, false, false, false, false, true];
          {
            pow_30047();
            of_pow(30080, true, false, false, false, false, false, true, true, true, true, false, false, false, false, true, false, true, true, false, true, true, true, true, true, true, false, false, false, true, false, false, false);
          }
          pow_mod_crc(30080);
        }
        calc {
          [true, true, false, true, true, false, true, true, false, false, true, true, true, true, true, true, true, true, false, true, false, false, true, true, false, true, false, false, true, true, true, false];
          {
            pow_15007();
            of_pow(15040, false, true, true, true, false, false, true, false, true, true, false, false, true, false, true, true, true, true, true, true, true, true, false, false, true, true, false, true, true, false, true, true);
          }
          pow_mod_crc(15040);
        }
      }
      pow_mod_crc(30080) + pow_mod_crc(15040);
    }
  }



  lemma lut_entry_235()
  ensures bits_of_int(lut[235] as int, 64)
      == pow_mod_crc(30208) + pow_mod_crc(15104)
  {
    calc {
      bits_of_int(lut[235] as int, 64);
      bits_of_int(7157277318341296730, 64);
      {
        lemma_bits_of_int_64_split(7157277318341296730);
      }
      bits_of_int(3601957466, 32) + bits_of_int(1666433484, 32);
      {
        unroll_bits_of_int_32_0xd6b1825a();
        unroll_bits_of_int_32_0x6353c1cc();
      }
      [false, true, false, true, true, false, true, false, false, true, false, false, false, false, false, true, true, false, false, false, true, true, false, true, false, true, true, false, true, false, true, true]+[false, false, true, true, false, false, true, true, true, false, false, false, false, false, true, true, true, true, false, false, true, false, true, false, true, true, false, false, false, true, true, false];
      {
        calc {
          [false, true, false, true, true, false, true, false, false, true, false, false, false, false, false, true, true, false, false, false, true, true, false, true, false, true, true, false, true, false, true, true];
          {
            pow_30175();
            of_pow(30208, true, true, false, true, false, true, true, false, true, false, true, true, false, false, false, true, true, false, false, false, false, false, true, false, false, true, false, true, true, false, true, false);
          }
          pow_mod_crc(30208);
        }
        calc {
          [false, false, true, true, false, false, true, true, true, false, false, false, false, false, true, true, true, true, false, false, true, false, true, false, true, true, false, false, false, true, true, false];
          {
            pow_15071();
            of_pow(15104, false, true, true, false, false, false, true, true, false, true, false, true, false, false, true, true, true, true, false, false, false, false, false, true, true, true, false, false, true, true, false, false);
          }
          pow_mod_crc(15104);
        }
      }
      pow_mod_crc(30208) + pow_mod_crc(15104);
    }
  }



  lemma lut_entry_236()
  ensures bits_of_int(lut[236] as int, 64)
      == pow_mod_crc(30336) + pow_mod_crc(15168)
  {
    calc {
      bits_of_int(lut[236] as int, 64);
      bits_of_int(3783922697974575666, 64);
      {
        lemma_bits_of_int_64_split(3783922697974575666);
      }
      bits_of_int(1313862194, 32) + bits_of_int(881013157, 32);
      {
        unroll_bits_of_int_32_0x4e4ff232();
        unroll_bits_of_int_32_0x348331a5();
      }
      [false, true, false, false, true, true, false, false, false, true, false, false, true, true, true, true, true, true, true, true, false, false, true, false, false, true, true, true, false, false, true, false]+[true, false, true, false, false, true, false, true, true, false, false, false, true, true, false, false, true, true, false, false, false, false, false, true, false, false, true, false, true, true, false, false];
      {
        calc {
          [false, true, false, false, true, true, false, false, false, true, false, false, true, true, true, true, true, true, true, true, false, false, true, false, false, true, true, true, false, false, true, false];
          {
            pow_30303();
            of_pow(30336, false, true, false, false, true, true, true, false, false, true, false, false, true, true, true, true, true, true, true, true, false, false, true, false, false, false, true, true, false, false, true, false);
          }
          pow_mod_crc(30336);
        }
        calc {
          [true, false, true, false, false, true, false, true, true, false, false, false, true, true, false, false, true, true, false, false, false, false, false, true, false, false, true, false, true, true, false, false];
          {
            pow_15135();
            of_pow(15168, false, false, true, true, false, true, false, false, true, false, false, false, false, false, true, true, false, false, true, true, false, false, false, true, true, false, true, false, false, true, false, true);
          }
          pow_mod_crc(15168);
        }
      }
      pow_mod_crc(30336) + pow_mod_crc(15168);
    }
  }



  lemma lut_entry_237()
  ensures bits_of_int(lut[237] as int, 64)
      == pow_mod_crc(30464) + pow_mod_crc(15232)
  {
    calc {
      bits_of_int(lut[237] as int, 64);
      bits_of_int(14148145487657884097, 64);
      {
        lemma_bits_of_int_64_split(14148145487657884097);
      }
      bits_of_int(1717885377, 32) + bits_of_int(3294121820, 32);
      {
        unroll_bits_of_int_32_0x6664d9c1();
        unroll_bits_of_int_32_0xc4584f5c();
      }
      [true, false, false, false, false, false, true, true, true, false, false, true, true, false, true, true, false, false, true, false, false, true, true, false, false, true, true, false, false, true, true, false]+[false, false, true, true, true, false, true, false, true, true, true, true, false, false, true, false, false, false, false, true, true, false, true, false, false, false, true, false, false, false, true, true];
      {
        calc {
          [true, false, false, false, false, false, true, true, true, false, false, true, true, false, true, true, false, false, true, false, false, true, true, false, false, true, true, false, false, true, true, false];
          {
            pow_30431();
            of_pow(30464, false, true, true, false, false, true, true, false, false, true, true, false, false, true, false, false, true, true, false, true, true, false, false, true, true, true, false, false, false, false, false, true);
          }
          pow_mod_crc(30464);
        }
        calc {
          [false, false, true, true, true, false, true, false, true, true, true, true, false, false, true, false, false, false, false, true, true, false, true, false, false, false, true, false, false, false, true, true];
          {
            pow_15199();
            of_pow(15232, true, true, false, false, false, true, false, false, false, true, false, true, true, false, false, false, false, true, false, false, true, true, true, true, false, true, false, true, true, true, false, false);
          }
          pow_mod_crc(15232);
        }
      }
      pow_mod_crc(30464) + pow_mod_crc(15232);
    }
  }



  lemma lut_entry_238()
  ensures bits_of_int(lut[238] as int, 64)
      == pow_mod_crc(30592) + pow_mod_crc(15296)
  {
    calc {
      bits_of_int(lut[238] as int, 64);
      bits_of_int(14093870007900133998, 64);
      {
        lemma_bits_of_int_64_split(14093870007900133998);
      }
      bits_of_int(2204850798, 32) + bits_of_int(3281484825, 32);
      {
        unroll_bits_of_int_32_0x836b5a6e();
        unroll_bits_of_int_32_0xc3977c19();
      }
      [false, true, true, true, false, true, true, false, false, true, false, true, true, false, true, false, true, true, false, true, false, true, true, false, true, true, false, false, false, false, false, true]+[true, false, false, true, true, false, false, false, false, false, true, true, true, true, true, false, true, true, true, false, true, false, false, true, true, true, false, false, false, false, true, true];
      {
        calc {
          [false, true, true, true, false, true, true, false, false, true, false, true, true, false, true, false, true, true, false, true, false, true, true, false, true, true, false, false, false, false, false, true];
          {
            pow_30559();
            of_pow(30592, true, false, false, false, false, false, true, true, false, true, true, false, true, false, true, true, false, true, false, true, true, false, true, false, false, true, true, false, true, true, true, false);
          }
          pow_mod_crc(30592);
        }
        calc {
          [true, false, false, true, true, false, false, false, false, false, true, true, true, true, true, false, true, true, true, false, true, false, false, true, true, true, false, false, false, false, true, true];
          {
            pow_15263();
            of_pow(15296, true, true, false, false, false, false, true, true, true, false, false, true, false, true, true, true, false, true, true, true, true, true, false, false, false, false, false, true, true, false, false, true);
          }
          pow_mod_crc(15296);
        }
      }
      pow_mod_crc(30592) + pow_mod_crc(15296);
    }
  }



  lemma lut_entry_239()
  ensures bits_of_int(lut[239] as int, 64)
      == pow_mod_crc(30720) + pow_mod_crc(15360)
  {
    calc {
      bits_of_int(lut[239] as int, 64);
      bits_of_int(17619844161229678565, 64);
      {
        lemma_bits_of_int_64_split(17619844161229678565);
      }
      bits_of_int(601221093, 32) + bits_of_int(4102439657, 32);
      {
        unroll_bits_of_int_32_0x23d5e7e5();
        unroll_bits_of_int_32_0xf48642e9();
      }
      [true, false, true, false, false, true, true, true, true, true, true, false, false, true, true, true, true, false, true, false, true, false, true, true, true, true, false, false, false, true, false, false]+[true, false, false, true, false, true, true, true, false, true, false, false, false, false, true, false, false, true, true, false, false, false, false, true, false, false, true, false, true, true, true, true];
      {
        calc {
          [true, false, true, false, false, true, true, true, true, true, true, false, false, true, true, true, true, false, true, false, true, false, true, true, true, true, false, false, false, true, false, false];
          {
            pow_30687();
            of_pow(30720, false, false, true, false, false, false, true, true, true, true, false, true, false, true, false, true, true, true, true, false, false, true, true, true, true, true, true, false, false, true, false, true);
          }
          pow_mod_crc(30720);
        }
        calc {
          [true, false, false, true, false, true, true, true, false, true, false, false, false, false, true, false, false, true, true, false, false, false, false, true, false, false, true, false, true, true, true, true];
          {
            pow_15327();
            of_pow(15360, true, true, true, true, false, true, false, false, true, false, false, false, false, true, true, false, false, true, false, false, false, false, true, false, true, true, true, false, true, false, false, true);
          }
          pow_mod_crc(15360);
        }
      }
      pow_mod_crc(30720) + pow_mod_crc(15360);
    }
  }



  lemma lut_entry_240()
  ensures bits_of_int(lut[240] as int, 64)
      == pow_mod_crc(30848) + pow_mod_crc(15424)
  {
    calc {
      bits_of_int(lut[240] as int, 64);
      bits_of_int(15779182064437711683, 64);
      {
        lemma_bits_of_int_64_split(15779182064437711683);
      }
      bits_of_int(1694913347, 32) + bits_of_int(3673877116, 32);
      {
        unroll_bits_of_int_32_0x65065343();
        unroll_bits_of_int_32_0xdafaea7c();
      }
      [true, true, false, false, false, false, true, false, true, true, false, false, true, false, true, false, false, true, true, false, false, false, false, false, true, false, true, false, false, true, true, false]+[false, false, true, true, true, true, true, false, false, true, false, true, false, true, true, true, false, true, false, true, true, true, true, true, false, true, false, true, true, false, true, true];
      {
        calc {
          [true, true, false, false, false, false, true, false, true, true, false, false, true, false, true, false, false, true, true, false, false, false, false, false, true, false, true, false, false, true, true, false];
          {
            pow_30815();
            of_pow(30848, false, true, true, false, false, true, false, true, false, false, false, false, false, true, true, false, false, true, false, true, false, false, true, true, false, true, false, false, false, false, true, true);
          }
          pow_mod_crc(30848);
        }
        calc {
          [false, false, true, true, true, true, true, false, false, true, false, true, false, true, true, true, false, true, false, true, true, true, true, true, false, true, false, true, true, false, true, true];
          {
            pow_15391();
            of_pow(15424, true, true, false, true, true, false, true, false, true, true, true, true, true, false, true, false, true, true, true, false, true, false, true, false, false, true, true, true, true, true, false, false);
          }
          pow_mod_crc(15424);
        }
      }
      pow_mod_crc(30848) + pow_mod_crc(15424);
    }
  }



  lemma lut_entry_241()
  ensures bits_of_int(lut[241] as int, 64)
      == pow_mod_crc(30976) + pow_mod_crc(15488)
  {
    calc {
      bits_of_int(lut[241] as int, 64);
      bits_of_int(5986260142597198349, 64);
      {
        lemma_bits_of_int_64_split(5986260142597198349);
      }
      bits_of_int(345362957, 32) + bits_of_int(1393784802, 32);
      {
        unroll_bits_of_int_32_0x1495d20d();
        unroll_bits_of_int_32_0x531377e2();
      }
      [true, false, true, true, false, false, false, false, false, true, false, false, true, false, true, true, true, false, true, false, true, false, false, true, false, false, true, false, true, false, false, false]+[false, true, false, false, false, true, true, true, true, true, true, false, true, true, true, false, true, true, false, false, true, false, false, false, true, true, false, false, true, false, true, false];
      {
        calc {
          [true, false, true, true, false, false, false, false, false, true, false, false, true, false, true, true, true, false, true, false, true, false, false, true, false, false, true, false, true, false, false, false];
          {
            pow_30943();
            of_pow(30976, false, false, false, true, false, true, false, false, true, false, false, true, false, true, false, true, true, true, false, true, false, false, true, false, false, false, false, false, true, true, false, true);
          }
          pow_mod_crc(30976);
        }
        calc {
          [false, true, false, false, false, true, true, true, true, true, true, false, true, true, true, false, true, true, false, false, true, false, false, false, true, true, false, false, true, false, true, false];
          {
            pow_15455();
            of_pow(15488, false, true, false, true, false, false, true, true, false, false, false, true, false, false, true, true, false, true, true, true, false, true, true, true, true, true, true, false, false, false, true, false);
          }
          pow_mod_crc(15488);
        }
      }
      pow_mod_crc(30976) + pow_mod_crc(15488);
    }
  }



  lemma lut_entry_242()
  ensures bits_of_int(lut[242] as int, 64)
      == pow_mod_crc(31104) + pow_mod_crc(15552)
  {
    calc {
      bits_of_int(lut[242] as int, 64);
      bits_of_int(8348349917053092587, 64);
      {
        lemma_bits_of_int_64_split(8348349917053092587);
      }
      bits_of_int(2728166123, 32) + bits_of_int(1943751684, 32);
      {
        unroll_bits_of_int_32_0xa29c82eb();
        unroll_bits_of_int_32_0x73db4c04();
      }
      [true, true, false, true, false, true, true, true, false, true, false, false, false, false, false, true, false, false, true, true, true, false, false, true, false, true, false, false, false, true, false, true]+[false, false, true, false, false, false, false, false, false, false, true, true, false, false, true, false, true, true, false, true, true, false, true, true, true, true, false, false, true, true, true, false];
      {
        calc {
          [true, true, false, true, false, true, true, true, false, true, false, false, false, false, false, true, false, false, true, true, true, false, false, true, false, true, false, false, false, true, false, true];
          {
            pow_31071();
            of_pow(31104, true, false, true, false, false, false, true, false, true, false, false, true, true, true, false, false, true, false, false, false, false, false, true, false, true, true, true, false, true, false, true, true);
          }
          pow_mod_crc(31104);
        }
        calc {
          [false, false, true, false, false, false, false, false, false, false, true, true, false, false, true, false, true, true, false, true, true, false, true, true, true, true, false, false, true, true, true, false];
          {
            pow_15519();
            of_pow(15552, false, true, true, true, false, false, true, true, true, true, false, true, true, false, true, true, false, true, false, false, true, true, false, false, false, false, false, false, false, true, false, false);
          }
          pow_mod_crc(15552);
        }
      }
      pow_mod_crc(31104) + pow_mod_crc(15552);
    }
  }



  lemma lut_entry_243()
  ensures bits_of_int(lut[243] as int, 64)
      == pow_mod_crc(31232) + pow_mod_crc(15616)
  {
    calc {
      bits_of_int(lut[243] as int, 64);
      bits_of_int(15939853774008398719, 64);
      {
        lemma_bits_of_int_64_split(15939853774008398719);
      }
      bits_of_int(4084249471, 32) + bits_of_int(3711286413, 32);
      {
        unroll_bits_of_int_32_0xf370b37f();
        unroll_bits_of_int_32_0xdd35bc8d();
      }
      [true, true, true, true, true, true, true, false, true, true, false, false, true, true, false, true, false, false, false, false, true, true, true, false, true, true, false, false, true, true, true, true]+[true, false, true, true, false, false, false, true, false, false, true, true, true, true, false, true, true, false, true, false, true, true, false, false, true, false, true, true, true, false, true, true];
      {
        calc {
          [true, true, true, true, true, true, true, false, true, true, false, false, true, true, false, true, false, false, false, false, true, true, true, false, true, true, false, false, true, true, true, true];
          {
            pow_31199();
            of_pow(31232, true, true, true, true, false, false, true, true, false, true, true, true, false, false, false, false, true, false, true, true, false, false, true, true, false, true, true, true, true, true, true, true);
          }
          pow_mod_crc(31232);
        }
        calc {
          [true, false, true, true, false, false, false, true, false, false, true, true, true, true, false, true, true, false, true, false, true, true, false, false, true, false, true, true, true, false, true, true];
          {
            pow_15583();
            of_pow(15616, true, true, false, true, true, true, false, true, false, false, true, true, false, true, false, true, true, false, true, true, true, true, false, false, true, false, false, false, true, true, false, true);
          }
          pow_mod_crc(15616);
        }
      }
      pow_mod_crc(31232) + pow_mod_crc(15616);
    }
  }



  lemma lut_entry_244()
  ensures bits_of_int(lut[244] as int, 64)
      == pow_mod_crc(31360) + pow_mod_crc(15680)
  {
    calc {
      bits_of_int(lut[244] as int, 64);
      bits_of_int(8243659798360217564, 64);
      {
        lemma_bits_of_int_64_split(8243659798360217564);
      }
      bits_of_int(3933067228, 32) + bits_of_int(1919376616, 32);
      {
        unroll_bits_of_int_32_0xea6dd7dc();
        unroll_bits_of_int_32_0x72675ce8();
      }
      [false, false, true, true, true, false, true, true, true, true, true, false, true, false, true, true, true, false, true, true, false, true, true, false, false, true, false, true, false, true, true, true]+[false, false, false, true, false, true, true, true, false, false, true, true, true, false, true, false, true, true, true, false, false, true, true, false, false, true, false, false, true, true, true, false];
      {
        calc {
          [false, false, true, true, true, false, true, true, true, true, true, false, true, false, true, true, true, false, true, true, false, true, true, false, false, true, false, true, false, true, true, true];
          {
            pow_31327();
            of_pow(31360, true, true, true, false, true, false, true, false, false, true, true, false, true, true, false, true, true, true, false, true, false, true, true, true, true, true, false, true, true, true, false, false);
          }
          pow_mod_crc(31360);
        }
        calc {
          [false, false, false, true, false, true, true, true, false, false, true, true, true, false, true, false, true, true, true, false, false, true, true, false, false, true, false, false, true, true, true, false];
          {
            pow_15647();
            of_pow(15680, false, true, true, true, false, false, true, false, false, true, true, false, false, true, true, true, false, true, false, true, true, true, false, false, true, true, true, false, true, false, false, false);
          }
          pow_mod_crc(15680);
        }
      }
      pow_mod_crc(31360) + pow_mod_crc(15680);
    }
  }



  lemma lut_entry_245()
  ensures bits_of_int(lut[245] as int, 64)
      == pow_mod_crc(31488) + pow_mod_crc(15744)
  {
    calc {
      bits_of_int(lut[245] as int, 64);
      bits_of_int(12851912084904041422, 64);
      {
        lemma_bits_of_int_64_split(12851912084904041422);
      }
      bits_of_int(3913374670, 32) + bits_of_int(2992318962, 32);
      {
        unroll_bits_of_int_32_0xe9415bce();
        unroll_bits_of_int_32_0xb25b29f2();
      }
      [false, true, true, true, false, false, true, true, true, true, false, true, true, false, true, false, true, false, false, false, false, false, true, false, true, false, false, true, false, true, true, true]+[false, true, false, false, true, true, true, true, true, false, false, true, false, true, false, false, true, true, false, true, true, false, true, false, false, true, false, false, true, true, false, true];
      {
        calc {
          [false, true, true, true, false, false, true, true, true, true, false, true, true, false, true, false, true, false, false, false, false, false, true, false, true, false, false, true, false, true, true, true];
          {
            pow_31455();
            of_pow(31488, true, true, true, false, true, false, false, true, false, true, false, false, false, false, false, true, false, true, false, true, true, false, true, true, true, true, false, false, true, true, true, false);
          }
          pow_mod_crc(31488);
        }
        calc {
          [false, true, false, false, true, true, true, true, true, false, false, true, false, true, false, false, true, true, false, true, true, false, true, false, false, true, false, false, true, true, false, true];
          {
            pow_15711();
            of_pow(15744, true, false, true, true, false, false, true, false, false, true, false, true, true, false, true, true, false, false, true, false, true, false, false, true, true, true, true, true, false, false, true, false);
          }
          pow_mod_crc(15744);
        }
      }
      pow_mod_crc(31488) + pow_mod_crc(15744);
    }
  }



  lemma lut_entry_246()
  ensures bits_of_int(lut[246] as int, 64)
      == pow_mod_crc(31616) + pow_mod_crc(15808)
  {
    calc {
      bits_of_int(lut[246] as int, 64);
      bits_of_int(4522457916458965775, 64);
      {
        lemma_bits_of_int_64_split(4522457916458965775);
      }
      bits_of_int(2519767823, 32) + bits_of_int(1052966787, 32);
      {
        unroll_bits_of_int_32_0x96309b0f();
        unroll_bits_of_int_32_0x3ec2ff83();
      }
      [true, true, true, true, false, false, false, false, true, true, false, true, true, false, false, true, false, false, false, false, true, true, false, false, false, true, true, false, true, false, false, true]+[true, true, false, false, false, false, false, true, true, true, true, true, true, true, true, true, false, true, false, false, false, false, true, true, false, true, true, true, true, true, false, false];
      {
        calc {
          [true, true, true, true, false, false, false, false, true, true, false, true, true, false, false, true, false, false, false, false, true, true, false, false, false, true, true, false, true, false, false, true];
          {
            pow_31583();
            of_pow(31616, true, false, false, true, false, true, true, false, false, false, true, true, false, false, false, false, true, false, false, true, true, false, true, true, false, false, false, false, true, true, true, true);
          }
          pow_mod_crc(31616);
        }
        calc {
          [true, true, false, false, false, false, false, true, true, true, true, true, true, true, true, true, false, true, false, false, false, false, true, true, false, true, true, true, true, true, false, false];
          {
            pow_15775();
            of_pow(15808, false, false, true, true, true, true, true, false, true, true, false, false, false, false, true, false, true, true, true, true, true, true, true, true, true, false, false, false, false, false, true, true);
          }
          pow_mod_crc(15808);
        }
      }
      pow_mod_crc(31616) + pow_mod_crc(15808);
    }
  }



  lemma lut_entry_247()
  ensures bits_of_int(lut[247] as int, 64)
      == pow_mod_crc(31744) + pow_mod_crc(15872)
  {
    calc {
      bits_of_int(lut[247] as int, 64);
      bits_of_int(11123572503752390216, 64);
      {
        lemma_bits_of_int_64_split(11123572503752390216);
      }
      bits_of_int(3346445896, 32) + bits_of_int(2589908545, 32);
      {
        unroll_bits_of_int_32_0xc776b648();
        unroll_bits_of_int_32_0x9a5ede41();
      }
      [false, false, false, true, false, false, true, false, false, true, true, false, true, true, false, true, false, true, true, false, true, true, true, false, true, true, true, false, false, false, true, true]+[true, false, false, false, false, false, true, false, false, true, true, true, true, false, true, true, false, true, true, true, true, false, true, false, false, true, false, true, true, false, false, true];
      {
        calc {
          [false, false, false, true, false, false, true, false, false, true, true, false, true, true, false, true, false, true, true, false, true, true, true, false, true, true, true, false, false, false, true, true];
          {
            pow_31711();
            of_pow(31744, true, true, false, false, false, true, true, true, false, true, true, true, false, true, true, false, true, false, true, true, false, true, true, false, false, true, false, false, true, false, false, false);
          }
          pow_mod_crc(31744);
        }
        calc {
          [true, false, false, false, false, false, true, false, false, true, true, true, true, false, true, true, false, true, true, true, true, false, true, false, false, true, false, true, true, false, false, true];
          {
            pow_15839();
            of_pow(15872, true, false, false, true, true, false, true, false, false, true, false, true, true, true, true, false, true, true, false, true, true, true, true, false, false, true, false, false, false, false, false, true);
          }
          pow_mod_crc(15872);
        }
      }
      pow_mod_crc(31744) + pow_mod_crc(15872);
    }
  }



  lemma lut_entry_248()
  ensures bits_of_int(lut[248] as int, 64)
      == pow_mod_crc(31872) + pow_mod_crc(15936)
  {
    calc {
      bits_of_int(lut[248] as int, 64);
      bits_of_int(16773551361067078341, 64);
      {
        lemma_bits_of_int_64_split(16773551361067078341);
      }
      bits_of_int(3257684677, 32) + bits_of_int(3905396759, 32);
      {
        unroll_bits_of_int_32_0xc22c52c5();
        unroll_bits_of_int_32_0xe8c7a017();
      }
      [true, false, true, false, false, false, true, true, false, true, false, false, true, false, true, false, false, false, true, true, false, true, false, false, false, true, false, false, false, false, true, true]+[true, true, true, false, true, false, false, false, false, false, false, false, false, true, false, true, true, true, true, false, false, false, true, true, false, false, false, true, false, true, true, true];
      {
        calc {
          [true, false, true, false, false, false, true, true, false, true, false, false, true, false, true, false, false, false, true, true, false, true, false, false, false, true, false, false, false, false, true, true];
          {
            pow_31839();
            of_pow(31872, true, true, false, false, false, false, true, false, false, false, true, false, true, true, false, false, false, true, false, true, false, false, true, false, true, true, false, false, false, true, false, true);
          }
          pow_mod_crc(31872);
        }
        calc {
          [true, true, true, false, true, false, false, false, false, false, false, false, false, true, false, true, true, true, true, false, false, false, true, true, false, false, false, true, false, true, true, true];
          {
            pow_15903();
            of_pow(15936, true, true, true, false, true, false, false, false, true, true, false, false, false, true, true, true, true, false, true, false, false, false, false, false, false, false, false, true, false, true, true, true);
          }
          pow_mod_crc(15936);
        }
      }
      pow_mod_crc(31872) + pow_mod_crc(15936);
    }
  }



  lemma lut_entry_249()
  ensures bits_of_int(lut[249] as int, 64)
      == pow_mod_crc(32000) + pow_mod_crc(16000)
  {
    calc {
      bits_of_int(lut[249] as int, 64);
      bits_of_int(11917527771528547651, 64);
      {
        lemma_bits_of_int_64_split(11917527771528547651);
      }
      bits_of_int(3469724995, 32) + bits_of_int(2774765661, 32);
      {
        unroll_bits_of_int_32_0xcecfcd43();
        unroll_bits_of_int_32_0xa563905d();
      }
      [true, true, false, false, false, false, true, false, true, false, true, true, false, false, true, true, true, true, true, true, false, false, true, true, false, true, true, true, false, false, true, true]+[true, false, true, true, true, false, true, false, false, false, false, false, true, false, false, true, true, true, false, false, false, true, true, false, true, false, true, false, false, true, false, true];
      {
        calc {
          [true, true, false, false, false, false, true, false, true, false, true, true, false, false, true, true, true, true, true, true, false, false, true, true, false, true, true, true, false, false, true, true];
          {
            pow_31967();
            of_pow(32000, true, true, false, false, true, true, true, false, true, true, false, false, true, true, true, true, true, true, false, false, true, true, false, true, false, true, false, false, false, false, true, true);
          }
          pow_mod_crc(32000);
        }
        calc {
          [true, false, true, true, true, false, true, false, false, false, false, false, true, false, false, true, true, true, false, false, false, true, true, false, true, false, true, false, false, true, false, true];
          {
            pow_15967();
            of_pow(16000, true, false, true, false, false, true, false, true, false, true, true, false, false, false, true, true, true, false, false, true, false, false, false, false, false, true, false, true, true, true, false, true);
          }
          pow_mod_crc(16000);
        }
      }
      pow_mod_crc(32000) + pow_mod_crc(16000);
    }
  }



  lemma lut_entry_250()
  ensures bits_of_int(lut[250] as int, 64)
      == pow_mod_crc(32128) + pow_mod_crc(16064)
  {
    calc {
      bits_of_int(lut[250] as int, 64);
      bits_of_int(14937308497135607527, 64);
      {
        lemma_bits_of_int_64_split(14937308497135607527);
      }
      bits_of_int(3627097831, 32) + bits_of_int(3477863151, 32);
      {
        unroll_bits_of_int_32_0xd8311ee7();
        unroll_bits_of_int_32_0xcf4bfaef();
      }
      [true, true, true, false, false, true, true, true, false, true, true, true, true, false, false, false, true, false, false, false, true, true, false, false, false, false, false, true, true, false, true, true]+[true, true, true, true, false, true, true, true, false, true, false, true, true, true, true, true, true, true, false, true, false, false, true, false, true, true, true, true, false, false, true, true];
      {
        calc {
          [true, true, true, false, false, true, true, true, false, true, true, true, true, false, false, false, true, false, false, false, true, true, false, false, false, false, false, true, true, false, true, true];
          {
            pow_32095();
            of_pow(32128, true, true, false, true, true, false, false, false, false, false, true, true, false, false, false, true, false, false, false, true, true, true, true, false, true, true, true, false, false, true, true, true);
          }
          pow_mod_crc(32128);
        }
        calc {
          [true, true, true, true, false, true, true, true, false, true, false, true, true, true, true, true, true, true, false, true, false, false, true, false, true, true, true, true, false, false, true, true];
          {
            pow_16031();
            of_pow(16064, true, true, false, false, true, true, true, true, false, true, false, false, true, false, true, true, true, true, true, true, true, false, true, false, true, true, true, false, true, true, true, true);
          }
          pow_mod_crc(16064);
        }
      }
      pow_mod_crc(32128) + pow_mod_crc(16064);
    }
  }



  lemma lut_entry_251()
  ensures bits_of_int(lut[251] as int, 64)
      == pow_mod_crc(32256) + pow_mod_crc(16128)
  {
    calc {
      bits_of_int(lut[251] as int, 64);
      bits_of_int(5029921885562273423, 64);
      {
        lemma_bits_of_int_64_split(5029921885562273423);
      }
      bits_of_int(619118223, 32) + bits_of_int(1171119950, 32);
      {
        unroll_bits_of_int_32_0x24e6fe8f();
        unroll_bits_of_int_32_0x45cddf4e();
      }
      [true, true, true, true, false, false, false, true, false, true, true, true, true, true, true, true, false, true, true, false, false, true, true, true, false, false, true, false, false, true, false, false]+[false, true, true, true, false, false, true, false, true, true, true, true, true, false, true, true, true, false, true, true, false, false, true, true, true, false, true, false, false, false, true, false];
      {
        calc {
          [true, true, true, true, false, false, false, true, false, true, true, true, true, true, true, true, false, true, true, false, false, true, true, true, false, false, true, false, false, true, false, false];
          {
            pow_32223();
            of_pow(32256, false, false, true, false, false, true, false, false, true, true, true, false, false, true, true, false, true, true, true, true, true, true, true, false, true, false, false, false, true, true, true, true);
          }
          pow_mod_crc(32256);
        }
        calc {
          [false, true, true, true, false, false, true, false, true, true, true, true, true, false, true, true, true, false, true, true, false, false, true, true, true, false, true, false, false, false, true, false];
          {
            pow_16095();
            of_pow(16128, false, true, false, false, false, true, false, true, true, true, false, false, true, true, false, true, true, true, false, true, true, true, true, true, false, true, false, false, true, true, true, false);
          }
          pow_mod_crc(16128);
        }
      }
      pow_mod_crc(32256) + pow_mod_crc(16128);
    }
  }



  lemma lut_entry_252()
  ensures bits_of_int(lut[252] as int, 64)
      == pow_mod_crc(32384) + pow_mod_crc(16192)
  {
    calc {
      bits_of_int(lut[252] as int, 64);
      bits_of_int(7772679452391561161, 64);
      {
        lemma_bits_of_int_64_split(7772679452391561161);
      }
      bits_of_int(3502692297, 32) + bits_of_int(1809717959, 32);
      {
        unroll_bits_of_int_32_0xd0c6d7c9();
        unroll_bits_of_int_32_0x6bde1ac7();
      }
      [true, false, false, true, false, false, true, true, true, true, true, false, true, false, true, true, false, true, true, false, false, false, true, true, false, false, false, false, true, false, true, true]+[true, true, true, false, false, false, true, true, false, true, false, true, true, false, false, false, false, true, true, true, true, false, true, true, true, true, false, true, false, true, true, false];
      {
        calc {
          [true, false, false, true, false, false, true, true, true, true, true, false, true, false, true, true, false, true, true, false, false, false, true, true, false, false, false, false, true, false, true, true];
          {
            pow_32351();
            of_pow(32384, true, true, false, true, false, false, false, false, true, true, false, false, false, true, true, false, true, true, false, true, false, true, true, true, true, true, false, false, true, false, false, true);
          }
          pow_mod_crc(32384);
        }
        calc {
          [true, true, true, false, false, false, true, true, false, true, false, true, true, false, false, false, false, true, true, true, true, false, true, true, true, true, false, true, false, true, true, false];
          {
            pow_16159();
            of_pow(16192, false, true, true, false, true, false, true, true, true, true, false, true, true, true, true, false, false, false, false, true, true, false, true, false, true, true, false, false, false, true, true, true);
          }
          pow_mod_crc(16192);
        }
      }
      pow_mod_crc(32384) + pow_mod_crc(16192);
    }
  }



  lemma lut_entry_253()
  ensures bits_of_int(lut[253] as int, 64)
      == pow_mod_crc(32512) + pow_mod_crc(16256)
  {
    calc {
      bits_of_int(lut[253] as int, 64);
      bits_of_int(12464328808824724810, 64);
      {
        lemma_bits_of_int_64_split(12464328808824724810);
      }
      bits_of_int(1168792906, 32) + bits_of_int(2902077699, 32);
      {
        unroll_bits_of_int_32_0x45aa5d4a();
        unroll_bits_of_int_32_0xacfa3103();
      }
      [false, true, false, true, false, false, true, false, true, false, true, true, true, false, true, false, false, true, false, true, false, true, false, true, true, false, true, false, false, false, true, false]+[true, true, false, false, false, false, false, false, true, false, false, false, true, true, false, false, false, true, false, true, true, true, true, true, false, false, true, true, false, true, false, true];
      {
        calc {
          [false, true, false, true, false, false, true, false, true, false, true, true, true, false, true, false, false, true, false, true, false, true, false, true, true, false, true, false, false, false, true, false];
          {
            pow_32479();
            of_pow(32512, false, true, false, false, false, true, false, true, true, false, true, false, true, false, true, false, false, true, false, true, true, true, false, true, false, true, false, false, true, false, true, false);
          }
          pow_mod_crc(32512);
        }
        calc {
          [true, true, false, false, false, false, false, false, true, false, false, false, true, true, false, false, false, true, false, true, true, true, true, true, false, false, true, true, false, true, false, true];
          {
            pow_16223();
            of_pow(16256, true, false, true, false, true, true, false, false, true, true, true, true, true, false, true, false, false, false, true, true, false, false, false, true, false, false, false, false, false, false, true, true);
          }
          pow_mod_crc(16256);
        }
      }
      pow_mod_crc(32512) + pow_mod_crc(16256);
    }
  }



  lemma lut_entry_254()
  ensures bits_of_int(lut[254] as int, 64)
      == pow_mod_crc(32640) + pow_mod_crc(16320)
  {
    calc {
      bits_of_int(lut[254] as int, 64);
      bits_of_int(12542935916760952933, 64);
      {
        lemma_bits_of_int_64_split(12542935916760952933);
      }
      bits_of_int(3473305701, 32) + bits_of_int(2920379842, 32);
      {
        unroll_bits_of_int_32_0xcf067065();
        unroll_bits_of_int_32_0xae1175c2();
      }
      [true, false, true, false, false, true, true, false, false, false, false, false, true, true, true, false, false, true, true, false, false, false, false, false, true, true, true, true, false, false, true, true]+[false, true, false, false, false, false, true, true, true, false, true, false, true, true, true, false, true, false, false, false, true, false, false, false, false, true, true, true, false, true, false, true];
      {
        calc {
          [true, false, true, false, false, true, true, false, false, false, false, false, true, true, true, false, false, true, true, false, false, false, false, false, true, true, true, true, false, false, true, true];
          {
            pow_32607();
            of_pow(32640, true, true, false, false, true, true, true, true, false, false, false, false, false, true, true, false, false, true, true, true, false, false, false, false, false, true, true, false, false, true, false, true);
          }
          pow_mod_crc(32640);
        }
        calc {
          [false, true, false, false, false, false, true, true, true, false, true, false, true, true, true, false, true, false, false, false, true, false, false, false, false, true, true, true, false, true, false, true];
          {
            pow_16287();
            of_pow(16320, true, false, true, false, true, true, true, false, false, false, false, true, false, false, false, true, false, true, true, true, false, true, false, true, true, true, false, false, false, false, true, false);
          }
          pow_mod_crc(16320);
        }
      }
      pow_mod_crc(32640) + pow_mod_crc(16320);
    }
  }



  lemma lut_entry_255()
  ensures bits_of_int(lut[255] as int, 64)
      == pow_mod_crc(32768) + pow_mod_crc(16384)
  {
    calc {
      bits_of_int(lut[255] as int, 64);
      bits_of_int(11897209723087789175, 64);
      {
        lemma_bits_of_int_64_split(11897209723087789175);
      }
      bits_of_int(2197331063, 32) + bits_of_int(2770034997, 32);
      {
        unroll_bits_of_int_32_0x82f89c77();
        unroll_bits_of_int_32_0xa51b6135();
      }
      [true, true, true, false, true, true, true, false, false, false, true, true, true, false, false, true, false, false, false, true, true, true, true, true, false, true, false, false, false, false, false, true]+[true, false, true, false, true, true, false, false, true, false, false, false, false, true, true, false, true, true, false, true, true, false, false, false, true, false, true, false, false, true, false, true];
      {
        calc {
          [true, true, true, false, true, true, true, false, false, false, true, true, true, false, false, true, false, false, false, true, true, true, true, true, false, true, false, false, false, false, false, true];
          {
            pow_32735();
            of_pow(32768, true, false, false, false, false, false, true, false, true, true, true, true, true, false, false, false, true, false, false, true, true, true, false, false, false, true, true, true, false, true, true, true);
          }
          pow_mod_crc(32768);
        }
        calc {
          [true, false, true, false, true, true, false, false, true, false, false, false, false, true, true, false, true, true, false, true, true, false, false, false, true, false, true, false, false, true, false, true];
          {
            pow_16351();
            of_pow(16384, true, false, true, false, false, true, false, true, false, false, false, true, true, false, true, true, false, true, true, false, false, false, false, true, false, false, true, true, false, true, false, true);
          }
          pow_mod_crc(16384);
        }
      }
      pow_mod_crc(32768) + pow_mod_crc(16384);
    }
  }


  lemma {:fuel bits_of_int,0} {:fuel pow_mod_crc,0} lut_entries(n: nat)
  requires 1 <= n <= 256
  ensures |lut| == 257
  ensures bits_of_int(lut[n-1] as int, 64) == pow_mod_crc(2*64*n) + pow_mod_crc(64*n)
  {
    if n == 1 { lut_entry_0(); }
    else if n == 2 { lut_entry_1(); }
    else if n == 3 { lut_entry_2(); }
    else if n == 4 { lut_entry_3(); }
    else if n == 5 { lut_entry_4(); }
    else if n == 6 { lut_entry_5(); }
    else if n == 7 { lut_entry_6(); }
    else if n == 8 { lut_entry_7(); }
    else if n == 9 { lut_entry_8(); }
    else if n == 10 { lut_entry_9(); }
    else if n == 11 { lut_entry_10(); }
    else if n == 12 { lut_entry_11(); }
    else if n == 13 { lut_entry_12(); }
    else if n == 14 { lut_entry_13(); }
    else if n == 15 { lut_entry_14(); }
    else if n == 16 { lut_entry_15(); }
    else if n == 17 { lut_entry_16(); }
    else if n == 18 { lut_entry_17(); }
    else if n == 19 { lut_entry_18(); }
    else if n == 20 { lut_entry_19(); }
    else if n == 21 { lut_entry_20(); }
    else if n == 22 { lut_entry_21(); }
    else if n == 23 { lut_entry_22(); }
    else if n == 24 { lut_entry_23(); }
    else if n == 25 { lut_entry_24(); }
    else if n == 26 { lut_entry_25(); }
    else if n == 27 { lut_entry_26(); }
    else if n == 28 { lut_entry_27(); }
    else if n == 29 { lut_entry_28(); }
    else if n == 30 { lut_entry_29(); }
    else if n == 31 { lut_entry_30(); }
    else if n == 32 { lut_entry_31(); }
    else if n == 33 { lut_entry_32(); }
    else if n == 34 { lut_entry_33(); }
    else if n == 35 { lut_entry_34(); }
    else if n == 36 { lut_entry_35(); }
    else if n == 37 { lut_entry_36(); }
    else if n == 38 { lut_entry_37(); }
    else if n == 39 { lut_entry_38(); }
    else if n == 40 { lut_entry_39(); }
    else if n == 41 { lut_entry_40(); }
    else if n == 42 { lut_entry_41(); }
    else if n == 43 { lut_entry_42(); }
    else if n == 44 { lut_entry_43(); }
    else if n == 45 { lut_entry_44(); }
    else if n == 46 { lut_entry_45(); }
    else if n == 47 { lut_entry_46(); }
    else if n == 48 { lut_entry_47(); }
    else if n == 49 { lut_entry_48(); }
    else if n == 50 { lut_entry_49(); }
    else if n == 51 { lut_entry_50(); }
    else if n == 52 { lut_entry_51(); }
    else if n == 53 { lut_entry_52(); }
    else if n == 54 { lut_entry_53(); }
    else if n == 55 { lut_entry_54(); }
    else if n == 56 { lut_entry_55(); }
    else if n == 57 { lut_entry_56(); }
    else if n == 58 { lut_entry_57(); }
    else if n == 59 { lut_entry_58(); }
    else if n == 60 { lut_entry_59(); }
    else if n == 61 { lut_entry_60(); }
    else if n == 62 { lut_entry_61(); }
    else if n == 63 { lut_entry_62(); }
    else if n == 64 { lut_entry_63(); }
    else if n == 65 { lut_entry_64(); }
    else if n == 66 { lut_entry_65(); }
    else if n == 67 { lut_entry_66(); }
    else if n == 68 { lut_entry_67(); }
    else if n == 69 { lut_entry_68(); }
    else if n == 70 { lut_entry_69(); }
    else if n == 71 { lut_entry_70(); }
    else if n == 72 { lut_entry_71(); }
    else if n == 73 { lut_entry_72(); }
    else if n == 74 { lut_entry_73(); }
    else if n == 75 { lut_entry_74(); }
    else if n == 76 { lut_entry_75(); }
    else if n == 77 { lut_entry_76(); }
    else if n == 78 { lut_entry_77(); }
    else if n == 79 { lut_entry_78(); }
    else if n == 80 { lut_entry_79(); }
    else if n == 81 { lut_entry_80(); }
    else if n == 82 { lut_entry_81(); }
    else if n == 83 { lut_entry_82(); }
    else if n == 84 { lut_entry_83(); }
    else if n == 85 { lut_entry_84(); }
    else if n == 86 { lut_entry_85(); }
    else if n == 87 { lut_entry_86(); }
    else if n == 88 { lut_entry_87(); }
    else if n == 89 { lut_entry_88(); }
    else if n == 90 { lut_entry_89(); }
    else if n == 91 { lut_entry_90(); }
    else if n == 92 { lut_entry_91(); }
    else if n == 93 { lut_entry_92(); }
    else if n == 94 { lut_entry_93(); }
    else if n == 95 { lut_entry_94(); }
    else if n == 96 { lut_entry_95(); }
    else if n == 97 { lut_entry_96(); }
    else if n == 98 { lut_entry_97(); }
    else if n == 99 { lut_entry_98(); }
    else if n == 100 { lut_entry_99(); }
    else if n == 101 { lut_entry_100(); }
    else if n == 102 { lut_entry_101(); }
    else if n == 103 { lut_entry_102(); }
    else if n == 104 { lut_entry_103(); }
    else if n == 105 { lut_entry_104(); }
    else if n == 106 { lut_entry_105(); }
    else if n == 107 { lut_entry_106(); }
    else if n == 108 { lut_entry_107(); }
    else if n == 109 { lut_entry_108(); }
    else if n == 110 { lut_entry_109(); }
    else if n == 111 { lut_entry_110(); }
    else if n == 112 { lut_entry_111(); }
    else if n == 113 { lut_entry_112(); }
    else if n == 114 { lut_entry_113(); }
    else if n == 115 { lut_entry_114(); }
    else if n == 116 { lut_entry_115(); }
    else if n == 117 { lut_entry_116(); }
    else if n == 118 { lut_entry_117(); }
    else if n == 119 { lut_entry_118(); }
    else if n == 120 { lut_entry_119(); }
    else if n == 121 { lut_entry_120(); }
    else if n == 122 { lut_entry_121(); }
    else if n == 123 { lut_entry_122(); }
    else if n == 124 { lut_entry_123(); }
    else if n == 125 { lut_entry_124(); }
    else if n == 126 { lut_entry_125(); }
    else if n == 127 { lut_entry_126(); }
    else if n == 128 { lut_entry_127(); }
    else if n == 129 { lut_entry_128(); }
    else if n == 130 { lut_entry_129(); }
    else if n == 131 { lut_entry_130(); }
    else if n == 132 { lut_entry_131(); }
    else if n == 133 { lut_entry_132(); }
    else if n == 134 { lut_entry_133(); }
    else if n == 135 { lut_entry_134(); }
    else if n == 136 { lut_entry_135(); }
    else if n == 137 { lut_entry_136(); }
    else if n == 138 { lut_entry_137(); }
    else if n == 139 { lut_entry_138(); }
    else if n == 140 { lut_entry_139(); }
    else if n == 141 { lut_entry_140(); }
    else if n == 142 { lut_entry_141(); }
    else if n == 143 { lut_entry_142(); }
    else if n == 144 { lut_entry_143(); }
    else if n == 145 { lut_entry_144(); }
    else if n == 146 { lut_entry_145(); }
    else if n == 147 { lut_entry_146(); }
    else if n == 148 { lut_entry_147(); }
    else if n == 149 { lut_entry_148(); }
    else if n == 150 { lut_entry_149(); }
    else if n == 151 { lut_entry_150(); }
    else if n == 152 { lut_entry_151(); }
    else if n == 153 { lut_entry_152(); }
    else if n == 154 { lut_entry_153(); }
    else if n == 155 { lut_entry_154(); }
    else if n == 156 { lut_entry_155(); }
    else if n == 157 { lut_entry_156(); }
    else if n == 158 { lut_entry_157(); }
    else if n == 159 { lut_entry_158(); }
    else if n == 160 { lut_entry_159(); }
    else if n == 161 { lut_entry_160(); }
    else if n == 162 { lut_entry_161(); }
    else if n == 163 { lut_entry_162(); }
    else if n == 164 { lut_entry_163(); }
    else if n == 165 { lut_entry_164(); }
    else if n == 166 { lut_entry_165(); }
    else if n == 167 { lut_entry_166(); }
    else if n == 168 { lut_entry_167(); }
    else if n == 169 { lut_entry_168(); }
    else if n == 170 { lut_entry_169(); }
    else if n == 171 { lut_entry_170(); }
    else if n == 172 { lut_entry_171(); }
    else if n == 173 { lut_entry_172(); }
    else if n == 174 { lut_entry_173(); }
    else if n == 175 { lut_entry_174(); }
    else if n == 176 { lut_entry_175(); }
    else if n == 177 { lut_entry_176(); }
    else if n == 178 { lut_entry_177(); }
    else if n == 179 { lut_entry_178(); }
    else if n == 180 { lut_entry_179(); }
    else if n == 181 { lut_entry_180(); }
    else if n == 182 { lut_entry_181(); }
    else if n == 183 { lut_entry_182(); }
    else if n == 184 { lut_entry_183(); }
    else if n == 185 { lut_entry_184(); }
    else if n == 186 { lut_entry_185(); }
    else if n == 187 { lut_entry_186(); }
    else if n == 188 { lut_entry_187(); }
    else if n == 189 { lut_entry_188(); }
    else if n == 190 { lut_entry_189(); }
    else if n == 191 { lut_entry_190(); }
    else if n == 192 { lut_entry_191(); }
    else if n == 193 { lut_entry_192(); }
    else if n == 194 { lut_entry_193(); }
    else if n == 195 { lut_entry_194(); }
    else if n == 196 { lut_entry_195(); }
    else if n == 197 { lut_entry_196(); }
    else if n == 198 { lut_entry_197(); }
    else if n == 199 { lut_entry_198(); }
    else if n == 200 { lut_entry_199(); }
    else if n == 201 { lut_entry_200(); }
    else if n == 202 { lut_entry_201(); }
    else if n == 203 { lut_entry_202(); }
    else if n == 204 { lut_entry_203(); }
    else if n == 205 { lut_entry_204(); }
    else if n == 206 { lut_entry_205(); }
    else if n == 207 { lut_entry_206(); }
    else if n == 208 { lut_entry_207(); }
    else if n == 209 { lut_entry_208(); }
    else if n == 210 { lut_entry_209(); }
    else if n == 211 { lut_entry_210(); }
    else if n == 212 { lut_entry_211(); }
    else if n == 213 { lut_entry_212(); }
    else if n == 214 { lut_entry_213(); }
    else if n == 215 { lut_entry_214(); }
    else if n == 216 { lut_entry_215(); }
    else if n == 217 { lut_entry_216(); }
    else if n == 218 { lut_entry_217(); }
    else if n == 219 { lut_entry_218(); }
    else if n == 220 { lut_entry_219(); }
    else if n == 221 { lut_entry_220(); }
    else if n == 222 { lut_entry_221(); }
    else if n == 223 { lut_entry_222(); }
    else if n == 224 { lut_entry_223(); }
    else if n == 225 { lut_entry_224(); }
    else if n == 226 { lut_entry_225(); }
    else if n == 227 { lut_entry_226(); }
    else if n == 228 { lut_entry_227(); }
    else if n == 229 { lut_entry_228(); }
    else if n == 230 { lut_entry_229(); }
    else if n == 231 { lut_entry_230(); }
    else if n == 232 { lut_entry_231(); }
    else if n == 233 { lut_entry_232(); }
    else if n == 234 { lut_entry_233(); }
    else if n == 235 { lut_entry_234(); }
    else if n == 236 { lut_entry_235(); }
    else if n == 237 { lut_entry_236(); }
    else if n == 238 { lut_entry_237(); }
    else if n == 239 { lut_entry_238(); }
    else if n == 240 { lut_entry_239(); }
    else if n == 241 { lut_entry_240(); }
    else if n == 242 { lut_entry_241(); }
    else if n == 243 { lut_entry_242(); }
    else if n == 244 { lut_entry_243(); }
    else if n == 245 { lut_entry_244(); }
    else if n == 246 { lut_entry_245(); }
    else if n == 247 { lut_entry_246(); }
    else if n == 248 { lut_entry_247(); }
    else if n == 249 { lut_entry_248(); }
    else if n == 250 { lut_entry_249(); }
    else if n == 251 { lut_entry_250(); }
    else if n == 252 { lut_entry_251(); }
    else if n == 253 { lut_entry_252(); }
    else if n == 254 { lut_entry_253(); }
    else if n == 255 { lut_entry_254(); }
    else if n == 256 { lut_entry_255(); }
  }
}
