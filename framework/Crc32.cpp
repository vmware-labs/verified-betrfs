// Needs to be compiled with -msse4.2

// From https://github.com/komrad36/CRC
// TODO verify this

#include <iostream>
#include <cstring>
#include <cstdint>
#include <smmintrin.h>
#include <immintrin.h>
#include "DafnyRuntime.h"
#include "Framework.h"

using namespace std;

//constexpr int32_t P = 0x82f63b78;

static constexpr uint64_t g_lut_intel[] = {
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
};

/*void compute_golden_lut_intel(uint32_t* tbl, uint32_t n) {
  uint32_t R = 1;
  for (uint32_t i = 0; i < n << 1; ++i) {
    tbl[i] = R;
    for (uint32_t j = 0; j < 64; j++) {
      R = R & 1 ? (R >> 1) ^ P : R >> 1;
    }
  }
}

void print_golden_lut_intel(uint32_t* tbl, uint32_t n) {
  printf("static constexpr uint64_t g_lut_intel[] = {\n");
  for (uint32_t i = 0; i < n; ++i) {
    printf("0x%08x%08x,%c", tbl[i], tbl[(i << 1) + 1], (i & 3) == 3 ? '\n' : ' ');
  }
  printf("};\n");
}

void golden_lut_print_demo_intel() {
  constexpr uint32_t n = 256;
  uint32_t* tbl = new uint32_t[n << 1];
  compute_golden_lut_intel(tbl, n);
  print_golden_lut_intel(tbl, n);
  delete tbl;
}*/

#define CRC_ITER(i) \
crcA = _mm_crc32_u64(crcA, *(uint64_t*)(pA - 8*(i)));   \
crcB = _mm_crc32_u64(crcB, *(uint64_t*)(pB - 8*(i)));   \
crcC = _mm_crc32_u64(crcC, *(uint64_t*)(pC - 8*(i)));

#define X0(n) CRC_ITER(n);
#define X1(n) X0(n+1) X0(n)
#define X2(n) X1(n+2) X1(n)
#define X3(n) X2(n+4) X2(n)
#define X4(n) X3(n+8) X3(n)
#define X5(n) X4(n+16) X4(n)
#define X6(n) X5(n+32) X5(n)
#define X7(n) X6(n+64) X6(n)
#define CRC_ITERS_256_TO_2() do {X0(256) X1(254) X2(250) X3(242) X4(226) X5(194) X6(130) X7(2)} while(0)

// must be >= 24
constexpr uint32_t LEAF_SIZE_INTEL = 6 * 24;

// OPTION 13
uint32_t option_13_golden_intel(const void* M, uint32_t bytes, uint32_t prev = 0) {
  uint64_t pA = (uint64_t)M;
  //uint64_t crcA = (uint64_t)(uint32_t)(~prev); // if you want to invert prev
  uint64_t crcA = prev;
  uint32_t toAlign = ((uint64_t)-(int64_t)pA) & 7;

  for (; toAlign && bytes; ++pA, --bytes, --toAlign)
    crcA = _mm_crc32_u8((uint32_t)crcA, *(uint8_t*)pA);

  while (bytes >= LEAF_SIZE_INTEL) {
    const uint32_t n = bytes < 256 * 24 ? bytes * 2731 >> 16 : 256;
    pA += 8 * n;
    uint64_t pB = pA + 8 * n;
    uint64_t pC = pB + 8 * n;
    uint64_t crcB = 0, crcC = 0;
    if (n == 256) {
      CRC_ITERS_256_TO_2();
    } else {
      for (int z = n; z >= 2; z--) {
        crcA = _mm_crc32_u64(crcA, *(uint64_t*)(pA - 8*(z)));
        crcB = _mm_crc32_u64(crcB, *(uint64_t*)(pB - 8*(z)));
        crcC = _mm_crc32_u64(crcC, *(uint64_t*)(pC - 8*(z)));
      }
    }

    crcA = _mm_crc32_u64(crcA, *(uint64_t*)(pA - 8));
    crcB = _mm_crc32_u64(crcB, *(uint64_t*)(pB - 8));
    const __m128i vK = _mm_cvtepu32_epi64(_mm_loadu_si128((__m128i*)(&g_lut_intel[n - 1])));
    const __m128i vA = _mm_clmulepi64_si128(_mm_cvtsi64_si128(crcA), vK, 0);
    const __m128i vB = _mm_clmulepi64_si128(_mm_cvtsi64_si128(crcB), vK, 16);
    crcA = _mm_crc32_u64(crcC, _mm_cvtsi128_si64(_mm_xor_si128(vA, vB)) ^ *(uint64_t*)(pC - 8));

    bytes -= 24 * n;
    pA = pC;
  }

  for (; bytes >= 8; bytes -= 8, pA += 8)
    crcA = _mm_crc32_u64(crcA, *(uint64_t*)(pA));

  for (; bytes; --bytes, ++pA)
    crcA = _mm_crc32_u8((uint32_t)crcA, *(uint8_t*)(pA));

  //return ~(uint32_t)crcA; // if you want to invert the result
  return (uint32_t)crcA;
}

/*uint32_t crc32c(const uint8_t *bytes, size_t len)
{
  uint32_t acc = 0xffffffff;

  while (((uintptr_t)bytes) & 0x7 && len > 0) {
    acc = _mm_crc32_u8(acc, *bytes);
    bytes++;
    len--;
  }

  while (len >= 8) {
    acc = _mm_crc32_u64(acc, *((const uint64_t *)bytes));
    len -= 8;
    bytes += 8;
  }

  if (len >= 4) {
    acc = _mm_crc32_u32(acc, *((const uint32_t *)bytes));
    len -= 4;
    bytes += 4;
  }

  if (len >= 2) {
    acc = _mm_crc32_u16(acc, *((const uint16_t *)bytes));
    len -= 2;
    bytes += 2;
  }

  if (len >= 1) {
    acc = _mm_crc32_u8(acc, *bytes);
    len -= 1;
    bytes += 1;
  }

  return ~acc;
}*/

namespace Crypto_Compile {
  DafnySequence<uint8_t> padded_crc32(uint8_t* bytes, int len)
  {
    //uint32_t crc = crc32c(bytes, len);
    uint32_t crc = ~option_13_golden_intel(bytes, len, 0xffffffff);

    DafnySequence<uint8_t> padded(32);
    padded.ptr()[0] = (uint8_t)(crc & 0xff);
    padded.ptr()[1] = (uint8_t)((crc >> 8) & 0xff);
    padded.ptr()[2] = (uint8_t)((crc >> 16) & 0xff);
    padded.ptr()[3] = (uint8_t)((crc >> 24) & 0xff);
    for (int i = 4; i < 32; i++) {
      padded.ptr()[i] = 0;
    }

    return padded;
  }

  DafnySequence<uint8> __default::Crc32C(DafnySequence<uint8> bytes)
  {
    return padded_crc32(bytes.ptr(), bytes.size());
  }

  DafnySequence<uint8> __default::Crc32CArray(DafnyArray<uint8> bytes, uint64 start, uint64 len)
  {
    return padded_crc32(&bytes.at(start), len);
  }
}

/*int main() {
  const char* ch = "The quick brown fox jumps over the lazy dog";
  cout << crc32c((const uint8_t*)ch, strlen(ch)) << endl;
}*/
