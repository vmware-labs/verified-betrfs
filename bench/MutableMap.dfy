include "../lib/DataStructures/MutableMapImpl.i.dfy"
include "../lib/Base/NativeTypes.s.dfy"
include "../lib/Math/LinearCongruentialGenerator.s.dfy"

module MutableMapBench {
  import opened NativeTypes
  import opened MutableMap
  import opened LinearCongruentialGenerator

  method Run(seed: uint64, nOperations: uint64, dry: bool)
  requires nOperations as nat < 0x10000000000000000 / 8
  {
    var hashMap := new ResizingHashMap<uint64>(1024 * 1024);
    assert hashMap.Inv();
    assert fresh(hashMap);
    var lcg: LCG := new LCG(seed);
    var lcg2: LCG := new LCG(seed);

    var i: uint64 := 0;
    var write_start: uint64 := steadyClockMillis();
    while i < nOperations
      invariant hashMap.Inv()
      invariant hashMap.Count <= i
      invariant fresh(hashMap)
      invariant fresh(hashMap.Repr)
      invariant {lcg} !! {lcg2} !! hashMap.Repr
    {
      var v := lcg.next();
      assert fresh(hashMap);
      assert hashMap.Count as nat < 0x10000000000000000 / 8;
      if (!dry) {
        hashMap.Insert(v, v); // if this wasn't fresh, we'd need to add it to the modifies clause
                                       // but this is main, and hashMap is freshly allocated in this method
                                       // guaranteed non-aliasing probably allows for easier reasoning here
      }
      assert fresh(hashMap);
      if (!dry) {
        assert v in hashMap.Contents && hashMap.Contents[v] == v;
      }
      if !dry && i >= 1000000 {
        var vn := lcg2.next();
        hashMap.Remove(vn);
      }
      i := i + 1;
      assert fresh(hashMap);
    }
    print i;
    var write_end: uint64 := steadyClockMillis();
    assume write_end >= write_start;
    var write_duration: uint64 := write_end - write_start;
    print(nOperations, "\twrite\trepr\t", write_duration, "\n");

    i := 0;

    var read_start: uint64 := steadyClockMillis();
    while i < nOperations
      invariant 0 <= i <= nOperations
      invariant hashMap.Inv()
      invariant {lcg} !! {lcg2} !! hashMap.Repr
    {
      var keyv := lcg.next();
      if (!dry) {
        var result := hashMap.Get(keyv);
        if result.Some? {
          opaqueBlackhole(result.value);
        }
      }
      i := i + 1;
    }
    var read_end: uint64 := steadyClockMillis();
    assume read_end >= read_start;
    var read_duration: uint64 := read_end - read_start;
    print(nOperations, "\tread\trepr\t", read_duration, "\n");
  }
}
