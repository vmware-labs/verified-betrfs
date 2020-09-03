include "../lib/DataStructures/LinearMutableMap.i.dfy"
include "../lib/Lang/NativeTypes.s.dfy"
include "../lib/Math/LinearCongruentialGenerator.s.dfy"

module MutableMapBench {
  import opened NativeTypes
  import opened LinearMutableMap
  import opened LinearCongruentialGenerator

  method Run(seed: uint64, dry: bool)
  {
    linear var hashMap := LinearMutableMap.Constructor(1024 * 1024);
    var lcg: LCG := new LCG(seed);

    var nOperations: uint64 := 64000000;
    print("METADATA operations ", nOperations, "\n");

    // WRITE
    var i: uint64 := 0;
    var write_start: uint64 := steadyClockMillis();
    while i < nOperations
      invariant i <= nOperations
      invariant LinearMutableMap.Inv(hashMap)
      invariant hashMap.count <= i
    {
      var v := lcg.next();
      assert hashMap.count as nat < 0x10000000000000000 / 8;
      if (!dry) {
        hashMap := LinearMutableMap.Insert(hashMap, v, v); // if this wasn't fresh, we'd need to add it to the modifies clause
                                       // but this is main, and hashMap is freshly allocated in this method
                                       // guaranteed non-aliasing probably allows for easier reasoning here
      }
      if (!dry) {
        assert v in hashMap.contents && hashMap.contents[v] == v;
      }
      i := i + 1;
    }
    var write_end: uint64 := steadyClockMillis();
    assume write_end >= write_start;
    var write_duration: uint64 := write_end - write_start;
    print("insert\t", write_duration, "\n");

    assert hashMap.count <= nOperations;

    // READ POSITIVE
    i := 0;
    lcg := new LCG(seed);
    var readpositive_start: uint64 := steadyClockMillis();
    while i < nOperations
      invariant 0 <= i <= nOperations
      invariant LinearMutableMap.Inv(hashMap)
    {
      var keyv := lcg.next();
      if (!dry) {
        var result := LinearMutableMap.Get(hashMap, keyv);
        if result.Some? {
          opaqueBlackhole(result.value);
        }
      }
      i := i + 1;
    }
    var readpositive_end: uint64 := steadyClockMillis();
    assume readpositive_end >= readpositive_start;
    var readpositive_duration: uint64 := readpositive_end - readpositive_start;
    print("readpositive\t", readpositive_duration, "\n");

    // READ POSITIVE
    i := 0;
    assume seed as nat + 1 < 0x1_0000_0000_0000_0000;
    lcg := new LCG(seed + 1);
    var readnegative_start: uint64 := steadyClockMillis();
    while i < nOperations
      invariant 0 <= i <= nOperations
      invariant LinearMutableMap.Inv(hashMap)
    {
      var keyv := lcg.next();
      if (!dry) {
        var result := LinearMutableMap.Get(hashMap, keyv);
        if result.Some? {
          opaqueBlackhole(result.value);
        }
      }
      i := i + 1;
    }
    var readnegative_end: uint64 := steadyClockMillis();
    assume readnegative_end >= readnegative_start;
    var readnegative_duration: uint64 := readnegative_end - readnegative_start;
    print("readnegative\t", readnegative_duration, "\n");

    // EMPTY (REMOVE POSITIVE)
    i := 0;
    lcg := new LCG(seed);
    var remove_start: uint64 := steadyClockMillis();
    while i < nOperations
      invariant i <= nOperations
      invariant LinearMutableMap.Inv(hashMap)
      invariant hashMap.count <= nOperations
    {
      var v := lcg.next();
      if (!dry) {
        hashMap := LinearMutableMap.Remove(hashMap, v);
        assert !(v in hashMap.contents);
      }
      i := i + 1;
    }
    var remove_end: uint64 := steadyClockMillis();
    assume remove_end >= remove_start;
    var remove_duration: uint64 := remove_end - remove_start;
    print("remove\t", remove_duration, "\n");

    LinearMutableMap.Destructor(hashMap);
  }
}
