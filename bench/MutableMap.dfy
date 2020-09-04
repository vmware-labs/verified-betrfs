include "../lib/DataStructures/MutableMapImpl.i.dfy"
include "../lib/Base/NativeTypes.s.dfy"
include "../lib/Math/LinearCongruentialGenerator.s.dfy"

module MutableMapBench {
  import opened NativeTypes
  import opened MutableMap
  import opened LinearCongruentialGenerator

  method Run(seed: uint64, dry: bool)
    requires false
  {
    var hashMap := new ResizingHashMap<uint64>(1024 * 1024);
    assert hashMap.Inv();
    assert fresh(hashMap);
    var lcg: LCG := new LCG(seed);

    var nOperations: uint64 := 64000000;
    print("METADATA operations ", nOperations, "\n");

    // WRITE
    var i: uint64 := 0;
    var write_start: uint64 := steadyClockMillis();
    while i < nOperations
      invariant i <= nOperations
      invariant hashMap.Inv()
      invariant hashMap.Count <= i
      invariant fresh(hashMap)
      invariant fresh(hashMap.Repr)
      invariant {lcg} !! hashMap.Repr
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
      i := i + 1;
      assert fresh(hashMap);
    }
    var write_end: uint64 := steadyClockMillis();
    var write_duration: uint64 := write_end - write_start;
    print("insert\t", write_duration, "\n");

    assert hashMap.Count <= nOperations;

    // READ POSITIVE
    i := 0;
    lcg := new LCG(seed);
    var readpositive_start: uint64 := steadyClockMillis();
    while i < nOperations
      invariant 0 <= i <= nOperations
      invariant hashMap.Count <= nOperations
      invariant hashMap.Inv()
      invariant fresh(hashMap)
      invariant fresh(hashMap.Repr)
      invariant {lcg} !! hashMap.Repr
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
    var readpositive_end: uint64 := steadyClockMillis();
    var readpositive_duration: uint64 := readpositive_end - readpositive_start;
    print("readpositive\t", readpositive_duration, "\n");

    // READ NEGATIVE
    i := 0;
    lcg := new LCG(seed + 1);
    var readnegative_start: uint64 := steadyClockMillis();
    while i < nOperations
      invariant 0 <= i <= nOperations
      invariant hashMap.Count <= nOperations
      invariant hashMap.Inv()
      invariant fresh(hashMap)
      invariant fresh(hashMap.Repr)
      invariant {lcg} !! hashMap.Repr
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
    var readnegative_end: uint64 := steadyClockMillis();
    var readnegative_duration: uint64 := readnegative_end - readnegative_start;
    print("readnegative\t", readnegative_duration, "\n");

    // EMTPY (REMOVE POSITIVE)
    i := 0;
    lcg := new LCG(seed);
    var remove_start: uint64 := steadyClockMillis();
    while i < nOperations
      invariant hashMap.Inv()
      invariant hashMap.Count <= nOperations
      invariant fresh(hashMap)
      invariant fresh(hashMap.Repr)
      invariant {lcg} !! hashMap.Repr
    {
      var vn := lcg.next();
      if (!dry) {
        hashMap.Remove(vn);
        assert !(vn in hashMap.Contents);
      }
      i := i + 1;
    }
    var remove_end: uint64 := steadyClockMillis();
    var remove_duration: uint64 := remove_end - remove_start;
    print("remove\t", remove_duration, "\n");

  }
}
