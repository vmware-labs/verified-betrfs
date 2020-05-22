include "../lib/DataStructures/LinearMutableMap.i.dfy"
include "../lib/Lang/NativeTypes.s.dfy"
include "../lib/Math/LinearCongruentialGenerator.s.dfy"

module MutableMapBench {
  import opened NativeTypes
  import opened LinearMutableMap
  import opened LinearCongruentialGenerator

  method Run(seed: uint64, nOperations: uint64, dry: bool)
  requires nOperations as nat < 0x10000000000000000 / 8
  {
    linear var hashMap := LinearMutableMap.Constructor(1024 * 1024);
    var lcg: LCG := new LCG(seed);
    var lcg2: LCG := new LCG(seed);

    var i: uint64 := 0;
    var write_start: uint64 := steadyClockMillis();
    while i < nOperations
      invariant LinearMutableMap.Inv(hashMap)
      invariant hashMap.count <= i
      invariant {lcg} !! {lcg2}
    {
      if i % 1000000 == 0 {
        print "Inserting ", i, "\n";
      }
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
      if !dry && i >= 1000000 {
        var vn := lcg2.next();
        hashMap := LinearMutableMap.Remove(hashMap, vn);
      }
      i := i + 1;
    }
    print i;
    var write_end: uint64 := steadyClockMillis();
    assume write_end >= write_start;
    var write_duration: uint64 := write_end - write_start;
    print(nOperations, "\twrite\tlinear\t", write_duration, "\n");

    i := 0;

    var read_start: uint64 := steadyClockMillis();
    while i < nOperations
      invariant 0 <= i <= nOperations
      invariant LinearMutableMap.Inv(hashMap)
      invariant {lcg} !! {lcg2}
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
    var read_end: uint64 := steadyClockMillis();
    assume read_end >= read_start;
    var read_duration: uint64 := read_end - read_start;
    print(nOperations, "\tread\tlinear\t", read_duration, "\n");

    LinearMutableMap.Destructor(hashMap);
  }
}
