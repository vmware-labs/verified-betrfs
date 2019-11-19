include "../lib/MutableMap.i.dfy"
include "../lib/NativeTypes.s.dfy"

module Main {
  import opened NativeTypes
  import opened MutableMap

  method Main() {
    var hashMap := new ResizingHashMap<uint64>(1024 * 1024);
    assert hashMap.Inv();
    assert fresh(hashMap);

    var nInsertions := 1000 * 1000 * 50;

    var i: uint64 := 0;
    while i < nInsertions
      invariant hashMap.Inv()
      invariant hashMap.Count <= i
      invariant fresh(hashMap)
      invariant fresh(hashMap.Repr)
    {
      if i % 1000000 == 0 {
        print "Inserting ", i, "\n";
      }
      var v := (i * 1073741827) % nInsertions;
      assert fresh(hashMap);
      assert hashMap.Count as nat < 0x10000000000000000 / 8;
      var _ := hashMap.Insert(v, v); // if this wasn't fresh, we'd need to add it to the modifies clause
                                     // but this is main, and hashMap is freshly allocated in this method
                                     // guaranteed non-aliasing probably allows for easier reasoning here
      assert fresh(hashMap);
      assert v in hashMap.Contents && hashMap.Contents[v] == v;
      if i >= 1000000 {
        var vn := ((i - 1000000) * 1073741827) % nInsertions;
        var _ := hashMap.Remove(vn);
      }
      i := i + 1;
      assert fresh(hashMap);
    }
    print i;
  }
}
