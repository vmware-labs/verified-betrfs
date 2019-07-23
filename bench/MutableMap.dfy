include "../lib/MutableMap.dfy"
include "../lib/NativeTypes.dfy"

module Main {
  import opened NativeTypes
  import opened MutableMap

  method Main() {
    var hashMap := new ResizingHashMap<uint64>(1024 * 1024);
    assert hashMap.Inv();

    var nInsertions := 1000 * 1000 * 50;

    var i: uint64 := 0;
    while i < nInsertions
      invariant hashMap.Inv()
    {
      if i % 1000000 == 0 {
        print "Inserting ", i, "\n";
      }
      var v := (i * 1073741827) % nInsertions;
      var _ := hashMap.Insert(v, v);
      assert v in hashMap.Contents && hashMap.Contents[v] == v;
      if i >= 1000000 {
        var vn := ((i - 1000000) * 1073741827) % nInsertions;
        var _ := hashMap.Remove(vn);
      }
      i := i + 1;
    }
    print i;
  }
}
