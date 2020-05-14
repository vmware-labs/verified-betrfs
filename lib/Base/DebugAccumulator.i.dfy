include "NativeTypes.s.dfy"

// Used for counting up instances of objects, while debugging some
// memory leaks in the GC implementation. (Looking forward to Rust
// & explicit memory management.)
module DebugAccumulator {
  import opened NativeTypes

  class AccRec {
    var key:string;
    var count:uint64;
    var unit:string;
    var index:DebugAccumulator;

    constructor(count:uint64, unit:string)
    {
      this.count := count;
      this.unit := unit;
    }

    constructor Index(index:DebugAccumulator)
    {
      this.count := 0;
      this.unit := "";
      this.index := index;
    }

    method doPrint(indent:uint64)
    requires false
    {
      var i := doIndent(indent);
      print i, this.key, ": ", this.count, " ", this.unit, "\n";
      Display(this.index, indent+2);
    }
  }

  method doIndent(indent:uint64) returns (s:string)
  requires false
  {
    var x:uint64 := 0;
    s := "";
    while x <  indent {
      s := s + " ";
      x := x + 1;
    }
  }

//  datatype AccRec = AccRec(count:uint64, unit:string)
//    | AccIndex(acc:DebugAccumulator)
  type DebugAccumulator = seq<AccRec>
  function method EmptyAccumulator() : DebugAccumulator
  {
    []
  }
  method AccPut(acc: DebugAccumulator, key:string, rec:AccRec) returns (out:DebugAccumulator)
  requires false
  {
    rec.key := key;
    out := acc + [rec];
  }

  method Display(a:DebugAccumulator, indent: uint64)
  requires false
  {
    var i:uint64 := 0;
    while i < |a| as uint64 {
      a[i].doPrint(indent);
      i := i + 1;
    }
  }
}
