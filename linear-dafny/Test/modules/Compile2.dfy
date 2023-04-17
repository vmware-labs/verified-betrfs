// RUN: %dafny /compile:4 /compileTarget:cpp /spillTargetCode:3 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

abstract module TotalOrder {
  type V
  predicate le(a: V, b: V)
  lemma le_self(a: V)
  ensures le(a, a)
  lemma le_transitive(a: V, b: V, c: V)
  ensures le(a, b) && le(b, c) ==> le(a, c)
}
abstract module TotalOrderImpl(to: TotalOrder) {
  method compute_le(x: to.V, y: to.V)
  returns (b: bool)
  ensures b == to.le(x, y)
}
module IntTotalOrder refines TotalOrder {
  newtype uint32 = i:int | 0 <= i < 0x100000000
  type V = uint32
  predicate le(a: V, b: V) { a <= b }
  lemma le_self(a: V) { }
  lemma le_transitive(a: V, b: V, c: V) { }
}
module IntTotalOrderImpl refines TotalOrderImpl(IntTotalOrder) {
  method compute_le(x: to.V, y: to.V)
  returns (b: bool)
  ensures b == to.le(x, y)
  {
    b := x <= y;
  }
}
module TotalOrderUtils(to: TotalOrder, toi: TotalOrderImpl(to)) {
  method get_max(x: to.V, y: to.V)
  returns (z: to.V)
  {
    var b := toi.compute_le(x, y);
    if b {
      return y;
    } else {
      return x;
    }
  }
}
import ITOI = IntTotalOrderImpl
import IntTOU = TotalOrderUtils(IntTotalOrder, IntTotalOrderImpl)
method Main() {
  var x := 5;
  var y := 7;
  var b := ITOI.compute_le(x, y);
  print b, "\n";
  var z := IntTOU.get_max(x, y);
  print z, "\n";
}
