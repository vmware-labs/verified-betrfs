module Loop {
newtype{:nativeType "ulong"} uint64 = i:int | 0 <= i < 0x1_0000_0000_0000_0000

linear datatype LinearBool = LinearBool(x: bool)

datatype Option<A> = Some(value: A) | None

method flip(linear inout v: LinearBool)
ensures v.x == !old_v.x
{
  inout v.x := !v.x;
}

method Main() {
  linear var b := LinearBool(false);
  var i: uint64 := 0;

  var o: Option<uint64> := Some(1);

  match o {
    case Some(p) => {
      while i < 10
      invariant i <= 10
      invariant i % 2 == 0 <==> !b.x
      {
        flip(inout b);
        i := i + p;
        var v := b.x;
        print v;
      }
      assert !b.x;
      var v := b.x;
      print v;
    }
    case None => assert false;
  }

  linear var LinearBool(_) := b;
}

}
