method Main() {
  var v: bv64 := 0xffff_ff00_ffff_ffff;
  print v & (0xffff_ffff_ffff_ffff ^ (1 << 16));
}
