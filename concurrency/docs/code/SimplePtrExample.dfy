include "Ptrs.s.dfy"

import opened Ptrs

method Main() {
  var ptr;
  glinear var points_to;

  ptr, points_to := alloc(5);

  // read a value, check that it is 5:
  var r := ptr.read(points_to);
  assert r == 5;

  // write a value
  ptr.write(inout points_to, 9);

  // we managed to update its value to 9:
  assert points_to.v == 9;

  // ... which can we see if we read it again:
  var q := ptr.read(points_to);
  assert q == 9;

  // free memory
  ptr.free(points_to);
}
