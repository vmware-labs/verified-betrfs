// RUN: %dafny /compile:3 /spillTargetCode:2 /compileTarget:cpp LinearExtern.h "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

include "linearSequence.s.dfy"
import opened LinearSequences

newtype{:nativeType "ulong"} uint64 = i:int | 0 <= i < 0x10000000000000000

method MethodLinearSeqReturn1()
returns (linear l: seq<uint64>)
ensures |l| == 5
{
  l := seq_alloc(5);
  l := seq_set(l, 0, 0);
}

method MethodLinearSeqReturn2()
returns (linear l1: seq<uint64>, linear l2: seq<uint64>)
ensures |l1| == 5
ensures |l2| == 5
{
  l1 := seq_alloc(5);
  l2 := seq_alloc(5);

  l1 := seq_set(l1, 0, 0);
  l2 := seq_set(l2, 0, 0);
}

method TestMethodLinearSeqReturn()
{
  print "TestMethodLinearSeqReturn\n";
  linear var s := MethodLinearSeqReturn1();
  linear var t, u := MethodLinearSeqReturn2();

  var s0 := seq_get(s, 0);
  var t0 := seq_get(t, 0);
  var u0 := seq_get(u, 0);

  print s0, "\n";
  print t0, "\n";
  print u0, "\n";

  var f1 := seq_free(s);
  f1 := seq_free(t);
  f1 := seq_free(u);

  print "----\n";
}

method Main()
{
  TestMethodLinearSeqReturn();
}
