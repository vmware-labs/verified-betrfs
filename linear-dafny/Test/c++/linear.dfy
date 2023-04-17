
include "LinearSequence.s.dfy"
import opened Types
import opened LinearMaybe
import opened LinearSequences
import opened LinearLSeq

linear datatype Node =
  Leaf(linear keys: seq<uint64>, linear values: seq<uint64>)
//  | Index(linear pivots: seq<uint64>, linear children: lseq<uint64>)

function method LinearReturn(linear s:seq<uint64>) : linear seq<uint64>
{
  s
}

method TestLinearRet(linear s:seq<uint64>) returns (linear s':seq<uint64>)
{
  s' := LinearReturn(s);
}

linear datatype Val0 = Leaf(x:uint64) | Branch(linear v:Val0)
datatype Val1 = Leaf(x:uint64) | Branch(v:Val1)

method Test(name:string, b:bool)
  requires b;
{
  if b {
    print name, ": This is expected\n";
  } else {
    print name, ": This is *** UNEXPECTED *** !!!!\n";
  }
}

/*
// Disallowed because operator== expects ordinary arguments
method LinearMaybeEqualityTest(linear a:maybe<uint64>, linear b:maybe<uint64>)
  requires has(a) && !has(b);
{
  var bar := a == b;
  print "Maybe equality is ", bar;

  var i := unwrap(a);
  DiscardLinearInt(i);
  var _ := discard(b);
}

// Disallowed here because type lseq is not type(==)
method LinearLSeqEqualityTest()
{
  var a:lseq<uint64>, b:lseq<uint64>;
  var result := a == b;
  print result;
}
*/

//newtype{:nativeType "ulong"} uint64 = i:int | 0 <= i < 0x10000000000000000
//
//function method {:extern "LinearExtern", "seq_alloc"} seq_alloc<A>(length:uint64):(linear s:seq<A>)
//function method {:extern "LinearExtern", "seq_free"} seq_free<A>(linear s:seq<A>):()
//

method TestLinearSequences()
{
  linear var s0 := seq_alloc<uint64>(10);
  var x := seq_get(s0, 0);
  print x;
  print "\n";
  linear var s1 := seq_set(s0, 0, 42);
//  x := seq_get(s0, 0);   // Fails linearity check
//  print x;
  Test("Test result of set", seq_get(s1, 0) == 42);
  linear var s2 := seq_set(s1, 0, 24);
  Test("Test result of set again", seq_get(s2, 0) == 24);
//  Test("Test length", seq_length(s1) == 10);  // Fails linearity check
  Test("Test length", seq_length(s2) == 10);
  var s3 := seq_unleash(s2);
  Test("Normal seq", s3[0] == 24);

  linear var t0 := seq_alloc<uint64>(5);
  linear var t1 := seq_set(t0, 4, 732);
  var _ := seq_free(t1);
}

method PassLinearSharedSequences(linear s:seq<uint64>, shared t:seq<uint64>) returns (shared t':seq<uint64>)
{
  var _ := seq_free(s);
  t' := t;
}

method TestPeek(shared u:maybe<uint64>)
  requires has(u)
{
  shared var val := peek(u);
}

method TestLinearMaybe(linear u:uint64) returns (linear x:uint64)
{
  linear var m := give(u);
  linear var e := empty<uint64>();

//  shared var m_val := peek(m);
//  shared var e_val := peek(e);
  TestPeek(m);
  //TestPeek(e);    // !has(e)

  linear var m_unwrapped := unwrap(m);
  //linear var e_unwrapped := unwrap(e);

  x := m_unwrapped;
  var _ := discard(e);
}

method {:extern "LinearExtern", "MakeLinearInt"} MakeLinearInt(u:uint64) returns (linear x:uint64)
method {:extern "LinearExtern", "DiscardLinearInt"} DiscardLinearInt(linear u:uint64)

lemma {:axiom} falso()
  ensures false;

method AccessShared(shared s:lseq<uint64>)
  requires lseq_length_raw(s) > 1
  requires has(lseq_share_raw(s, 0))
{
  shared var m := lseq_share_raw(s, 0);
  shared var a := peek(m);
}

method TestLSeq()
{
  linear var s := lseq_alloc_raw<uint64>(10);
  var len := lseq_length_raw(s);
  print len;
  print "\n";

  linear var u := MakeLinearInt(24);
  linear var m := give(u);
  linear var (s', m') := lseq_swap_raw_fun(s, 0, m);

  AccessShared(s');

  linear var (s'', m'') := lseq_swap_raw_fun(s', 0, m');
  falso();    // Skip proofs about has
  var _ := discard(m'');
  var _ := lseq_free_raw(s'');
}

type {:extern "predefined"} T

method ExpectsSharedT(shared t: T) {
}

method ProvidesSharedT(linear t: T) returns (linear t': T) {
  ExpectsSharedT(t);
  t' := t;
}

method Main()
{
  TestLinearSequences();
  linear var x := MakeLinearInt(42);
  linear var y := TestLinearMaybe(x);
  DiscardLinearInt(y);

//  linear var a := MakeLinearInt(12);
//  linear var m_a := give(a);
//  linear var m_b := empty<uint64>();
//  LinearMaybeEqualityTest(m_a, m_b);
}
