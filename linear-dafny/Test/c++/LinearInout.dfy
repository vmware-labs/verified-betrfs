  
include "LinearSequence.s.dfy"

module LinearInout {

import opened Types 
import opened LinearMaybe 
import opened LinearLSeq

linear datatype Val0 = Leaf(x:bool) //| Branch(linear v:Val0)

method do_something(linear inout m:Val0)
ensures m.x == true
{
  inout m.x := true;
}

method test(linear inout m:Val0) 
ensures m.x == true
{
  do_something(inout m);
}

method Main() {
  linear var v := Leaf(false);
  do_something(inout v);
  var b := v.x;
  assert b;
  print b;
  linear var Leaf(_) := v;
}

/*
function lseqs<A>(l:lseq<A>):(s:seq<A>)
  ensures rank_is_less_than(s, l)
  ensures |s| == |lseqs_raw(l)|
{
  var s := seq(|lseqs_raw(l)|, i requires 0 <= i < |lseqs_raw(l)| => read(lseqs_raw(l)[i]));
  axiom_lseqs_rank(l, s);
  s
}

function lseq_has<A>(l:lseq<A>):(s:seq<bool>)
    ensures |s| == |lseqs_raw(l)|
{
  seq(|lseqs_raw(l)|, i requires 0 <= i < |lseqs_raw(l)| => has(lseqs_raw(l)[i]))
}

method lseq_swap_inout<A>(linear inout s:lseq<A>, i:uint64, linear a1:A) returns(linear a2:A)
    requires i as int < |lseqs(old_s)|
    requires lseq_has(old_s)[i]
//    ensures a2 == lseqs(s)[i]
//    ensures lseqs(s) == lseqs(old_s)[i as int := a1]
//    requires i as nat < |old_s| && i as nat in old_s
//    ensures a2 == s[i as nat]
//    ensures lseq_has(s) == lseq_has(old_s)
//    ensures lseqs(s) == lseqs(old_s)[i as nat := a1]
{
  //s, a2 := lseq_swap(s, i, a1);
  linear var x1:maybe<A> := give(a1);
  linear var (s2tmp, x2) := lseq_swap_raw_fun(s, i, x1);
  s := s2tmp;
  a2 := unwrap(x2);
}
*/

}
