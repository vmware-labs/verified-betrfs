include "Option.s.dfy"
include "NativeTypes.s.dfy"

module Sequences {
  import opened Options
  import opened NativeTypes

  function Last<E>(run: seq<E>) : E
    requires |run| > 0;
  {
    run[|run|-1]
  }

  function DropLast<E>(run: seq<E>) : seq<E>
    requires |run| > 0;
  {
    run[..|run|-1]
  }

  function Set<T>(run: seq<T>) : set<T> {
    set x : T | x in multiset(run)
  }
  
  function ISet<T>(run: seq<T>) : iset<T> {
    iset x : T | x in multiset(run)
  }
  
  predicate {:opaque} NoDupes<T>(a: seq<T>) {
    (forall i, j :: 0 <= i < |a| && 0 <= j < |a| && i != j ==> a[i] != a[j])
  }

  lemma DisjointConcatenation<T>(a: seq<T>, b: seq<T>)
    requires NoDupes(a);
    requires NoDupes(b);
    requires multiset(a) !! multiset(b);
    ensures NoDupes(a + b);
  {
    reveal_NoDupes();
    var c := a + b;
    if |c| > 1 {
      assert forall i, j :: i != j && 0 <= i < |a| && |a| <= j < |c| ==>
        c[i] in multiset(a) && c[j] in multiset(b) && c[i] != c[j]; // Observe
    }
  }

  function IndexOf<T>(s: seq<T>, e: T) : int
    requires e in s;
    ensures 0 <= IndexOf(s,e) < |s|;
    ensures s[IndexOf(s,e)] == e;
  {
    var i :| 0 <= i < |s| && s[i] == e;
    i
  }

  function {:opaque} Range(n: int) : seq<int>
    requires n >= 0
    ensures |Range(n)| == n
    ensures forall i | 0 <= i < n :: Range(n)[i] == i
  {
    if n == 0 then [] else Range(n-1) + [n-1]
  }
  
  function Apply<E,R>(f: (E ~> R), run: seq<E>) : (result: seq<R>)
    requires forall i :: 0 <= i < |run| ==> f.requires(run[i])
    ensures |result| == |run|
    ensures forall i :: 0 <= i < |run| ==> result[i] == f(run[i]);
    reads f.reads
  {
    if |run| == 0 then []
    else  [f(run[0])] + Apply(f, run[1..])
  }

  function Filter<E>(f : (E ~> bool), run: seq<E>) : (result: seq<E>)
    requires forall i :: 0 <= i < |run| ==> f.requires(run[i])
    ensures |result| <= |run|
    ensures forall i: nat :: i < |result| && f.requires(result[i]) ==> f(result[i])
    reads f.reads
  {
    if |run| == 0 then []
    else ((if f(run[0]) then [run[0]] else []) + Filter(f, run[1..]))
  }
  
  function FoldLeft<A,E>(f: (A, E) -> A, init: A, run: seq<E>) : A
  {
    if |run| == 0 then init
    else FoldLeft(f, f(init, run[0]), run[1..])
  }

  function FoldRight<A,E>(f: (A, E) -> A, init: A, run: seq<E>) : A
  {
    if |run| == 0 then init
    else f(FoldRight(f, init, run[1..]), run[0])
  }

  function {:opaque} remove<A>(s: seq<A>, pos: int) : seq<A>
  requires 0 <= pos < |s|
  ensures |remove(s, pos)| == |s| - 1
  ensures forall i | 0 <= i < pos :: remove(s, pos)[i] == s[i]
  ensures forall i | pos <= i < |s| - 1 :: remove(s, pos)[i] == s[i+1]
  {
    s[.. pos] + s[pos + 1 ..]
  }

  function {:opaque} insert<A>(s: seq<A>, a: A, pos: int) : seq<A>
  requires 0 <= pos <= |s|;
  ensures |insert(s,a,pos)| == |s| + 1;
  ensures forall i :: 0 <= i < pos ==> insert(s, a, pos)[i] == s[i];
  ensures forall i :: pos <= i < |s| ==> insert(s, a, pos)[i+1] == s[i];
  ensures insert(s, a, pos)[pos] == a;
  {
    s[..pos] + [a] + s[pos..]
  }

  method Insert<A>(s: seq<A>, a: A, pos: uint64) returns (res: seq<A>)
  requires 0 <= pos as int <= |s|;
  ensures res == insert(s, a, pos as int);
  {
    return s[..pos] + [a] + s[pos..];
  }

  function {:opaque} replace1with2<A>(s: seq<A>, a: A, b: A, pos: int) : seq<A>
  requires 0 <= pos < |s|;
  ensures |replace1with2(s,a,b,pos)| == |s| + 1;
  ensures forall i :: 0 <= i < pos ==> replace1with2(s, a, b, pos)[i] == s[i];
  ensures forall i :: pos < i < |s| ==> replace1with2(s, a, b, pos)[i+1] == s[i];
  ensures replace1with2(s, a, b, pos)[pos] == a;
  ensures replace1with2(s, a, b, pos)[pos + 1] == b;
  {
    s[..pos] + [a, b] + s[pos+1..]
  }

  method Replace1with2<A>(s: seq<A>, a: A, b: A, pos: uint64) returns (res:seq<A>)
  requires 0 <= pos as int < |s|;
  requires pos < 0xffff_ffff_ffff_ffff
  ensures res == replace1with2(s, a, b, pos as int)
  {
    return s[..pos] + [a, b] + s[pos+1..];
  }

  function {:opaque} replace2with1<A>(s: seq<A>, a: A, pos: int) : seq<A>
  requires 0 <= pos < |s| - 1;
  ensures |replace2with1(s,a,pos)| == |s| - 1;
  ensures forall i :: 0 <= i < pos ==> replace2with1(s, a, pos)[i] == s[i];
  ensures forall i :: pos < i < |s| - 1 ==> replace2with1(s, a, pos)[i] == s[i+1];
  ensures replace2with1(s, a, pos)[pos] == a;
  {
    s[..pos] + [a] + s[pos+2..]
  }

  function {:opaque} concat<A>(a: seq<A>, b: seq<A>) : seq<A>
  ensures |concat(a,b)| == |a| + |b|
  ensures forall i :: 0 <= i < |a| ==> a[i] == concat(a,b)[i];
  ensures forall i :: 0 <= i < |b| ==> b[i] == concat(a,b)[|a| + i];
  {
    a + b
  }

  function {:opaque} concat3<A>(a: seq<A>, b: A, c: seq<A>) : seq<A>
  ensures |concat3(a,b,c)| == |a| + |c| + 1
  ensures forall i :: 0 <= i < |a| ==> a[i] == concat3(a,b,c)[i];
  ensures concat3(a,b,c)[|a|] == b;
  ensures forall i :: 0 <= i < |c| ==> c[i] == concat3(a,b,c)[|a| + 1 + i];
  {
    a + [b] + c
  }

  predicate {:opaque} IsPrefix<A(==)>(a: seq<A>, b: seq<A>) {
    && |a| <= |b|
    && a == b[..|a|]
  }

  predicate {:opaque} IsSuffix<A(==)>(a: seq<A>, b: seq<A>) {
    && |a| <= |b|
    && a == b[|b|-|a|..]
  }

  lemma SelfIsPrefix<A>(a: seq<A>)
  ensures IsPrefix(a, a);
  {
    reveal_IsPrefix();
  }

  lemma IsPrefixFromEqSums<A>(a: seq<A>, b: seq<A>, c: seq<A>, d: seq<A>)
  requires a + b == c + d
  requires IsSuffix(b, d);
  ensures IsPrefix(c, a);
  {
    reveal_IsPrefix();
    reveal_IsSuffix();
    assert |c| <= |a|;
    assert c
        == (c + d)[..|c|]
        == (a + b)[..|c|]
        == a[..|c|];
  }

  function {:opaque} SeqIndexIterate<A(==)>(run: seq<A>, needle: A, i: int) : (res : Option<int>)
  requires 0 <= i <= |run|
  ensures res.Some? ==> 0 <= res.value < |run| && run[res.value] == needle
  ensures res.None? ==> forall j | i <= j < |run| :: run[j] != needle
  decreases |run| - i
  {
    if i == |run| then None
    else if run[i] == needle then Some(i)
    else SeqIndexIterate(run, needle, i+1)
  }

  function {:opaque} SeqIndex<A(==)>(run: seq<A>, needle: A) : (res : Option<int>)
  ensures res.Some? ==> 0 <= res.value < |run| && run[res.value] == needle
  ensures res.None? ==> forall i | 0 <= i < |run| :: run[i] != needle
  {
    SeqIndexIterate(run, needle, 0)
  }

  function {:opaque} SeqOfLength<V(==)>(length: nat, v: V) : (res: seq<V>)
  ensures |res| == length
  ensures forall i: nat | i < |res| :: res[i] == v
  {
    if length == 0 then
      []
    else
      [v] + SeqOfLength(length - 1, v)
  }

  // This is a workaround since Dafny right now doesn't support
  // s[i := t] when i is a native type integer.
  function method {:opaque} SeqIndexUpdate<T>(s: seq<T>, i: uint64, t: T) : seq<T>
  requires i as int + 1 < 0x1_0000_0000_0000_0000
  requires 0 <= i as int < |s|
  ensures SeqIndexUpdate(s, i, t) == s[i as int := t]
  {
    s[..i] + [t] + s[i+1..]
  }
}
