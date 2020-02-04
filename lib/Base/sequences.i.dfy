include "Option.s.dfy"
include "NativeTypes.s.dfy"

module Sequences {
  import opened Options
  import opened NativeTypes

  lemma EqualExtensionality<E>(a: seq<E>, b: seq<E>)
    requires |a| == |b|
    requires forall i :: 0 <= i < |a| ==> a[i] == b[i]
    ensures a == b
  {
  }
  
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
    reads set i, o | 0 <= i < |run| && o in f.reads(run[i]) :: o
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

  lemma InsertMultiset<A>(s: seq<A>, a: A, pos: int)
    requires 0 <= pos <= |s|;
    ensures multiset(insert(s, a, pos)) == multiset(s) + multiset{a}
  {
    reveal_insert();
    assert s == s[..pos] + s[pos..];
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

  function {:opaque} Zip<A,B>(a: seq<A>, b: seq<B>) : seq<(A,B)>
    requires |a| == |b|
    ensures |Zip(a, b)| == |a|
    ensures forall i :: 0 <= i < |Zip(a, b)| ==> Zip(a, b)[i] == (a[i], b[i])
  {
    if |a| == 0 then []
    else Zip(DropLast(a), DropLast(b)) + [(Last(a), Last(b))]
  }

  function {:opaque} Unzip<A,B>(z: seq<(A, B)>) : (seq<A>, seq<B>)
    ensures |Unzip(z).0| == |Unzip(z).1| == |z|
    ensures forall i :: 0 <= i < |z| ==> (Unzip(z).0[i], Unzip(z).1[i]) == z[i]
  {
    if |z| == 0 then ([], [])
    else
      var (a, b) := Unzip(DropLast(z));
      (a + [Last(z).0], b + [Last(z).1])
  }

  lemma ZipOfUnzip<A,B>(s: seq<(A,B)>)
    ensures Zip(Unzip(s).0, Unzip(s).1) == s
  {
  }
  
  lemma UnzipOfZip<A,B>(sa: seq<A>, sb: seq<B>)
    requires |sa| == |sb|
    ensures Unzip(Zip(sa, sb)).0 == sa
    ensures Unzip(Zip(sa, sb)).1 == sb
  {
  }
  
  function {:opaque} FlattenShape<A>(seqs: seq<seq<A>>) : (shape: seq<nat>)
    ensures |shape| == |seqs|
    ensures forall i :: 0 <= i < |shape| ==> shape[i] == |seqs[i]|
  {
    if |seqs| == 0 then []
    else FlattenShape(DropLast(seqs)) + [|Last(seqs)|]
  }

  function {:opaque} FlattenLength(shape: seq<nat>) : nat
  {
    if |shape| == 0 then 0
    else FlattenLength(DropLast(shape)) + Last(shape)
  }
  
  lemma FlattenLengthMonotonic(shape: seq<nat>, prefix: nat)
    requires prefix < |shape|
    ensures FlattenLength(shape[..prefix]) <= FlattenLength(shape)
  {
    reveal_FlattenLength();
    if prefix == |shape|-1 {
    } else {
      FlattenLengthMonotonic(DropLast(shape), prefix);
      assert DropLast(shape)[..prefix] == shape[..prefix];
    }
  }

  function {:opaque} Flatten<A>(seqs: seq<seq<A>>) : seq<A>
    ensures |Flatten(seqs)| == FlattenLength(FlattenShape(seqs))
    ensures |seqs| == 0 ==> |Flatten(seqs)| == 0
  {
    reveal_FlattenShape();
    reveal_FlattenLength();
    if |seqs| == 0 then []
    else Flatten(DropLast(seqs)) + Last(seqs)
  }

  function FlattenIndex(shape: seq<nat>, i: nat, j: nat) : nat
    requires i < |shape|
    requires j < shape[i]
  {
    FlattenLength(shape[..i]) + j
  }

  function UnflattenIndex(shape: seq<nat>, i: nat) : (nat, nat)
    requires i < FlattenLength(shape)
  {
    reveal_FlattenLength();
    if i < FlattenLength(DropLast(shape)) then UnflattenIndex(DropLast(shape), i)
    else (|shape|-1, i - FlattenLength(DropLast(shape)))
  }

  lemma FlattenIndexInBounds(shape: seq<nat>, i: nat, j: nat)
    requires i < |shape|
    requires j < shape[i]
    ensures FlattenIndex(shape, i, j) < FlattenLength(shape)
  {
    reveal_FlattenLength();
    if i == |shape|-1 {
    } else {
      FlattenIndexInBounds(DropLast(shape), i, j);
      assert DropLast(shape)[..i] == shape[..i];
    }
  }
  
  lemma UnflattenIndexInBounds(shape: seq<nat>, i: nat)
    requires i < FlattenLength(shape)
    ensures UnflattenIndex(shape, i).0 < |shape|
    ensures UnflattenIndex(shape, i).1 < shape[UnflattenIndex(shape, i).0]
  {
    var shapeidx := UnflattenIndex(shape, i).0;
  }

  lemma FlattenUnflattenIdentity(shape: seq<nat>, i: nat)
    requires i < FlattenLength(shape)
    ensures UnflattenIndex(shape, i).0 < |shape|
    ensures UnflattenIndex(shape, i).1 < shape[UnflattenIndex(shape, i).0]
    ensures i == FlattenIndex(shape, UnflattenIndex(shape, i).0, UnflattenIndex(shape, i).1)
  {
    UnflattenIndexInBounds(shape, i);
    var (shapeidx, shapeoff) := UnflattenIndex(shape, i);
    if shapeidx == |shape|-1 {
    } else {
      FlattenUnflattenIdentity(DropLast(shape), i);
      assert DropLast(shape)[..shapeidx] == shape[..shapeidx];
    }
  }
  
  lemma UnflattenFlattenIdentity(shape: seq<nat>, i: nat, j: nat)
    requires i < |shape|
    requires j < shape[i]
    ensures FlattenIndex(shape, i, j) < FlattenLength(shape)
    ensures (i, j) == UnflattenIndex(shape, FlattenIndex(shape, i, j))
  {
    FlattenIndexInBounds(shape, i, j);
    if i == |shape| - 1 {
    } else {
      UnflattenFlattenIdentity(DropLast(shape), i, j);
      assert DropLast(shape)[..i] == shape[..i];
    }
  }
  
  lemma FlattenIndexOrdering(shape: seq<nat>, il: nat, io: nat, jl: nat, jo: nat)
    requires il < |shape|
    requires io < shape[il]
    requires jl < |shape|
    requires jo < shape[jl]
    requires il <= jl
    requires il == jl ==> io < jo
    ensures FlattenIndex(shape, il, io) < FlattenIndex(shape, jl, jo)
  {
    reveal_FlattenLength();
    if il < jl-1 {
      assert shape[..il] == shape[..il+1][..il];
      FlattenLengthMonotonic(shape[..jl], il+1);
      assert shape[..jl][..il+1] == shape[..il+1];
    } else if il == jl - 1 {
      assert shape[..il] == shape[..il+1][..il];
    } else {
    }
  }

  lemma UnflattenIndexOrdering(shape: seq<nat>, i: nat, j: nat)
    requires i < j < FlattenLength(shape)
    ensures UnflattenIndex(shape, i).0 <= UnflattenIndex(shape, j).0
    ensures UnflattenIndex(shape, i).0 == UnflattenIndex(shape, j).0 ==> UnflattenIndex(shape, i).1 < UnflattenIndex(shape, j).1
  {
    FlattenUnflattenIdentity(shape, i);
  }

  lemma FlattenIndexIsCorrect<A>(seqs: seq<seq<A>>, i: nat, j: nat)
    requires i < |seqs|
    requires j < |seqs[i]|
    ensures FlattenIndex(FlattenShape(seqs), i, j) < |Flatten(seqs)|
    ensures Flatten(seqs)[FlattenIndex(FlattenShape(seqs), i, j)] == seqs[i][j]
  {
    reveal_Flatten();
    FlattenIndexInBounds(FlattenShape(seqs), i, j);
    if i == |seqs|-1 {
    } else {
      FlattenIndexIsCorrect(DropLast(seqs), i, j);
      assert DropLast(FlattenShape(seqs))[..i] == FlattenShape(seqs)[..i];
    }
  }

  lemma UnflattenIndexIsCorrect<A>(seqs: seq<seq<A>>, i: nat)
    requires i < FlattenLength(FlattenShape(seqs))
    ensures UnflattenIndex(FlattenShape(seqs), i).0 < |seqs|
    ensures UnflattenIndex(FlattenShape(seqs), i).1 < |seqs[UnflattenIndex(FlattenShape(seqs), i).0]|
    ensures Flatten(seqs)[i] == seqs[UnflattenIndex(FlattenShape(seqs), i).0][UnflattenIndex(FlattenShape(seqs), i).1]
  {
    var shape := FlattenShape(seqs);
    UnflattenIndexInBounds(shape, i);
    reveal_Flatten();
  }

  lemma CardinalityOfSetsOfSequenceIndices<T>(q:seq<T>, t:set<int>)
    requires t == set i | 0 <= i < |q|
    ensures |t| == |q|
  {
    if |q|>0 {
      var sq := q[..|q|-1];
      var st := set i | 0 <= i < |sq|;
      calc {
        |q|;
        |sq| + 1;
          { CardinalityOfSetsOfSequenceIndices(sq, st); }
        |st| + 1;
          { assert t == st + {|sq|}; }
        |t|;
      }
    }
  }

}
