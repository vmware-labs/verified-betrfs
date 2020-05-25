include "Option.s.dfy"
include "../Lang/NativeTypes.s.dfy"
include "mathematics.i.dfy"

module Sequences {
  import opened Options
  import opened NativeTypes
  import Math = Mathematics

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

  function FirstOpt<E>(run: seq<E>) : Option<E>
  {
    if |run| == 0 then None else Some(run[0])
  }

  function DropLast<E>(run: seq<E>) : seq<E>
    requires |run| > 0;
  {
    run[..|run|-1]
  }

  function Set<T>(run: seq<T>) : set<T> {
    set x : T | x in multiset(run)
  }

  lemma SetCardinality<T>(run: seq<T>)
    ensures |Set(run)| <= |run|
  {
    if |run| == 0 {
    } else {
      assert Set(run) == Set(DropLast(run)) + {Last(run)};
      SetCardinality(DropLast(run));
    }
  }
  
  lemma SetCardinality0<T>(run: seq<T>)
    ensures |Set(run)| == 0 <==> |run| == 0
  {
    if |run| != 0 {
      assert run[0] in Set(run);
    }
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

  lemma NoDupesSetCardinality<T>(a: seq<T>)
    requires NoDupes(a)
    ensures |Set(a)| == |a|
  {
    reveal_NoDupes();
    if |a| == 0 {
    } else {
      NoDupesSetCardinality(DropLast(a));
      assert Set(a) == Set(DropLast(a)) + {Last(a)};
    }
  }

  lemma NoDupesMultiset<T>(a: seq<T>)
    requires NoDupes(a)
    ensures forall x | x in multiset(a) :: multiset(a)[x] == 1
  {
    if |a| == 0 {
    } else {
      assert a == DropLast(a) + [ Last(a) ];
      assert Last(a) !in DropLast(a) by {
        reveal_NoDupes();
      }
      assert NoDupes(DropLast(a)) by {
        reveal_NoDupes();
      }
      NoDupesMultiset(DropLast(a));
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

  // TODO: can we replace Apply with this?
  function {:opaque} ApplyOpaque<E,R>(f: (E ~> R), run: seq<E>) : (result: seq<R>)
    requires forall i :: 0 <= i < |run| ==> f.requires(run[i])
    ensures |result| == |run|
    ensures forall i :: 0 <= i < |run| ==> result[i] == f(run[i]);
    reads set i, o | 0 <= i < |run| && o in f.reads(run[i]) :: o
  {
    Apply(f, run)
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

  function FoldFromRight<A,E>(f: (A, E) -> A, init: A, run: seq<E>) : A
  {
    if |run| == 0 then init
    else f(FoldFromRight(f, init, DropLast(run)), Last(run))
  }

  function {:opaque} remove<A>(s: seq<A>, pos: int) : seq<A>
  requires 0 <= pos < |s|
  ensures |remove(s, pos)| == |s| - 1
  ensures forall i | 0 <= i < pos :: remove(s, pos)[i] == s[i]
  ensures forall i | pos <= i < |s| - 1 :: remove(s, pos)[i] == s[i+1]
  {
    s[.. pos] + s[pos + 1 ..]
  }

  function {:opaque} RemoveOneValue<V>(s: seq<V>, v: V) : (s': seq<V>)
    ensures NoDupes(s) ==> NoDupes(s') && Set(s') == Set(s) - {v}
  {
    reveal_NoDupes();
    if v !in s then s else
    var i :| 0 <= i < |s| && s[i] == v;
    s[.. i] + s[i + 1 ..]
  }

//  function {:opaque} RemoveValue<V>(s: seq<V>, v: V) : seq<V>
//  // ensures forall i: nat | i < |RemoveValue(s, v)| :: RemoveValue(s, v)[i] != v
//  ensures Set(RemoveValue(s, v)) == Set(s) - {v}
//  {
//    if s == [] then s
//      else (if s[0] == v then [] else [s[0]]) + RemoveValue(s[1..], v)
//  }
//
//  lemma RemoveValueMultiset<V>(s: seq<V>, v: V) returns (res: seq<V>)
//  ensures Set(RemoveValue(s, v)) == Set(s) - {v}
//  {
//    reveal_RemoveValue();
//    if s == [] {
//      assert Set(RemoveValue(s, v)) == Set(s) - {v};
//    } else {
//      assert s == [s[0]] + s[1..];
//      var _ := RemoveValueMultiset(s[1..], v);
//      assert Set(s) == Set([s[0]]) + Set(s[1..]);
//      // TODO(andreal)
//      assume Set(RemoveValue(s, v)) == Set(s) - {v};
//    }
//  }

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

  function {:opaque} concatSeq<A>(a: seq<seq<A>>) : seq<A>
  {
    if |a| == 0 then [] else concatSeq(DropLast(a)) + Last(a)
  }

  lemma concatSeqAdditive<A>(a: seq<seq<A>>, b: seq<seq<A>>)
  ensures concatSeq(a + b) == concatSeq(a) + concatSeq(b)
  {
    if b == [] {
      calc {
        concatSeq(a + b);
        { assert a + b == a; }
        concatSeq(a);
        {
          reveal_concatSeq();
          assert concatSeq(b) == [];
        }
        concatSeq(a) + concatSeq(b);
      }
    } else {
      calc {
        concatSeq(a + b);
        { reveal_concatSeq(); }
        concatSeq(DropLast(a + b)) + Last(a + b);
        {
          assert DropLast(a + b) == a + DropLast(b);
          assert Last(a + b) == Last(b);
        }
        concatSeq(a + DropLast(b)) + Last(b);
        {
          concatSeqAdditive(a, DropLast(b));
        }
        concatSeq(a) + concatSeq(DropLast(b)) + Last(b);
        { reveal_concatSeq(); }
        concatSeq(a) + concatSeq(b);
      }
    }
  }

  lemma lemma_concatSeqLen_ge_elemLen<A>(a: seq<seq<A>>, i: int)
  requires 0 <= i < |a|
  ensures |concatSeq(a)| >= |a[i]|
  {
    reveal_concatSeq();
    if i < |a| - 1 {
      lemma_concatSeqLen_ge_elemLen(a[..|a|-1], i);
    }
  }

  lemma lemma_concatSeqLen_le_mul<A>(a: seq<seq<A>>, t: int)
  requires forall i | 0 <= i < |a| :: |a[i]| <= t
  ensures |concatSeq(a)| <= |a| * t
  {
    reveal_concatSeq();
    if |a| == 0 {
    } else {
      lemma_concatSeqLen_le_mul(a[..|a|-1], t);
    }
  }

  predicate {:opaque} IsPrefix<A(==)>(a: seq<A>, b: seq<A>)
  ensures IsPrefix(a, b) ==> |a| <= |b|
  {
    && |a| <= |b|
    && a == b[..|a|]
  }

  predicate {:opaque} IsSuffix<A(==)>(a: seq<A>, b: seq<A>) {
    && |a| <= |b|
    && a == b[|b|-|a|..]
  }

//~  lemma SelfIsPrefix<A>(a: seq<A>)
//~  ensures IsPrefix(a, a);
//~  {
//~    reveal_IsPrefix();
//~  }

//~  lemma IsPrefixFromEqSums<A>(a: seq<A>, b: seq<A>, c: seq<A>, d: seq<A>)
//~  requires a + b == c + d
//~  requires IsSuffix(b, d);
//~  ensures IsPrefix(c, a);
//~  {
//~    reveal_IsPrefix();
//~    reveal_IsSuffix();
//~    assert |c| <= |a|;
//~    assert c
//~        == (c + d)[..|c|]
//~        == (a + b)[..|c|]
//~        == a[..|c|];
//~  }

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

  lemma FlattenShapeAdditive<A>(seqs1: seq<seq<A>>, seqs2: seq<seq<A>>)
    ensures FlattenShape(seqs1 + seqs2) == FlattenShape(seqs1) + FlattenShape(seqs2)
  {
  }
  
  function {:opaque} FlattenLength(shape: seq<nat>) : nat
    ensures |shape| == 0 ==> FlattenLength(shape) == 0
  {
    if |shape| == 0 then 0
    else FlattenLength(DropLast(shape)) + Last(shape)
  }


  lemma FlattenLengthAdditive(shape1: seq<nat>, shape2: seq<nat>)
    ensures FlattenLength(shape1 + shape2) == FlattenLength(shape1) + FlattenLength(shape2)
  {
    if |shape2| == 0 {
      assert shape1 + shape2 == shape1;
    } else {
      reveal_FlattenLength();
      assert shape1 + shape2 == (shape1 + DropLast(shape2)) + [Last(shape2)];
    }
  }
  
  lemma FlattenLengthSubSeq(shape: seq<nat>, from: nat, to: nat)
    requires from <= to <= |shape|
    ensures FlattenLength(shape[from..to]) <= FlattenLength(shape)
  {
    assert shape == shape[..from] + shape[from..to] + shape[to..];
    FlattenLengthAdditive(shape[..from] + shape[from..to], shape[to..]);
    FlattenLengthAdditive(shape[..from], shape[from..to]);
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

  lemma FlattenSingleton<A>(s: seq<A>)
    ensures Flatten([ s ]) == s
  {
    reveal_Flatten();
  }
  
  lemma FlattenAdditive<A>(seqs1: seq<seq<A>>, seqs2: seq<seq<A>>)
    ensures Flatten(seqs1 + seqs2) == Flatten(seqs1) + Flatten(seqs2)
    decreases |seqs2|
  {
    if |seqs2| == 0 {
      assert seqs1 + seqs2 == seqs1;
    } else if |seqs2| == 1 {
      reveal_Flatten();
    } else {
      calc {
        Flatten(seqs1 + seqs2);
        { assert seqs1 + seqs2 == seqs1 + DropLast(seqs2) + [ Last(seqs2) ]; }
        Flatten(seqs1 + DropLast(seqs2) + [ Last(seqs2) ]);
        { FlattenAdditive(seqs1 + DropLast(seqs2), [ Last(seqs2) ]); }
        Flatten(seqs1 + DropLast(seqs2)) + Flatten([ Last(seqs2) ]);
        { FlattenAdditive(seqs1, DropLast(seqs2)); }
        Flatten(seqs1) + Flatten(DropLast(seqs2)) + Flatten([ Last(seqs2) ]);
        { FlattenAdditive(DropLast(seqs2), [ Last(seqs2) ]); }
        Flatten(seqs1) + Flatten(DropLast(seqs2) + [ Last(seqs2) ]);
        { assert seqs2 == DropLast(seqs2) + [ Last(seqs2) ]; }
        Flatten(seqs1) + Flatten(seqs2);
      }
    }
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
  
//~  lemma FlattenIndexOrdering(shape: seq<nat>, il: nat, io: nat, jl: nat, jo: nat)
//~    requires il < |shape|
//~    requires io < shape[il]
//~    requires jl < |shape|
//~    requires jo < shape[jl]
//~    requires il <= jl
//~    requires il == jl ==> io < jo
//~    ensures FlattenIndex(shape, il, io) < FlattenIndex(shape, jl, jo)
//~  {
//~    reveal_FlattenLength();
//~    if il < jl-1 {
//~      assert shape[..il] == shape[..il+1][..il];
//~      FlattenLengthSubSeq(shape[..jl], 0, il+1);
//~      assert shape[..jl][..il+1] == shape[..il+1];
//~    } else if il == jl - 1 {
//~      assert shape[..il] == shape[..il+1][..il];
//~    } else {
//~    }
//~  }

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

  function {:opaque} seqMax(s: seq<int>): int
    requires 0 < |s|
    ensures forall k :: k in s ==> seqMax(s) >= k
    ensures seqMax(s) in s
  {
    assert s == DropLast(s) + [Last(s)];
    if |s| == 1
    then s[0]
    else Math.max(seqMax(DropLast(s)), Last(s))
  }

  lemma SeqMaxCorrespondence(s1:seq<int>, s2:seq<int>, wit: seq<nat>)
    requires 0 < |s1|
    requires 0 < |s2|
    requires |wit| == |s2|
    requires forall j:nat :: j < |wit| ==> wit[j] < |s1|
    requires forall i :: 0 <= i < |s2| ==> s2[i] <= s1[wit[i]]
    ensures seqMax(s2) <= seqMax(s1)
  {
    if seqMax(s2) > seqMax(s1) {
      var idx :| 0 <= idx < |s2| && s2[idx] == seqMax(s2);
      assert s1[wit[idx]] in s1;  // trigger
      assert false;
    }
  }

  lemma SubseqMax(s: seq<int>, from: nat, to: nat)
    requires 0 <= from < to <= |s|
    ensures seqMax(s[from .. to]) <= seqMax(s)
  {
    var subseq := s[from .. to];
    SeqMaxCorrespondence(s, subseq, seq(|subseq|, i requires 0<=i<|subseq| => i + from));
  }

  lemma lemma_seq_suffix_slice<T>(s: seq<T>, i: int, j: int, k: int)
  requires 0 <= i <= |s|
  requires 0 <= j <= k <= |s| - i
  ensures s[i..][j..k] == s[i+j..i+k];
  {
  }

  lemma lemma_seq_slice_suffix<T>(s: seq<T>, i: int, j: int, k: int)
  requires 0 <= i <= j <= |s|
  requires 0 <= k <= j - i
  ensures s[i..j][k..] == s[i+k..j];
  {
  }

  lemma lemma_array_suffix_slice<T>(ar: array<T>, i: int, j: int, k: int)
  requires 0 <= i <= ar.Length
  requires 0 <= j <= k <= ar.Length - i
  ensures ar[i..][j..k] == ar[i+j..i+k];
  {
  }

  lemma lemma_seq_extensionality<T>(s: seq<T>, t: seq<T>)
  requires |s| == |t|
  requires forall i | 0 <= i < |s| :: s[i] == t[i]
  ensures s == t
  {
  }

  lemma lemma_seq_slice_slice<T>(s: seq<T>, i: int, j: int, k: int, l: int)
  requires 0 <= i <= j <= |s|
  requires 0 <= k <= l <= j - i
  ensures s[i..j][k..l] == s[i+k..i+l];
  {
    lemma_seq_extensionality(s[i..j][k..l], s[i+k..i+l]);
  }

  lemma lemma_array_slice_slice<T>(ar: array<T>, i: int, j: int, k: int, l: int)
  requires 0 <= i <= j <= ar.Length
  requires 0 <= k <= l <= j - i
  ensures ar[i..j][k..l] == ar[i+k..i+l];
  {
    lemma_seq_slice_slice(ar[..], i, j, k, l);
  }

  lemma lemma_seq_extensionality_slice<T>(s: seq<T>, t: seq<T>, a: int, b: int)
  requires 0 <= a <= b <= |s|
  requires b <= |t|
  requires forall i | a <= i < b :: s[i] == t[i]
  ensures s[a..b] == t[a..b]
  {
  }

  function {:opaque} fill<T>(n: int, t: T) : (res: seq<T>)
  requires n >= 0
  ensures |res| == n
  ensures forall i | 0 <= i < n :: res[i] == t
  {
    if n == 0 then [] else fill(n-1, t) + [t]
  }

  lemma sum_slice_second<T>(a: seq<T>, b: seq<T>, i: int, j: int)
  requires |a| <= i <= j <= |a| + |b|
  ensures (a+b)[i..j] == b[i-|a| .. j-|a|]
  {
  }
}
