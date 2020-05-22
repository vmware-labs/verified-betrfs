include "../Base/NativeArrays.s.dfy"
include "../Lang/NativeTypes.s.dfy"

module Collections__Seqs_i {
import opened NativeTypes
import NativeArrays

function last<T>(s:seq<T>):T
    requires |s| > 0;
{
    s[|s|-1]
}

function all_but_last<T>(s:seq<T>):seq<T>
    requires |s| > 0;
    ensures  |all_but_last(s)| == |s| - 1;
{
    s[..|s|-1]
}


lemma SeqAdditionIsAssociative<T>(a:seq<T>, b:seq<T>, c:seq<T>)
    ensures a+(b+c) == (a+b)+c;
{
}

predicate ItemAtPositionInSeq<T>(s:seq<T>, v:T, idx:int)
{
    0 <= idx < |s| && s[idx] == v
}

lemma Lemma_ItemInSeqAtASomePosition<T>(s:seq<T>, v:T)
    requires v in s;
    ensures  exists idx :: ItemAtPositionInSeq(s, v, idx);
{
    var idx :| 0 <= idx < |s| && s[idx] == v;
    assert ItemAtPositionInSeq(s, v, idx);
}

function FindIndexInSeq<T>(s:seq<T>, v:T):int
    ensures var idx := FindIndexInSeq(s, v);
            if idx >= 0 then
                idx < |s| && s[idx] == v
            else
                v !in s;
{
    if v in s then
        Lemma_ItemInSeqAtASomePosition(s, v);
        var idx :| ItemAtPositionInSeq(s, v, idx);
        idx
    else
        -1
}

//~ lemma Lemma_IdenticalSingletonSequencesHaveIdenticalElement<T>(x:T, y:T)
//~     requires [x] == [y];
//~     ensures  x == y;
//~ {
//~     calc {
//~         x;
//~         [x][0];
//~         [y][0];
//~         y;
//~     }
//~ }

//////////////////////////////////////////////////////////
//  Combining sequences of sequences
//////////////////////////////////////////////////////////
function SeqCat<T>(seqs:seq<seq<T>>) : seq<T>
{
    if |seqs| == 0 then []
    else seqs[0] + SeqCat(seqs[1..])
}

function SeqCatRev<T>(seqs:seq<seq<T>>) : seq<T>
{
    if |seqs| == 0 then []
    else SeqCatRev(all_but_last(seqs)) + last(seqs)
}

lemma lemma_SeqCat_adds<T>(A:seq<seq<T>>, B:seq<seq<T>>)
    ensures SeqCat(A + B) == SeqCat(A) + SeqCat(B);
{
    if |A| == 0 {
      assert A + B == B;
    } else {
        calc {
            SeqCat(A + B);
                { assert (A + B)[0] == A[0];  assert (A + B)[1..] == A[1..] + B; }
            A[0] + SeqCat(A[1..] + B);
            A[0] + SeqCat(A[1..]) + SeqCat(B);
            SeqCat(A) + SeqCat(B);
        }
    }
}

lemma lemma_SeqCatRev_adds<T>(A:seq<seq<T>>, B:seq<seq<T>>)
    ensures SeqCatRev(A + B) == SeqCatRev(A) + SeqCatRev(B);
{
    if |B| == 0 {
        assert SeqCatRev(B) == [];
        assert A+B == A;
    } else {
        calc {
            SeqCatRev(A + B);
                { assert last(A + B) == last(B);  assert all_but_last(A + B) == A + all_but_last(B); }
            SeqCatRev(A + all_but_last(B)) + last(B);
            SeqCatRev(A) + SeqCatRev(all_but_last(B)) + last(B);
                { assert SeqCatRev(all_but_last(B)) + last(B) == SeqCatRev(B); }
            SeqCatRev(A) + SeqCatRev(B);
        }
    }
}

lemma lemma_SeqCat_equivalent<T>(seqs:seq<seq<T>>)
    ensures SeqCat(seqs) == SeqCatRev(seqs);
{
    if |seqs| == 0 {
    } else {
        calc {
            SeqCatRev(seqs);
            SeqCatRev(all_but_last(seqs)) + last(seqs);
                { lemma_SeqCat_equivalent(all_but_last(seqs)); }
            SeqCat(all_but_last(seqs)) + last(seqs);
            SeqCat(all_but_last(seqs)) + SeqCat([last(seqs)]);
                { lemma_SeqCat_adds(all_but_last(seqs), [last(seqs)]); 
                  assert seqs == all_but_last(seqs) + [last(seqs)]; }
            SeqCat(seqs);
        }

    }
}

/*
function LenSum<T>(a:seq<seq<T>>) : int
{
  |SeqCatRev(a)|
}

lemma LenSumPrefixLe<T>(a:seq<seq<T>>, i: int)
requires 0 <= i <= |a|
ensures LenSum(a[..i]) <= LenSum(a)

method ComputeSeqCat<T>(a:seq<seq<T>>, defaultValue: T) returns (c: seq<T>)
requires |a| < 0x1_0000_0000_0000_0000
requires LenSum(a) < 0x1_0000_0000_0000_0000
ensures c == SeqCatRev(a)
{
  var len: uint64 := 0;
  var i: uint64 := 0;
  while i < |a| as uint64
  invariant 0 <= i as int <= |a|
  invariant len as int == LenSum(a[..i])
  {
    LenSumPrefixLe(a, i as int + 1);
    assert a[..i+1][..i] == a[..i];
    assert len as int + |a[i]|
        == LenSum(a[..i]) + |a[i]|
        == |SeqCatRev(a[..i])| + |a[i]|
        == |SeqCatRev(a[..i]) + a[i]|
        == |SeqCatRev(a[..i+1])|
        == LenSum(a[..i+1]);
    assert len as int + |a[i]| <= LenSum(a);

    len := len + |a[i]| as uint64;
    i := i + 1;
  }

  assert a == a[..i];
  assert len as int == LenSum(a);
  var ar := new T[len]((i) => defaultValue);

  var j: uint64 := 0;
  var pos: uint64 := 0;
  while j < |a| as uint64
  invariant 0 <= j as int <= |a|
  invariant pos as int == LenSum(a[..j])
  invariant 0 <= LenSum(a[..j]) <= ar.Length
  invariant ar[..LenSum(a[..j])] == SeqCatRev(a[..j])
  {
    LenSumPrefixLe(a, j as int + 1);
    assert a[..j+1][..j] == a[..j];
    assert pos as int + |a[j]|
        == LenSum(a[..j]) + |a[j]|
        == |SeqCatRev(a[..j])| + |a[j]|
        == |SeqCatRev(a[..j]) + a[j]|
        == |SeqCatRev(a[..j+1])|
        == LenSum(a[..j+1]);

    assert pos as int + |a[j]| <= ar.Length;
    NativeArrays.CopySeqIntoArray(a[j], 0, ar, pos, |a[j]| as uint64);

    assert pos as int + |a[j]|
        == LenSum(a[..j]) + |a[j]|
        == LenSum(a[..j+1]);

    assert ar[..LenSum(a[..j+1])]
        == SeqCatRev(a[..j+1]);

    pos := pos + |a[j]| as uint64;
    j := j + 1;
  }

  return ar[..];
}
*/

}
