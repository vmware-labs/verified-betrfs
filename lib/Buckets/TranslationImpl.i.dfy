include "BoundedPivotsLib.i.dfy"
include "TranslationLib.i.dfy"
include "BucketImpl.i.dfy"

include "../Base/KeyType.s.dfy"
include "../Lang/LinearSequence.i.dfy"
include "../Lang/LinearSequence.s.dfy"

//
// Provides definitions and libraries for edge table and 
// other translation related methods and lemma
//

module TranslationImpl {
  import opened NativeTypes
  import opened BoundedPivotsLib
  import opened Translations = TranslationLib
  import opened Sequences
  import opened Options
  import opened KeyType
  import opened BucketImpl
  import opened LinearSequence_i
  import opened LinearSequence_s

  method ComputeSplitLeftEdges(et: EdgeTable, pt: PivotTable, pt': PivotTable, pivot: Key, cLeft: uint64) returns (et': EdgeTable)
  requires WFPivots(pt)
  requires WFEdges(et, pt)
  requires ValidLeftCutOffKey(pt, pivot)
  requires |pt| < 0x4000_0000_0000_0000
  requires cLeft as int == CutoffForLeft(pt, pivot)
  requires pt' == SplitLeft(pt, pivot)
  ensures et' == SplitLeftEdges(et, pt, pivot)
  {
    if (pt[cLeft + 1].Element? && pt[ cLeft+1 ].e == pivot) || et[cLeft].None? {
      return et[..cLeft + 1];
    } else {
      var oldlcp : Key := ComputePivotLcp(pt[cLeft], pt[cLeft+1]);
      var newlcp : Key := ComputePivotLcp(pt'[cLeft], pt'[cLeft+1]);
      PivotLcpSubRangeLeft(pt[cLeft], pt[cLeft+1], pt'[cLeft+1]);
      
      assume |et[cLeft].value + newlcp[|oldlcp|..]| <= 1024;
      var translation : Key := et[cLeft].value + newlcp[|oldlcp|..];
      return et[..cLeft] +  [Some(translation)];
    }
  }

  method ComputeSplitRightEdges(et: EdgeTable, pt: PivotTable, pt': PivotTable, pivot: Key, cRight: uint64) returns (et': EdgeTable)
  requires WFPivots(pt)
  requires WFEdges(et, pt)
  requires BoundedKey(pt, pivot)
  requires |pt| < 0x4000_0000_0000_0000
  requires cRight as int == CutoffForRight(pt, pivot)
  requires pt' == SplitRight(pt, pivot)
  ensures et' == SplitRightEdges(et, pt, pivot)
  {
    if pt[cRight].e == pivot || et[cRight].None? {
      return et[cRight..];
    } else {
      var oldlcp : Key := ComputePivotLcp(pt[cRight], pt[cRight+1]);
      var newlcp : Key := ComputePivotLcp(pt'[0], pt'[1]);
      PivotLcpSubRangeRight(pt[cRight], pt'[0], pt'[1]);

      assume |et[cRight].value + newlcp[|oldlcp|..]| <= 1024;
      var translation : Key := et[cRight].value + newlcp[|oldlcp|..];
      return [Some(translation)] + et[cRight+1..];
    }
  }

  method Computelcpright(left: Key) returns (prefix: Key)
  ensures prefix == lcpright(left)
  {
    var i: uint64 := 0;
    var len := |left| as uint64;

    while i < len
      invariant 0 <= i <= len
      invariant forall j | 0 <= j < i :: left[j] as int == Uint8UpperBound() - 1 
    {
      if left[i] as int == Uint8UpperBound() - 1 {
        i := i + 1;
      } else {
        prefixIslcpright(left[..i]);
        assert left[..i] == lcpright(left[..i]);
        assert lcpright(left[i..]) == [];
        assert left[..i] + left[i..] == left;
        lcprightConcat(left[..i], left[i..]);
        return left[..i];
      }
    }
    prefixIslcpright(left);
    return left;
  }

  // TODO: Implement
  method Computelcp(left: Key, right: Key) returns (prefix: Key)
  ensures prefix == lcp(left, right)
  {
    assume false;
    prefix := [];
  }

  method ComputePivotLcp(left: Element, right: Element) returns (prefix: Key)
  requires ElementIsKey(left)
  requires right.Element? ==> ElementIsKey(right)
  ensures prefix == PivotLcp(left, right)
  {
    if right.Max_Element? {
      prefix := Computelcpright(left.e);
    } else {
      prefix := Computelcp(left.e, right.e);
    }
  }

  // TODO: Implement
  method ComputeTranslateKey(pt: PivotTable, et: EdgeTable, key: Key, r: uint64) returns (k: Key)
  requires WFPivots(pt)
  requires BoundedKey(pt, key)
  requires WFEdges(et, pt)
  requires r as int == Route(pt, key)
  ensures k == TranslateKey(pt, et, key)
  {
    assume false;
    k := [];
    // var r := Route(pt, key);
    // if et[r].None? then
    //   None
    // else
    //   var prefix := PivotLcp(pt[r], pt[r+1]);
    //   PrefixOfLcpIsPrefixOfKey(pt[r], pt[r+1], prefix, key);
    //   Some(PrefixSet(prefix, et[r].value))
  }

  // TODO: implement
  method ComputeApplyPrefixSet(pset: Option<PrefixSet>, key: Key) returns (k: Key)
  requires pset.Some? ==> IsPrefix(pset.value.prefix, key)
  ensures k == ApplyPrefixSet(pset, key)
  {
    assume false;
    k := key;
  }

  // TODO: implement
  method ComputeComposePrefixSet(a: Option<PrefixSet>, b: Option<PrefixSet>) returns (c: Option<PrefixSet>)
  requires a.Some? && b.Some? ==> 
    ( IsPrefix(a.value.newPrefix, b.value.prefix)
    || IsPrefix(b.value.prefix, a.value.newPrefix))
  ensures c == ComposePrefixSet(a, b)
  {
    assume false;
    c := None;
  }

  // TODO: implement
  method ComputeShortestUncommonPrefix(prefix: Key) returns (upper: Element)
  ensures upper == ShortestUncommonPrefix(prefix, |prefix|)
  {
    assume false;
    upper := Keyspace.Max_Element;
  }

  // TODO: implement
  method ComputeTranslateElement(e: Element, prefix: Key, newPrefix: Key) returns (e': Element)
  requires ElementIsKey(e)
  requires IsPrefix(prefix, e.e)
  ensures e' == TranslateElement(e, prefix, newPrefix)
  {
    assume false;
    e' := Keyspace.Element([]);
  }

  // TODO: impelement
  method ComputeTranslatePivotPair(left: Element, right: Element, prefix: Key, newPrefix: Key)
  returns (left': Element, right': Element)
  requires ElementIsKey(left)
  requires right.Element? ==> ElementIsKey(right)
  requires IsPrefix(prefix, left.e)
  requires Keyspace.lt(left, right)
  ensures var (l, r) := TranslatePivotPairInternal(left, right, prefix, newPrefix);
    && l == left'
    && r == right'
  {
    assume false;
    left' := Keyspace.Element([]);
    right' := Keyspace.Max_Element;
  }

  // TODO: implement
  method ComputeTranslatePivots(pt: PivotTable, prefix: Key, newPrefix: Key, end: Element) returns (pt': PivotTable)
  requires WFPivots(pt)
  requires forall i | 0 <= i < NumBuckets(pt) :: IsPrefix(prefix, pt[i].e)
  requires end.Element? ==> ElementIsKey(end)
  requires Keyspace.lt(TranslateElement(pt[|pt|-2], prefix, newPrefix), end)
  ensures pt' == TranslatePivots(pt, prefix, newPrefix, end, 0)
  {
    assume false;
    pt' := [];
  }

  // TODO: implement
  method ComputeTranslateEdges(et: EdgeTable, pt: PivotTable) returns (et': EdgeTable)
  requires WFPivots(pt)
  requires WFEdges(et, pt)
  ensures et' == TranslateEdges(et, pt, 0)
  {
    assume false;
    et' := [];
  }

  // TODO: implement
  method ComputeTranslateBucket(shared bucket: MutBucket, prefix: Key, newPrefix: Key) returns (linear bucket': MutBucket)
  requires bucket.Inv()
  ensures bucket'.Inv()
  ensures bucket'.I() == TranslateBucket(bucket.I(), prefix ,newPrefix)
  {
    assume false;
    bucket' := MutBucket.Alloc();
  }

  // TODO: implement
  method ComputeTranslateBuckets(shared blist: lseq<MutBucket>, prefix: Key, newPrefix: Key) returns (linear blist': lseq<MutBucket>)
  requires MutBucket.InvLseq(blist)
  ensures MutBucket.InvLseq(blist')
  ensures MutBucket.ILseq(blist') == TranslateBuckets(MutBucket.ILseq(blist), prefix, newPrefix)
  {
    blist' := lseq_alloc(0);
    assume false;
  }

  // TODO: Implement
  method ComputeParentKeysInChildRange(parentpivots: PivotTable, parentedges: EdgeTable, childpivots: PivotTable, slot: uint64)
  returns (b: bool)
  requires WFPivots(parentpivots)
  requires WFPivots(childpivots)
  requires WFEdges(parentedges, parentpivots)
  requires 0 <= slot as int < |parentedges|
  ensures b == ParentKeysInChildRange(parentpivots, parentedges, childpivots, slot as int)
  {
    assume false;
    b := true;
    // if parentedges[slot].None? {
    //   ComputeContainsRange();
    // }
    // Keyspace.reveal_IsStrictlySorted();
    // && (parentedges[slot].None? ==> 
    //     ContainsRange(childpivots, parentpivots[slot], parentpivots[slot+1]))
    // && (parentedges[slot].Some? ==> 
    //     && var (left, right) := TranslatePivotPair(parentpivots, parentedges, slot);
    //     && ContainsRange(childpivots, left, right))
  }
}
