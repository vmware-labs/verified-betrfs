include "BoundedPivotsLib.i.dfy"
include "BucketsLib.i.dfy"
include "MapSeqs.i.dfy"

include "../Base/KeyType.s.dfy"
include "../Lang/System/SeqComparison.s.dfy"

//
// Provides definitions and libraries for edge table and 
// other translation related methods and lemma
//

module TranslationLib {
  import opened NativeTypes
  import opened BoundedPivotsLib
  import opened BucketsLib
  import opened MapSeqs
  import opened Sequences
  import opened Options
  import opened KeyType

  import SeqComparison

  type EdgeTable = seq<Option<Key>>

  predicate NonEmptyLcp(pt: PivotTable, i: int)
  requires WFPivots(pt)
  requires 0 <= i < NumBuckets(pt)
  {
    Keyspace.reveal_IsStrictlySorted();
    PivotLcp(pt[i], pt[i+1]) != []
  }

  predicate WFEdges(et: EdgeTable, pt: PivotTable)
  requires WFPivots(pt)
  {
    && |et| == NumBuckets(pt)
    && (forall i | 0 <= i < |et| && et[i].Some? :: NonEmptyLcp(pt, i))
  }

  predicate TranslationPreserved(pt: PivotTable, et: EdgeTable, pt': PivotTable, et': EdgeTable)
  requires WFPivots(pt)
  requires WFPivots(pt')
  requires WFEdges(et, pt)
  requires WFEdges(et', pt')
  {
    && (forall key | BoundedKey(pt', key) :: 
        && BoundedKey(pt, key)
        && TranslateKey(pt', et', key) == TranslateKey(pt, et, key))
  }

  function SplitLeftEdges(et: EdgeTable, pt: PivotTable, pivot: Key) : (et': EdgeTable)
  requires WFPivots(pt)
  requires WFEdges(et, pt)
  requires ValidLeftCutOffKey(pt, pivot)
  ensures WFEdges(et', SplitLeft(pt, pivot))
  ensures TranslationPreserved(pt, et, SplitLeft(pt, pivot), et')
  {
    var cLeft := CutoffForLeft(pt, pivot);
    if (pt[cLeft + 1].Element? && pt[ cLeft+1 ].e == pivot) || et[cLeft].None? then (
      et[..cLeft + 1]
    ) else (
      var pt' := SplitLeft(pt, pivot);

      var oldlcp : Key := PivotLcp(pt[cLeft], pt[cLeft+1]);
      var newlcp : Key := PivotLcp(pt'[cLeft], pt'[cLeft+1]);
      PivotLcpSubRangeLeft(pt[cLeft], pt[cLeft+1], pt'[cLeft+1]);
  
      assume |et[cLeft].value + newlcp[|oldlcp|..]| <= 1024;
      var translation : Key := et[cLeft].value + newlcp[|oldlcp|..];
      et[..cLeft] +  [Some(translation)]
    )
  }

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

  function SplitRightEdges(et: EdgeTable, pt: PivotTable, pivot: Key) : (et': EdgeTable)
  requires WFPivots(pt)
  requires WFEdges(et, pt)
  requires BoundedKey(pt, pivot)
  ensures WFEdges(et', SplitRight(pt, pivot))
  ensures TranslationPreserved(pt, et, SplitRight(pt, pivot), et')
  {
    var cRight := CutoffForRight(pt, pivot);
    if pt[cRight].e == pivot || et[cRight].None? then (
      et[cRight..]
    ) else (
      var pt' := SplitRight(pt, pivot);

      var oldlcp : Key := PivotLcp(pt[cRight], pt[cRight+1]);
      var newlcp : Key := PivotLcp(pt'[0], pt'[1]);
      PivotLcpSubRangeRight(pt[cRight], pt'[0], pt'[1]);

      assume |et[cRight].value + newlcp[|oldlcp|..]| <= 1024;
      var translation : Key := et[cRight].value + newlcp[|oldlcp|..];
      [Some(translation)] + et[cRight+1..]
    )
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

  lemma WFConcatEdges(leftpt: PivotTable, leftet: EdgeTable, rightpt: PivotTable, rightet: EdgeTable, pt: PivotTable)
  requires WFPivots(leftpt)
  requires WFPivots(rightpt)
  requires WFPivots(pt)
  requires WFEdges(leftet, leftpt)
  requires WFEdges(rightet, rightpt)
  requires Last(leftpt) == rightpt[0]
  requires pt == concat3(leftpt[..|leftpt|-1], Last(leftpt), rightpt[1..])
  ensures WFEdges(concat(leftet, rightet), pt)
  ensures TranslationPreserved(pt, concat(leftet, rightet), leftpt, leftet)
  ensures TranslationPreserved(pt, concat(leftet, rightet), rightpt, rightet)
  {
    var et := concat(leftet, rightet);
    assert |et| == NumBuckets(pt);

    forall i | 0 <= i < |et|
    ensures et[i].Some? ==> PivotLcp(pt[i], pt[i+1]) != []
    {
      if i < |leftet| {
        assert pt[i] == leftpt[i];
        assert pt[i+1] == leftpt[i+1];
        assert et[i] == leftet[i];
      } else {
        assert pt[i] == rightpt[i-|leftet|];
        assert pt[i+1] == rightpt[i-|leftet|+1];
        assert et[i] == rightet[i-|leftet|];
      }
    }
    Keyspace.reveal_IsStrictlySorted();
  }

  // lcp functions and methods

  function lcpright(left: Key): (prefix: Key)
  ensures IsPrefix(prefix, left)
  ensures SeqComparison.lte(prefix, left)
  {
    reveal_IsPrefix();
    SeqComparison.reveal_lte();

    if |left| > 0 && left[0] as int == Uint8UpperBound() - 1 then
      [left[0]] + lcpright(left[1..])
    else
      []
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

  function lcp(left: Key, right: Key): (prefix: Key)
  ensures IsPrefix(prefix, left)
  ensures SeqComparison.lte(prefix, left)
  {
    reveal_IsPrefix();
    SeqComparison.reveal_lte();

    if |left| > 0 && |right| > 0 && left[0] == right[0] then (
      [left[0]] + lcp(left[1..], right[1..])
    ) else if |left| > 0 && |right| == 1 && (left[0] as int + 1) == right[0] as int then (
      [left[0]] + lcpright(left[1..])
    ) else (
      []
    )
  }

  method Computelcp(left: Key, right: Key) returns (prefix: Key)
  ensures prefix == lcp(left, right)
  {
    assume false;
    prefix := [];
  }

  function PivotLcp(left: Element, right: Element) : (prefix: Key)
  requires ElementIsKey(left)
  requires right.Element? ==> ElementIsKey(right)
  {
    if right.Max_Element? then (
      lcpright(left.e)
    ) else (
      lcp(left.e, right.e)
    )
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

  lemma lcprightCorrect(left: Key, prefix: Key, key: Key)
  requires lcpright(left) == prefix
  requires SeqComparison.lte(left, key)
  ensures IsPrefix(prefix, key)
  {
    reveal_IsPrefix();
    SeqComparison.reveal_lte();

    if |left| > 0 && left[0] as int == Uint8UpperBound() - 1 {
      lcprightCorrect(left[1..], prefix[1..], key[1..]);
    }
  }

  lemma lcprightConcat(key1: Key, key2: Key)
  requires |key1 + key2| <= 1024
  ensures lcpright(key1 + key2) == lcpright(key1) + lcpright(key2)
  {
    reveal_IsPrefix();
    SeqComparison.reveal_lte();
    assume false;
  }

  lemma lcprightSubRangeRight(left: Key, left': Key, prefix: Key, prefix': Key)
  requires lcpright(left) == prefix
  requires lcpright(left') == prefix'
  requires SeqComparison.lte(left, left')
  ensures IsPrefix(prefix, prefix')
  {
    reveal_IsPrefix();
    SeqComparison.reveal_lte();

    if |left| > 0 && left[0] as int == Uint8UpperBound() - 1 {
      lcprightSubRangeRight(left[1..], left'[1..], prefix[1..], prefix'[1..]);
    }
  }

  lemma lcprightSubRangeLeft(left: Key, right: Key, prefix: Key, prefix': Key)
  requires lcpright(left) == prefix
  requires lcp(left, right) == prefix'
  requires SeqComparison.lt(left, right)
  ensures IsPrefix(prefix, prefix')
  {
    reveal_IsPrefix();
    SeqComparison.reveal_lte();

    if |left| > 0 && left[0] as int == Uint8UpperBound() - 1 {
      lcprightSubRangeLeft(left[1..], right[1..], prefix[1..], prefix'[1..]);
    }
  }

  lemma lcpCorrect(left: Key, right: Key, prefix: Key, key: Key)
  requires lcp(left, right) == prefix
  requires SeqComparison.lte(left, key)
  requires SeqComparison.lt(key, right)
  ensures IsPrefix(prefix, key)
  {
    reveal_IsPrefix();
    SeqComparison.reveal_lte();

    if |left| > 0 && |right| > 0 && left[0] == right[0] {
      lcpCorrect(left[1..], right[1..], prefix[1..], key[1..]);
    } else if |left| > 0 && |right| == 1 && (left[0] as int + 1) == right[0] as int {
      if key[0] == right[0] {
        assert SeqComparison.lt(key[1..], right[1..]);
        assert false;
      }
      lcprightCorrect(left[1..], lcpright(left[1..]), key[1..]);
    }
  }

  lemma lcpSubRangeRight(left: Key, left': Key, right: Key, prefix: Key, prefix': Key)
  requires lcp(left, right) == prefix
  requires lcp(left', right) == prefix'
  requires SeqComparison.lte(left, left')
  requires SeqComparison.lt(left', right)
  ensures IsPrefix(prefix, prefix')
  {
    reveal_IsPrefix();
    SeqComparison.reveal_lte();

    if |left| > 0 && |right| > 0 && left[0] == right[0] {
      lcpSubRangeRight(left[1..], left'[1..], right[1..], prefix[1..], prefix'[1..]);
    } else if |left| > 0 && |right| == 1 && (left[0] as int + 1) == right[0] as int {
      if left'[0] == right[0] {
        assert SeqComparison.lt(left'[1..], right[1..]);
        assert false;
      }
      lcprightSubRangeRight(left[1..], left'[1..], prefix[1..], prefix'[1..]);
    }
  }

  lemma lcpSubRangeLeft(left: Key, right: Key, right': Key, prefix: Key, prefix': Key)
  requires lcp(left, right) == prefix
  requires lcp(left, right') == prefix'
  requires SeqComparison.lt(right', right)
  requires SeqComparison.lt(left, right')
  ensures IsPrefix(prefix, prefix')
  {
    reveal_IsPrefix();
    SeqComparison.reveal_lte();

    if |left| > 0 && |right| > 0 && left[0] == right[0] {
      lcpSubRangeLeft(left[1..], right[1..], right'[1..], prefix[1..], prefix'[1..]);
    } else if |left| > 0 && |right| == 1 && (left[0] as int + 1) == right[0] as int {
      if right'[0] == right[0] {
        assert SeqComparison.lt(right'[1..], right[1..]);
        assert false;
      }
      lcprightSubRangeLeft(left[1..], right'[1..], prefix[1..], prefix'[1..]);
    }
  }

  lemma PivotLcpSubRangeRight(left: Element, left': Element, right: Element)
  requires ElementIsKey(left)
  requires ElementIsKey(left')
  requires Keyspace.lte(left, left')
  requires Keyspace.lt(left', right)
  requires right.Element? ==> ElementIsKey(right)
  ensures IsPrefix(PivotLcp(left, right), PivotLcp(left', right))
  {
    var oldprefix := PivotLcp(left, right);
    var newprefix := PivotLcp(left', right);

    if right.Max_Element? {
      lcprightSubRangeRight(left.e, left'.e, oldprefix, newprefix);
    } else {
      lcpSubRangeRight(left.e, left'.e, right.e, oldprefix, newprefix);
    }
  }

  lemma PivotLcpSubRangeLeft(left: Element, right: Element, right': Element)
  requires ElementIsKey(left)
  requires ElementIsKey(right')
  requires Keyspace.lt(left, right')
  requires Keyspace.lt(right', right)
  requires right.Element? ==> ElementIsKey(right)
  ensures IsPrefix(PivotLcp(left, right), PivotLcp(left, right'))
  {
    var oldprefix := PivotLcp(left, right);
    var newprefix := PivotLcp(left, right');

    if right.Max_Element? {
      lcprightSubRangeLeft(left.e, right'.e, oldprefix, newprefix);
    } else {
      lcpSubRangeLeft(left.e, right.e, right'.e, oldprefix, newprefix);
    }
  }

  lemma PrefixOfLcpIsPrefixOfKey(left: Element, right: Element, prefix: Key, key: Key)
  requires ElementIsKey(left)
  requires right.Element? ==> ElementIsKey(right)
  requires Keyspace.lt(left, right)
  requires InBetween(left, right, key)
  requires IsPrefix(prefix, PivotLcp(left, right))
  ensures IsPrefix(prefix, key)
  {
    reveal_IsPrefix();
    SeqComparison.reveal_lte();

    var lcp := PivotLcp(left, right);
    if right.Max_Element? {
      Keyspace.Base_Order.transitivity(lcp, left.e, key);
      lcprightCorrect(left.e, lcp, key);
    } else {
      lcpCorrect(left.e, right.e, lcp, key);
    }
  }

  lemma PrefixOfLcpIsPrefixOfKeys(left: Element, right: Element, prefix: Key)
  requires ElementIsKey(left)
  requires right.Element? ==> ElementIsKey(right)
  requires Keyspace.lt(left, right)
  requires IsPrefix(prefix, PivotLcp(left, right))
  ensures AllKeysInBetweenHasPrefix(left, right, prefix)
  {
    forall key : Key | InBetween(left, right, key)
    ensures IsPrefix(prefix, key)
    {
      PrefixOfLcpIsPrefixOfKey(left, right, prefix, key);
    }
  }

  predicate AllKeysInBetweenHasPrefix(left: Element, right: Element, prefix: Key)
  requires ElementIsKey(left)
  requires right.Element? ==> ElementIsKey(right)
  requires Keyspace.lt(left, right)
  {
    && (forall key : Key | InBetween(left, right, key) :: IsPrefix(prefix, key))
  }

  // used by succ query
  datatype PrefixSet = PrefixSet(prefix: Key, newPrefix: Key)
  type TranslationTable = seq<Option<PrefixSet>>

  function Translate(pt: PivotTable, et: EdgeTable, key: Key): (pset: Option<PrefixSet>)
  requires WFPivots(pt)
  requires BoundedKey(pt, key)
  requires WFEdges(et, pt)
  ensures pset.Some? ==> IsPrefix(pset.value.prefix, key)
  {
    var r := Route(pt, key);
    if et[r].None? then
      None
    else
      var prefix := PivotLcp(pt[r], pt[r+1]);
      PrefixOfLcpIsPrefixOfKey(pt[r], pt[r+1], prefix, key);
      Some(PrefixSet(prefix, et[r].value))
  }

  function TranslateKey(pt: PivotTable, et: EdgeTable, key: Key): Key
  requires WFPivots(pt)
  requires BoundedKey(pt, key)
  requires WFEdges(et, pt)
  {
    var pset := Translate(pt, et, key);
    ApplyPrefixSet(pset, key)
  }

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

  function ApplyPrefixSet(pset: Option<PrefixSet>, key: Key) : Key
  requires pset.Some? ==> IsPrefix(pset.value.prefix, key)
  {
    if pset.None? then key 
    else (
      assume |pset.value.newPrefix + key[|pset.value.prefix|..]| <= 1024;
      pset.value.newPrefix + key[|pset.value.prefix|..]
    )
  }

  function ComposePrefixSet(a: Option<PrefixSet>, b: Option<PrefixSet>): (c: Option<PrefixSet>)
  requires a.Some? && b.Some? ==> 
    ( IsPrefix(a.value.newPrefix, b.value.prefix)
    || IsPrefix(b.value.prefix, a.value.newPrefix))
  {
    if a == None then (
      b
    ) else if b == None then (
      a
    ) else (
      reveal_IsPrefix();
      if |a.value.newPrefix| <= |b.value.prefix| then (
        var prefix := ApplyPrefixSet(Some(PrefixSet(a.value.newPrefix, a.value.prefix)), b.value.prefix);  
        Some(PrefixSet(prefix, b.value.newPrefix))
      ) else (
        var newPrefix := ApplyPrefixSet(b, a.value.newPrefix);
        Some(PrefixSet(a.value.prefix, newPrefix))
      )
    )
  }

  lemma ComposePrefixSetCorrect(a: Option<PrefixSet>, b: Option<PrefixSet>, c: Option<PrefixSet>, 
    key: Key, akey: Key, ckey: Key)
  requires a.Some? ==> IsPrefix(a.value.prefix, key)
  requires c.Some? ==> IsPrefix(c.value.prefix, key)
  requires akey == ApplyPrefixSet(a, key)
  requires ckey == ApplyPrefixSet(c, key)
  requires c.None? ==> ckey == key
  requires b.Some? ==> IsPrefix(b.value.prefix, akey)
  requires a.Some? && b.Some? ==> 
    ( IsPrefix(a.value.newPrefix, b.value.prefix)
    || IsPrefix(b.value.prefix, a.value.newPrefix))
  requires c == ComposePrefixSet(a, b)
  ensures ApplyPrefixSet(b, akey) == ckey
  {
  }

  // given a prefix find its upperbound s.t. lcp(prefix, upper) == prefix
  function {:opaque} ShortestUncommonPrefix(prefix: Key, idx: int): (upper: Element)
  requires 0 <= idx <= |prefix|
  requires forall i | idx < i < |prefix| :: prefix[i] as int == (Uint8UpperBound() - 1)
  ensures upper.Element? ==> (
    && ElementIsKey(upper)
    && lcp(prefix, upper.e) == prefix
    && SeqComparison.lt(prefix, upper.e)
    && (|upper.e| <= |prefix|)
    && (upper.e[..|upper.e|-1] == prefix[..|upper.e|-1])
    && (upper.e[|upper.e|-1] as int == prefix[|upper.e|-1] as int + 1)
  )
  ensures PivotLcp(KeyToElement(prefix), upper) == prefix
  decreases idx
  {
    reveal_IsPrefix();
    SeqComparison.reveal_lte();

    if idx < |prefix| && prefix[idx] as int < Uint8UpperBound() - 1
    then (
      var k : Key := prefix[..idx] + [prefix[idx] + 1];
      PrefixLteProperties(prefix[..idx], prefix, k);
      prefixIslcp(prefix, k);
      KeyToElement(k)
    ) else (
      if idx == 0 then (
        prefixIslcpright(prefix);
        Keyspace.Max_Element
      ) else (
        ShortestUncommonPrefix(prefix, idx - 1)
      )
    )
  }

  lemma prefixIslcpright(prefix: Key)
  requires forall i | 0 <= i < |prefix| :: prefix[i] as int == (Uint8UpperBound() - 1)
  ensures lcpright(prefix) == prefix
  {
  }

  lemma prefixIslcp(prefix: Key, upper: Key)
  requires 0 < |upper| <= |prefix|
  requires IsPrefix(prefix[..|upper|-1], upper)
  requires upper[|upper|-1] as int == (prefix[|upper|-1] as int + 1)
  requires forall i | |upper| <= i < |prefix| :: prefix[i] as int == (Uint8UpperBound() - 1)
  ensures lcp(prefix, upper) == prefix
  {
    reveal_IsPrefix();

    if |upper| == 1 {
      prefixIslcpright(prefix[1..]);
    } else {
      prefixIslcp(prefix[1..], upper[1..]);
    }
  }

  lemma PrefixLteProperties(prefix: Key, left: Key, right: Key)
  requires IsPrefix(prefix, left)
  requires IsPrefix(prefix, right)
  ensures SeqComparison.lte(left, right) ==> 
    ( && SeqComparison.lte(left[|prefix|..], right[|prefix|..])
      && IsPrefix(prefix, lcp(left, right)))
  ensures SeqComparison.lte(left[|prefix|..], right[|prefix|..]) ==>
    ( && SeqComparison.lte(left, right))
  {
    reveal_IsPrefix();
    SeqComparison.reveal_lte();

    if |prefix| > 0 {
      PrefixLteProperties(prefix[1..], left[1..], right[1..]);
    }
  }

  function TranslateElement(e: Element, prefix: Key, newPrefix: Key): (e': Element)
  requires ElementIsKey(e)
  requires IsPrefix(prefix, e.e)
  ensures ElementIsKey(e')
  ensures IsPrefix(newPrefix, e'.e)
  {
    reveal_IsPrefix();
    var key : Key := e.e;
    assume |newPrefix + key[|prefix|..]| <= 1024;
    var translatedKey : Key := newPrefix + key[|prefix|..];
    KeyToElement(translatedKey)
  }

  function TranslatePivotPair(pt: PivotTable, et: EdgeTable, slot: int) : (p: (Element, Element))
  requires WFPivots(pt)
  requires WFEdges(et, pt)
  requires 0 <= slot < NumBuckets(pt)
  requires et[slot].Some?
  {
    Keyspace.reveal_IsStrictlySorted();

    var prefix := PivotLcp(pt[slot], pt[slot+1]);
    var newPrefix := et[slot].value;

    TranslatePivotPairInternal(pt[slot], pt[slot+1], prefix, newPrefix)
  }

  function TranslatePivotPairInternal(left: Element, right: Element, prefix: Key, newPrefix: Key) : (p: (Element, Element))
  requires ElementIsKey(left)
  requires right.Element? ==> ElementIsKey(right)
  requires IsPrefix(prefix, left.e)
  requires Keyspace.lt(left, right)
  ensures var (left', right') := p;
        && Keyspace.lt(left', right')
        && ElementIsKey(left')
        && (right'.Element? ==> ElementIsKey(right'))
        && AllKeysInBetweenHasPrefix(left', right', newPrefix)
  {
    var left' := TranslateElement(left, prefix, newPrefix);

    if right.Max_Element? || !IsPrefix(prefix, right.e)
    then (
      var right' := ShortestUncommonPrefix(newPrefix, |newPrefix|);

      PrefixOfLcpIsPrefixOfKeys(KeyToElement(newPrefix), right', newPrefix);
      assert Keyspace.lte(KeyToElement(newPrefix), left') by {
        SeqComparison.reveal_lte();
        PrefixLteProperties(newPrefix, newPrefix, left'.e);
      }

      if right'.Max_Element? then (
        assert Keyspace.lt(left', right');
        (left', right')
      ) else (
        KeyWithPrefixLt(newPrefix, right'.e, left'.e);
        (left', right')
      )
    ) else (
      var right' := TranslateElement(right, prefix, newPrefix);

      PrefixLteProperties(prefix, left.e, right.e);
      PrefixLteProperties(newPrefix, left'.e, right'.e);
      PrefixOfLcpIsPrefixOfKeys(left', right', newPrefix);

      (left', right')
    )
  }

  lemma KeyWithPrefixLt(prefix: Key, right: Key, key: Key)
  requires SeqComparison.lt(prefix, right)
  requires IsPrefix(prefix, key)
  requires !IsPrefix(prefix, right)
  ensures SeqComparison.lt(key, right)
  {
    reveal_IsPrefix();
    SeqComparison.reveal_lte();

    if |right| > 0 && right[0] == prefix[0] {
      KeyWithPrefixLt(prefix[1..], right[1..], key[1..]);
    }
  }

  lemma TranslatePivotPairRangeProperty(left: Element, right: Element, prefix: Key, newPrefix: Key)
  requires ElementIsKey(left)
  requires right.Element? ==> ElementIsKey(right)
  requires IsPrefix(prefix, left.e)
  requires Keyspace.lt(left, right)
  ensures var (left', right') := TranslatePivotPairInternal(left, right, prefix, newPrefix);
      && (forall k : Key | InBetween(left', right', k) ::
          && Keyspace.lte(left, Keyspace.Element(prefix + k[|newPrefix|..]))
          && Keyspace.lt(Keyspace.Element(prefix + k[|newPrefix|..]), right))
       && (forall k : Key | InBetween(left, right, k) && IsPrefix(prefix, k) ::
          && Keyspace.lte(left', Keyspace.Element(newPrefix + k[|prefix|..]))
          && Keyspace.lt(Keyspace.Element(newPrefix + k[|prefix|..]), right'))
  {
    var (left', right') := TranslatePivotPairInternal(left, right, prefix, newPrefix);

    forall k : Key | InBetween(left', right', k)
    ensures Keyspace.lte(left, Keyspace.Element(prefix + k[|newPrefix|..]))
    ensures Keyspace.lt(Keyspace.Element(prefix + k[|newPrefix|..]), right)
    {
      assert IsPrefix(newPrefix, k);
      assume |prefix + k[|newPrefix|..]| <= 1024;
      var k' : Key := prefix + k[|newPrefix|..];

      PrefixLteProperties(newPrefix, left'.e, k);
      PrefixLteProperties(prefix, left.e, k');

      if right.Max_Element? || !IsPrefix(prefix, right.e){
        if right.Max_Element? {
          assert Keyspace.lt(Keyspace.Element(k'), right);
        } else {
          assert Keyspace.lte(KeyToElement(prefix), left) by {
            SeqComparison.reveal_lte();
            PrefixLteProperties(prefix, prefix, left.e);
          }
          Keyspace.transitivity_le_lt(KeyToElement(prefix), left, right);
          assert Keyspace.lt(KeyToElement(prefix), right);
          KeyWithPrefixLt(prefix, right.e, k');
        }
      } else {
        PrefixLteProperties(newPrefix, k, right'.e);
        PrefixLteProperties(prefix, k', right.e);
      }
    }

    forall k : Key | InBetween(left, right, k) && IsPrefix(prefix, k) 
    ensures Keyspace.lte(left', Keyspace.Element(newPrefix + k[|prefix|..]))
    ensures Keyspace.lt(Keyspace.Element(newPrefix + k[|prefix|..]), right')
    {
      assume |newPrefix + k[|prefix|..]| <= 1024;
      var k' : Key := newPrefix + k[|prefix|..];

      PrefixLteProperties(prefix, left.e, k);
      PrefixLteProperties(newPrefix, left'.e, k');

      if right.Max_Element? || !IsPrefix(prefix, right.e){
        if right'.Element? {
          KeyWithPrefixLt(newPrefix, right'.e, k');
        }
      } else {
        PrefixLteProperties(prefix, k, right.e);
        PrefixLteProperties(newPrefix, k', right'.e);
      }
    }
  }

  function TranslatePivots(pt: PivotTable, prefix: Key, newPrefix: Key, end: Element, idx: int): (pt' : PivotTable)
  requires WFPivots(pt)
  requires 0 <= idx < NumBuckets(pt)
  requires forall i | 0 <= i < NumBuckets(pt) :: IsPrefix(prefix, pt[i].e)
  requires end.Element? ==> ElementIsKey(end)
  requires Keyspace.lt(TranslateElement(pt[|pt|-2], prefix, newPrefix), end)
  ensures WFPivots(pt')
  ensures |pt'| == |pt[idx..]|
  ensures forall i | 0 <= i <  NumBuckets(pt') :: 
      && IsPrefix(newPrefix, pt'[i].e)
      && pt[idx+i] == TranslateElement(pt'[i], newPrefix, prefix)
  ensures Last(pt') == end
  decreases |pt| - idx
  {
    reveal_IsPrefix();
    Keyspace.reveal_IsStrictlySorted();

    if idx + 1 == NumBuckets(pt) then (
      [ TranslateElement(pt[idx], prefix, newPrefix), end ]
    ) else (
      var pt' := [ TranslateElement(pt[idx], prefix, newPrefix) ] + TranslatePivots(pt, prefix, newPrefix, end, idx+1);
      PrefixLteProperties(prefix, pt[idx].e, pt[idx+1].e);
      PrefixLteProperties(newPrefix, pt'[0].e, pt'[1].e);
      pt'
    )
  }

  function TranslateEdges(et: EdgeTable, pt: PivotTable, idx: int) : (et': EdgeTable)
  requires WFPivots(pt)
  requires WFEdges(et, pt)
  requires 0 <= idx < |et|
  ensures |et'| == |et[idx..]|
  ensures forall i | 0 <= i < |et'| :: et'[i] == 
    (if et[i+idx].Some? then et[i+idx] else Some(PivotLcp(pt[i+idx], pt[i+idx+1])))
  decreases |et| - idx
  {
    Keyspace.reveal_IsStrictlySorted();
    var edge := if et[idx].Some? then et[idx] else Some(PivotLcp(pt[idx], pt[idx+1]));

    if idx + 1 == |et| then (
      [ edge ]
    ) else (
      [ edge ] + TranslateEdges(et, pt, idx+1)
    )
  }

  lemma TranslatePivotsEdgesPreserveTranslateKey(pt: PivotTable, et: EdgeTable, pt': PivotTable,
    et': EdgeTable, prefix: Key, newPrefix: Key, end: Element, key: Key, key': Key)
  requires WFPivots(pt)
  requires WFPivots(pt')
  requires |pt| == |pt'|
  requires WFEdges(et, pt)
  requires WFEdges(et', pt')
  requires BoundedKey(pt, key) && IsPrefix(prefix, key)
  requires BoundedKey(pt', key')
  requires Route(pt, key) == Route(pt', key')
  requires key' == newPrefix + key[|prefix|..]
  requires PivotLcp(pt'[0], Last(pt')) == newPrefix
  requires forall i | 0 <= i <  NumBuckets(pt') :: 
      && IsPrefix(newPrefix, pt'[i].e)
      && pt[i] == TranslateElement(pt'[i], newPrefix, prefix)
  requires var (_, right) := TranslatePivotPairInternal(pt'[0], Last(pt'), newPrefix, prefix);
    && right == Last(pt)
  requires et' == TranslateEdges(et, pt, 0)
  ensures TranslateKey(pt, et, key) == TranslateKey(pt', et', key')
  {
    var i := Route(pt, key);
    var lcp : Key := PivotLcp(pt[i], pt[i+1]);
    var lcp' : Key := PivotLcp(pt'[i], pt'[i+1]);

    Keyspace.reveal_IsStrictlySorted();
    PrefixOfLcpIsPrefixOfKey(pt[i], pt[i+1], lcp, key);
    PrefixOfLcpIsPrefixOfKey(pt'[i], pt'[i+1], lcp', key');

    if i+1 == NumBuckets(pt') {
      if pt'[i+1].Max_Element? || !IsPrefix(newPrefix, pt'[i+1].e) {
        assert PivotLcp(KeyToElement(prefix), Last(pt)) == prefix;

        var lkey : Key := pt[i].e;
        assert prefix[|prefix|..] == [];
        Lexi.EmptyLte(lkey[|prefix|..]);
        PrefixLteProperties(prefix, prefix, lkey);
        PivotLcpSubRangeRight(KeyToElement(prefix), pt[i], pt[i+1]);
        assert IsPrefix(prefix, lcp);

        PivotLcpSubRangeRight(pt'[0], pt'[i], pt'[i+1]);
        assert IsPrefix(newPrefix, lcp');

        if pt'[i+1].Max_Element? && pt[i+1].Max_Element? {
          SameLcprightSubfix(pt[i].e, prefix, pt'[i].e, newPrefix);
        } else if pt'[i+1].Max_Element? {
          SameLcpLcprightSubfix(pt'[i].e, newPrefix, pt[i].e, pt[i+1].e, prefix);
        } else if pt[i+1].Max_Element? {
          SameLcpLcprightSubfix(pt[i].e, prefix, pt'[i].e, pt'[i+1].e, newPrefix);
        } else {
          SameLcpLcpSubfix(pt[i].e, pt[i+1].e, prefix, pt'[i].e, pt'[i+1].e, newPrefix);
        }
      } else {
        SameLcpSubfix(pt[i].e, pt[i+1].e, prefix, pt'[i].e, pt'[i+1].e, newPrefix);
      }
    } else {
      SameLcpSubfix(pt[i].e, pt[i+1].e, prefix, pt'[i].e, pt'[i+1].e, newPrefix);
    }

    if et[i].Some? {
      assert et[i] == et'[i];
    } else {
      assert et'[i].value == lcp;
    }
  }

  lemma TranslatePivotsSameRoute(pt: PivotTable, pt': PivotTable, prefix: Key, prefix': Key, key: Key, key': Key)
  requires WFPivots(pt)
  requires WFPivots(pt')
  requires |pt| == |pt'|
  requires BoundedKey(pt, key) && IsPrefix(prefix, key)
  requires key' == prefix' + key[|prefix|..]
  requires forall i | 0 <= i <  NumBuckets(pt') :: 
      && IsPrefix(prefix', pt'[i].e)
      && pt[i] == TranslateElement(pt'[i], prefix', prefix)
  requires Keyspace.lt(KeyToElement(key'), Last(pt'))
  ensures BoundedKey(pt', key')
  ensures Route(pt, key) == Route(pt', key')
  {
    var i := Route(pt, key);

    PrefixLteProperties(prefix, pt[i].e, key);
    PrefixLteProperties(prefix', pt'[i].e, key');

    if i+1 < NumBuckets(pt) {
      PrefixLteProperties(prefix, key, pt[i+1].e);
      PrefixLteProperties(prefix', key', pt'[i+1].e);
    }

    RouteIs(pt', key', i);
  }

  function TranslateBucketInternal(keys: seq<Key>, msgs: seq<M.Message>, prefix: Key, newPrefix: Key) : (r: (seq<Key>, seq<M.Message>))
  requires |keys| == |msgs|
  ensures var (keys', msgs') := r;
    && |keys'| <= |keys|
    && |keys'| == |msgs'|
    && (forall i | 0 <= i < |keys'| :: IsPrefix(newPrefix, keys'[i]))
    && (forall i | 0 <= i < |msgs'| :: msgs'[i] in msgs)
  {
    reveal_IsPrefix();

    if |keys| > 0 then (
      var key : Key := Last(keys);
      var (keys', msgs') := TranslateBucketInternal(DropLast(keys), DropLast(msgs), prefix, newPrefix);
      if IsPrefix(prefix, key) then (
        var key' := newPrefix + key[|prefix|..]; 
        assume |key'| <= 1024;
        (keys' + [key'], msgs' + [Last(msgs)])
      ) else (
        (keys', msgs')
      )
    ) else (
      ([], [])
    )
  }

  function TranslateBucket(bucket: Bucket, prefix: Key, newPrefix: Key) : (res : Bucket)
  requires PreWFBucket(bucket)
  ensures WFBucket(bucket) ==> WFBucket(res)
  ensures PreWFBucket(res)
  decreases |bucket.keys|
  {
    var (keys', msgs') := TranslateBucketInternal(bucket.keys, bucket.msgs, prefix, newPrefix);
    Bucket(keys', msgs')
  }

  function TranslateBuckets(blist: BucketList, prefix: Key, newPrefix: Key) : (res : BucketList)
  requires forall i | 0 <= i < |blist| :: WFBucket(blist[i])
  ensures |res| == |blist|
  ensures forall i | 0 <= i < |res| :: 
      && WFBucket(res[i])
      && res[i] == TranslateBucket(blist[i], prefix, newPrefix)
  {
    if |blist| > 0 then (
      var newbucket := TranslateBucket(Last(blist), prefix, newPrefix);
      TranslateBuckets(DropLast(blist), prefix, newPrefix) + [ newbucket ]
    ) else (
      blist
    )
  }

  predicate SameSubfixKeys(keys: seq<Key>, keys': seq<Key>, prefix: Key, newPrefix: Key)
  {
    && |keys| == |keys'|
    && (forall i | 0 <= i < |keys| :: IsPrefix(prefix, keys[i]))
    && (forall i | 0 <= i < |keys'| :: IsPrefix(newPrefix, keys'[i]))
    && (forall i | 0 <= i < |keys| :: 
      && var key : Key := keys[i];
      && var key' : Key := keys'[i];
      && IsPrefix(newPrefix, key') 
      && key[|prefix|..] == key'[|newPrefix|..]
    )
  }

  lemma SortedBucketStaysSorted(keys: seq<Key>, msgs: seq<M.Message>, prefix: Key, newPrefix: Key)
  requires |keys| == |msgs|
  requires forall i | 0 <= i < |keys| :: IsPrefix(prefix, keys[i])
  ensures var (keys', msgs') := TranslateBucketInternal(keys, msgs, prefix, newPrefix);
    && (Lexi.IsStrictlySorted(keys) ==> Lexi.IsStrictlySorted(keys'))
    && SameSubfixKeys(keys, keys', prefix, newPrefix)
    && (msgs' == msgs)
  {
    reveal_IsPrefix();

    if |keys| > 0 {
      var (keys', msgs') := TranslateBucketInternal(DropLast(keys), DropLast(msgs), prefix, newPrefix);
      if |keys| > 1 && Lexi.IsStrictlySorted(keys) {
        var key : Key := Last(keys);
        assume |newPrefix + key[|prefix|..]| <= 1024;
        var key' := newPrefix + key[|prefix|..];
        
        Lexi.reveal_IsStrictlySorted();
        PrefixLteProperties(prefix, keys[|keys|-2], key);
        PrefixLteProperties(newPrefix, Last(keys'), key');
      }
      SortedBucketStaysSorted(DropLast(keys), DropLast(msgs), prefix, newPrefix);
    }
  }

  lemma SortedBucketListStaysSorted(blist: BucketList, prefix: Key, newPrefix: Key)
  requires forall i | 0 <= i < |blist| ::
      && WFBucket(blist[i])
      && (forall j | 0 <= j < |blist[i].keys| :: IsPrefix(prefix, blist[i].keys[j]))
  ensures var blist' := TranslateBuckets(blist, prefix, newPrefix);
      && (BucketListWellMarshalled(blist) ==> BucketListWellMarshalled(blist'))
      && (forall i | 0 <= i < |blist| :: SameSubfixKeys(blist[i].keys, blist'[i].keys, prefix, newPrefix))
  {
    if |blist| > 0 {
      SortedBucketStaysSorted(Last(blist).keys, Last(blist).msgs, prefix, newPrefix);
      SortedBucketListStaysSorted(DropLast(blist), prefix, newPrefix);
    }
  }

  lemma TranslateBucketSameMessage(bucket: Bucket, bucket': Bucket, 
    prefix: Key, newPrefix: Key, key: Key, key': Key)
  requires WFBucket(bucket)
  requires WFBucket(bucket')
  requires Lexi.IsStrictlySorted(bucket.keys)
  requires bucket' == TranslateBucket(bucket, prefix, newPrefix)
  requires forall i | 0 <= i < |bucket.keys| :: IsPrefix(prefix, bucket.keys[i])
  requires IsPrefix(prefix, key)
  requires key' == newPrefix + key[|prefix|..]
  ensures key in bucket.as_map() <==> key' in bucket'.as_map()
  ensures key in bucket.as_map() ==> (bucket.as_map()[key] == bucket'.as_map()[key'])
  {
    SortedBucketStaysSorted(bucket.keys, bucket.msgs, prefix, newPrefix);
    key_sets_eq(bucket.keys, bucket.msgs);
    key_sets_eq(bucket'.keys, bucket'.msgs);

    if key in bucket.keys {
      var i := GetIndex(bucket.keys, bucket.msgs, key);
      assert bucket.keys[i] == key;
      assert bucket'.keys[i] == key';

      MapMapsIndex(bucket.keys, bucket.msgs, i);
      MapMapsIndex(bucket'.keys, bucket'.msgs, i);
    } else {
      if key' in bucket'.keys {
        var i := GetIndex(bucket'.keys, bucket'.msgs, key');
        assert key == prefix + key'[|newPrefix|..];
        assert bucket.keys[i] == key;
        assert false;
      }
    }
  }

  lemma BucketKeysHasPrefix(bucket: Bucket, pt: PivotTable, i: int, prefix: Key)
  requires 0 <= i < NumBuckets(pt)
  requires WFPivots(pt)
  requires WFBucketAt(bucket, pt, i)
  requires Keyspace.lt(pt[0], Last(pt))
  requires AllKeysInBetweenHasPrefix(pt[0], Last(pt), prefix);
  ensures forall k | k in bucket.keys :: IsPrefix(prefix, k)
  {
    forall k | k in bucket.keys
    ensures IsPrefix(prefix, k)
    {
      assert BoundedKey(pt, k);
      assert InBetween(pt[0], pt[|pt|-1], k);
    }
  }

  lemma SameLcpSubfix(left: Key, right: Key, prefix: Key, left': Key, right': Key, prefix': Key)
  requires IsPrefix(prefix, left) && IsPrefix(prefix, right)
  requires IsPrefix(prefix', left') && IsPrefix(prefix', right')
  requires left[|prefix|..] == left'[|prefix'|..]
  requires right[|prefix|..] == right'[|prefix'|..]
  ensures var Lcp : Key := lcp(left, right);
    && var Lcp' : Key := lcp(left', right');
    && IsPrefix(prefix, Lcp)
    && IsPrefix(prefix', Lcp')
    && Lcp[|prefix|..] == Lcp'[|prefix'|..]
  {
    reveal_IsPrefix();
    SeqComparison.reveal_lte();

    if |prefix| > 0 && |prefix'| > 0 {
      SameLcpSubfix(left[1..], right[1..], prefix[1..], left'[1..], right'[1..], prefix'[1..]);
    } else if |prefix| == 0 && |prefix'| > 0 {
      SameLcpSubfix(left, right, prefix, left'[1..], right'[1..], prefix'[1..]);
    } else if |prefix| > 0 && |prefix'| == 0 {
      SameLcpSubfix(left[1..], right[1..], prefix[1..], left', right', prefix');
    }
  }

  lemma SameLcprightSubfix(left: Key, prefix: Key, left': Key, prefix': Key)
  requires IsPrefix(prefix, left)
  requires IsPrefix(prefix', left')
  requires left[|prefix|..] == left'[|prefix'|..]
  requires IsPrefix(prefix, lcpright(left))
  requires IsPrefix(prefix', lcpright(left'))
  ensures var Lcp : Key := lcpright(left);
    && var Lcp' : Key := lcpright(left');
    && Lcp[|prefix|..] == Lcp'[|prefix'|..]
  {
    reveal_IsPrefix();
    SeqComparison.reveal_lte();

    if |prefix| > 0 && |prefix'| > 0 {
      SameLcprightSubfix(left[1..], prefix[1..], left'[1..], prefix'[1..]);
    } else if |prefix| == 0 && |prefix'| > 0 {
      SameLcprightSubfix(left, prefix, left'[1..], prefix'[1..]);
    } else if |prefix| > 0 && |prefix'| == 0 {
      SameLcprightSubfix(left[1..], prefix[1..], left', prefix');
    }
  }

  lemma SameLcpLcprightSubfix(left: Key, prefix: Key, left': Key, right': Key, prefix': Key)
  requires IsPrefix(prefix, left)
  requires IsPrefix(prefix', left')
  requires left[|prefix|..] == left'[|prefix'|..]
  requires !IsPrefix(prefix', right')
  requires SeqComparison.lt(left', right')
  requires IsPrefix(prefix, lcpright(left))
  requires IsPrefix(prefix', lcp(left', right'))
  ensures var Lcp : Key := lcpright(left);
    && var Lcp' : Key := lcp(left', right');
    && Lcp[|prefix|..] == Lcp'[|prefix'|..]
  {
    reveal_IsPrefix();
    SeqComparison.reveal_lte();

    if |prefix'| > 0 {
      var newleft := if |prefix| > 0 then left[1..] else left;
      var newprefix := if |prefix| > 0 then prefix[1..] else prefix;

      if |right'| > 0 && prefix'[0] == right'[0] {
        SameLcpLcprightSubfix(newleft, newprefix, left'[1..], right'[1..], prefix'[1..]);
      } else {
        SameLcprightSubfix(newleft, newprefix, left'[1..], prefix'[1..]);
      }
    }
  }

  lemma SameLcpLcpSubfix(left: Key, right: Key, prefix: Key, left': Key, right': Key, prefix': Key)
  requires IsPrefix(prefix, left)
  requires IsPrefix(prefix', left')
  requires left[|prefix|..] == left'[|prefix'|..]
  requires !IsPrefix(prefix, right)
  requires !IsPrefix(prefix', right')
  requires SeqComparison.lt(left, right)
  requires SeqComparison.lt(left', right')
  requires IsPrefix(prefix, lcp(left, right))
  requires IsPrefix(prefix', lcp(left', right'))
  ensures var Lcp : Key := lcp(left, right);
    && var Lcp' : Key := lcp(left', right');
    && Lcp[|prefix|..] == Lcp'[|prefix'|..]
  {
    reveal_IsPrefix();
    SeqComparison.reveal_lte();

    if |prefix| > 0 && |prefix'| > 0 {
      if |right| > 0 && |right'| > 0 && prefix[0] == right[0] && prefix'[0] == right'[0] {
        SameLcpLcpSubfix(left[1..], right[1..], prefix[1..], left'[1..], right'[1..], prefix'[1..]);
      } else if |right| > 0 && prefix[0] == right[0] {
        SameLcpLcprightSubfix(left'[1..], prefix'[1..], left[1..], right[1..], prefix[1..]);
      } else if |right'| > 0 && prefix'[0] == right'[0] {
        SameLcpLcprightSubfix(left[1..], prefix[1..], left'[1..], right'[1..], prefix'[1..]); 
      } else {
        SameLcprightSubfix(left[1..], prefix[1..], left'[1..], prefix'[1..]);
      }
    }
  }

  predicate ParentKeysInChildRange(parentpivots: PivotTable, parentedges: EdgeTable, childpivots: PivotTable, slot: int)
  requires WFPivots(parentpivots)
  requires WFPivots(childpivots)
  requires WFEdges(parentedges, parentpivots)
  requires 0 <= slot < |parentedges|
  {
    Keyspace.reveal_IsStrictlySorted();
    && (parentedges[slot].None? ==> 
        ContainsRange(childpivots, parentpivots[slot], parentpivots[slot+1]))
    && (parentedges[slot].Some? ==> 
        && var (left, right) := TranslatePivotPair(parentpivots, parentedges, slot);
        && ContainsRange(childpivots, left, right))
  }

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
