include "BoundedPivotsLib.i.dfy"
include "BucketsLib.i.dfy"
include "MapSeqs.i.dfy"
include "TranslationApply.s.dfy"

include "../Base/KeyType.s.dfy"
include "../Lang/System/SeqComparison.s.dfy"

//
// Provides definitions and libraries for edge table and 
// other translation related functions and lemma
//

module TranslationLib {
  import opened NativeTypes
  import opened BoundedPivotsLib
  import opened BucketsLib
  import opened MapSeqs
  import opened Sequences
  import opened Options
  import opened KeyType
  import opened TranslationApply

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

  function {:timeLimitMultiplier 4} SplitLeftEdges(et: EdgeTable, pt: PivotTable, pivot: Key) : (et': EdgeTable)
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

      var oldlcp := PivotLcp(pt[cLeft], pt[cLeft+1]);
      var newlcp := PivotLcp(pt'[cLeft], pt'[cLeft+1]);
      PivotLcpSubRangeLeft(pt[cLeft], pt[cLeft+1], pt'[cLeft+1]);

      var translation := changePrefix(oldlcp, et[cLeft].value, newlcp);
      var et' := et[..cLeft] +  [Some(translation)];

      assert TranslationPreserved(pt, et, pt', et') by {
        forall key | BoundedKey(pt', key)
        ensures BoundedKey(pt, key)
        ensures TranslateKey(pt', et', key) == TranslateKey(pt, et, key)
        {
          var i := Route(pt, key);
          if i == cLeft {
            var tkey := TranslateKey(pt, et, key);
            var tkey' := TranslateKey(pt', et', key);
            calc {
              tkey';
              et'[cLeft].value + key[|newlcp|..];
              et[cLeft].value + newlcp[|oldlcp|..] + key[|newlcp|..];
              tkey;
            }
          }
        }
      }

      et'
    )
  }

  function  {:timeLimitMultiplier 4} SplitRightEdges(et: EdgeTable, pt: PivotTable, pivot: Key) : (et': EdgeTable)
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

      var oldlcp := PivotLcp(pt[cRight], pt[cRight+1]);
      var newlcp := PivotLcp(pt'[0], pt'[1]);
      PivotLcpSubRangeRight(pt[cRight], pt'[0], pt'[1]);

      var translation := changePrefix(oldlcp, et[cRight].value, newlcp);
      var et' := [Some(translation)] + et[cRight+1..];

      assert TranslationPreserved(pt, et, pt', et') by {
        forall key | BoundedKey(pt', key)
        ensures BoundedKey(pt, key)
        ensures TranslateKey(pt', et', key) == TranslateKey(pt, et, key)
        {
          var i := Route(pt, key);
          if i == cRight {
            var tkey := TranslateKey(pt, et, key);
            var tkey' := TranslateKey(pt', et', key);
            calc {
              tkey';
              et'[0].value + key[|newlcp|..];
              et[cRight].value + newlcp[|oldlcp|..] + key[|newlcp|..];
              tkey;
            }
          }
        }
      }

      et'
    )
  }

  lemma {:timeLimitMultiplier 3} WFConcatEdges(leftpt: PivotTable, leftet: EdgeTable, rightpt: PivotTable, rightet: EdgeTable, pt: PivotTable)
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

  // lcp functions and lemma

  function lcpright(left: Key): (prefix: Key)
  ensures IsPrefix(prefix, left)
  ensures SeqComparison.lte(prefix, left)
  {
    reveal_IsPrefix();
    SeqComparison.reveal_lte();

    if |left| > 0 && left[0] as int == Uint8UpperBound() as int - 1 then
      [left[0]] + lcpright(left[1..])
    else
      []
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

  lemma lcprightCorrect(left: Key, prefix: Key, key: Key)
  requires lcpright(left) == prefix
  requires SeqComparison.lte(left, key)
  ensures IsPrefix(prefix, key)
  {
    reveal_IsPrefix();
    SeqComparison.reveal_lte();

    if |left| > 0 && left[0] as int == Uint8UpperBound() as int - 1 {
      lcprightCorrect(left[1..], prefix[1..], key[1..]);
    }
  }

  lemma lcprightSubRangeRight(left: Key, left': Key, prefix: Key, prefix': Key)
  requires lcpright(left) == prefix
  requires lcpright(left') == prefix'
  requires SeqComparison.lte(left, left')
  ensures IsPrefix(prefix, prefix')
  {
    reveal_IsPrefix();
    SeqComparison.reveal_lte();

    if |left| > 0 && left[0] as int == Uint8UpperBound() as int - 1 {
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

    if |left| > 0 && left[0] as int == Uint8UpperBound() as int - 1 {
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

  function RevPrefixSet(pset: Option<PrefixSet>) : Option<PrefixSet>
  {
    if pset.None? then None else Some(PrefixSet(pset.value.newPrefix, pset.value.prefix))
  }

  function method ApplyPrefixSet(pset: Option<PrefixSet>, key: Key) : (key': Key)
  requires pset.Some? ==> IsPrefix(pset.value.prefix, key)
  ensures pset.Some? ==> IsPrefix(pset.value.newPrefix, key')
  {
    if pset.None? then key 
    else (
      reveal_IsPrefix();
      changePrefix(pset.value.prefix, pset.value.newPrefix, key)
    )
  }

  function ComposePrefixSet(a: Option<PrefixSet>, b: Option<PrefixSet>): (c: Option<PrefixSet>)
  requires a.Some? && b.Some? ==> 
    ( IsPrefix(a.value.prefix, b.value.prefix)
    || IsPrefix(b.value.prefix, a.value.prefix))
  {
    if a == None then (
      RevPrefixSet(b)
    ) else if b == None then (
      a
    ) else (
      reveal_IsPrefix();
      if |a.value.prefix| <= |b.value.prefix| then (
        var newPrefix := ApplyPrefixSet(a, b.value.prefix);  
        Some(PrefixSet(b.value.newPrefix, newPrefix))
      ) else (
        var prefix := ApplyPrefixSet(b, a.value.prefix);
        Some(PrefixSet(prefix, a.value.newPrefix))
      )
    )
  }

  lemma ComposePrefixSetCorrect(a: Option<PrefixSet>, b: Option<PrefixSet>, c: Option<PrefixSet>, 
    key: Key, akey: Key, ckey: Key)
  requires a.Some? && b.Some? ==> 
    ( IsPrefix(a.value.prefix, b.value.prefix)
    || IsPrefix(b.value.prefix, a.value.prefix))
  requires c == ComposePrefixSet(a, b)
  requires a.Some? ==> IsPrefix(a.value.prefix, akey)
  requires b.Some? ==> IsPrefix(b.value.prefix, akey)
  requires c.Some? ==> IsPrefix(c.value.prefix, ckey)
  requires a == c ==> akey == ckey
  requires key == ApplyPrefixSet(a, akey)
  ensures ApplyPrefixSet(b, akey) == ckey ==> key == ApplyPrefixSet(c, ckey)
  ensures key == ApplyPrefixSet(c, ckey) ==> ApplyPrefixSet(b, akey) == ckey
  {
    reveal_IsPrefix();
  }

  // given a prefix find its upperbound s.t. lcp(prefix, upper) == prefix
  function {:opaque} ShortestUncommonPrefix(prefix: Key, idx: int): (upper: Element)
  requires 0 <= idx <= |prefix|
  requires forall i | idx < i < |prefix| :: prefix[i] as int == (Uint8UpperBound() as int - 1)
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

    if idx < |prefix| && prefix[idx] as int < Uint8UpperBound() as int - 1
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
  requires forall i | 0 <= i < |prefix| :: prefix[i] as int == (Uint8UpperBound() as int - 1)
  ensures lcpright(prefix) == prefix
  {
    if |prefix| > 0 {
      prefixIslcpright(prefix[1..]);
    }
  }

  lemma prefixIslcp(prefix: Key, upper: Key)
  requires 0 < |upper| <= |prefix|
  requires IsPrefix(prefix[..|upper|-1], upper)
  requires upper[|upper|-1] as int == (prefix[|upper|-1] as int + 1)
  requires forall i | |upper| <= i < |prefix| :: prefix[i] as int == (Uint8UpperBound() as int - 1)
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
    KeyToElement(changePrefix(prefix, newPrefix, e.e))
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

  lemma AllKeysWithPrefixLt(prefix: Key, right: Key)
  requires SeqComparison.lt(prefix, right)
  requires !IsPrefix(prefix, right)
  ensures forall k : Key | IsPrefix(prefix, k) :: SeqComparison.lt(k, right)
  {
    forall k : Key | IsPrefix(prefix, k)
    ensures SeqComparison.lt(k, right) 
    {
      KeyWithPrefixLt(prefix, right, k);
    }
  }

  lemma KeyLtPrefix(prefix: Key, key: Key)
  requires SeqComparison.lt(key, prefix)
  ensures !IsPrefix(prefix, key)
  {
    reveal_IsPrefix();
    SeqComparison.reveal_lte();

    if |key| > 0 && key[0] == prefix[0] {
      KeyLtPrefix(prefix[1..], key[1..]);
    }
  }

  lemma AllKeysLtPrefix(prefix: Key)
  ensures forall k : Key | SeqComparison.lt(k, prefix) :: !IsPrefix(prefix, k)
  {
    forall k : Key | SeqComparison.lt(k, prefix)
    ensures !IsPrefix(prefix, k) 
    {
      KeyLtPrefix(prefix, k);
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
      var k' := changePrefix(newPrefix, prefix, k);

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
      var k' := changePrefix(prefix, newPrefix, k);

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

  // translated bucket and idxs of corresponding keys
  datatype TBucket = TBucket(b: Bucket, ghost idxs: seq<int>)

  predicate {:opaque} WFTBucket(bucket: Bucket, tbucket: TBucket, prefix: Key, tPrefix: Key, idx: int)
  requires 0 <= idx <= |bucket.keys|
  {
    && PreWFBucket(bucket)
    && PreWFBucket(tbucket.b)
    && |tbucket.b.keys| <= |bucket.keys[idx..]|
    && |tbucket.b.keys| == |tbucket.idxs|
    && (forall i | 0 <= i < |tbucket.b.keys| ::
        && idx <= tbucket.idxs[i] < |bucket.keys|
        && var tkey : Key := tbucket.b.keys[i];
        && var key : Key := bucket.keys[tbucket.idxs[i]];
        && IsPrefix(prefix, key)
        && tkey == ApplyPrefixSet(Some(PrefixSet(prefix, tPrefix)), key)
        && bucket.msgs[tbucket.idxs[i]] == tbucket.b.msgs[i])
    && (forall i, j | 0 <= i < j < |tbucket.idxs| :: tbucket.idxs[i] < tbucket.idxs[j])
    && (forall i | idx <= i < |bucket.keys| && i !in tbucket.idxs :: !IsPrefix(prefix, bucket.keys[i]))
  }

  function TranslateBucketInternal(bucket: Bucket, prefix: Key, newPrefix: Key, idx: int) : (tbucket: TBucket)
  requires PreWFBucket(bucket)
  requires 0 <= idx <= |bucket.keys|
  ensures WFTBucket(bucket, tbucket, prefix, newPrefix, idx)
  ensures WFBucket(bucket) ==> WFBucket(tbucket.b)
  ensures BucketWellMarshalled(bucket) ==> BucketWellMarshalled(tbucket.b)
  decreases |bucket.keys| - idx
  {
    reveal_WFTBucket();

    if idx == |bucket.keys| then (
      TBucket(Bucket([], []), [])
    ) else (
      reveal_IsPrefix();
      if IsPrefix(prefix, bucket.keys[idx]) then (
        var key := bucket.keys[idx];
        var key' := changePrefix(prefix, newPrefix, key);

        var tbucket := TranslateBucketInternal(bucket, prefix, newPrefix, idx + 1);
        var tbucket' := TBucket(Bucket([key'] + tbucket.b.keys, [bucket.msgs[idx]] + tbucket.b.msgs), [idx] + tbucket.idxs);

        assert BucketWellMarshalled(bucket) ==> BucketWellMarshalled(tbucket'.b) by {
          if BucketWellMarshalled(bucket) && |tbucket'.b.keys| > 1 {
            Lexi.IsStrictlySortedImpliesLt(bucket.keys, idx, tbucket.idxs[0]);
            PrefixLteProperties(prefix, key,  bucket.keys[tbucket.idxs[0]]);
            PrefixLteProperties(newPrefix, key',  tbucket.b.keys[0]);
            Lexi.reveal_IsStrictlySorted();
          }
        }

        tbucket'
      ) else (
        TranslateBucketInternal(bucket, prefix, newPrefix, idx + 1)
      )
    )
  }

  function TranslateBucket(bucket: Bucket, prefix: Key, newPrefix: Key) : (res : Bucket)
  requires PreWFBucket(bucket)
  ensures WFBucket(bucket) ==> WFBucket(res)
  ensures PreWFBucket(res)
  ensures BucketWellMarshalled(bucket) ==> BucketWellMarshalled(res)
  {
    var tbucket := TranslateBucketInternal(bucket, prefix, newPrefix, 0);
    tbucket.b
  }

  function TranslateBuckets(blist: BucketList, prefix: Key, newPrefix: Key) : (res : BucketList)
  requires forall i | 0 <= i < |blist| :: WFBucket(blist[i])
  ensures |res| == |blist|
  ensures forall i | 0 <= i < |res| :: 
      && WFBucket(res[i])
      && res[i] == TranslateBucket(blist[i], prefix, newPrefix)
  ensures BucketListWellMarshalled(blist) ==> BucketListWellMarshalled(res)
  {
    if |blist| > 0 then (
      var newbucket := TranslateBucket(Last(blist), prefix, newPrefix);
      TranslateBuckets(DropLast(blist), prefix, newPrefix) + [ newbucket ]
    ) else (
      blist
    )
  }

  lemma TranslateBucketSameMessage(bucket: Bucket, bucket': Bucket, 
    prefix: Key, newPrefix: Key, key: Key, key': Key)
  requires WFBucket(bucket)
  requires WFBucket(bucket')
  requires BucketWellMarshalled(bucket)
  requires bucket' == TranslateBucket(bucket, prefix, newPrefix)
  requires IsPrefix(prefix, key)
  requires key' == newPrefix + key[|prefix|..]
  ensures key in bucket.as_map() <==> key' in bucket'.as_map()
  ensures key in bucket.as_map() ==> (bucket.as_map()[key] == bucket'.as_map()[key'])
  {
    var tbucket := TranslateBucketInternal(bucket, prefix, newPrefix, 0);
    assert tbucket.b == bucket';

    key_sets_eq(bucket.keys, bucket.msgs);
    key_sets_eq(bucket'.keys, bucket'.msgs);

    reveal_IsPrefix();
    if key' in bucket'.keys {
      var i' := GetIndex(bucket'.keys, bucket'.msgs, key');
      var i := tbucket.idxs[i'];

      assert bucket.keys[i] == key;
      assert bucket'.keys[i'] == key';

      MapMapsIndex(bucket.keys, bucket.msgs, i);
      MapMapsIndex(bucket'.keys, bucket'.msgs, i');
    } else {
      if key in bucket.keys {
        var i := GetIndex(bucket.keys, bucket.msgs, key);
        if i in tbucket.idxs {
          var i' :| 0 <= i' < |tbucket.idxs| && tbucket.idxs[i'] == i;
          assert bucket'.keys[i'] == key';
        }
        assert false;
      }
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
}
