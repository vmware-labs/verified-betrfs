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
  import opened TranslationApply
  import opened Sequences
  import opened Options
  import opened KeyType
  import opened ValueType`Internal
  import opened ValueMessage
  import opened BucketImpl
  import opened BucketsLib
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

      var translation := changePrefix(oldlcp, et[cLeft].value, newlcp);
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

      var translation := changePrefix(oldlcp, et[cRight].value, newlcp);
      return [Some(translation)] + et[cRight+1..];
    }
  }

  lemma lcprightCondition(s: Key, len: nat)
    requires len <= |s|
    requires forall j | 0 <= j < len :: s[j] == 255
    requires len == |s| || s[len] < 255
    ensures s[..len] == lcpright(s)
  {
    if |s| == 0 || s[0] < 255 {
    } else {
      lcprightCondition(s[1..], len-1);
    }
  }

  method ComputelcprightLen(left: Key) returns (len: uint64)
  ensures len as nat == |lcpright(left)|
  {
    var i: uint64 := 0;
    var llen := |left| as uint64;

    while i < llen && left[i] == 255
      invariant 0 <= i <= llen
      invariant forall j | 0 <= j < i :: left[j] as int == Uint8UpperBound() as int - 1
    {
      i := i + 1;
    }
    lcprightCondition(left, i as nat);
    return i;
  }

  method Computelcpright(left: Key) returns (prefix: Key)
  ensures prefix == lcpright(left)
  {
    var len := ComputelcprightLen(left);
    return left[..len];
  }

  lemma lcpCondition(left: Key, right: Key, common_len: nat)
    requires common_len <= |left|
    requires common_len <= |right|
    requires forall j | 0 <= j < common_len :: left[j] == right[j]
    requires common_len == |left| || common_len == |right| || left[common_len] != right[common_len]
    ensures lcp(left, right) ==
      if common_len < |left| && common_len + 1 == |right| && left[common_len] as nat + 1 == right[common_len] as nat then
        left[..common_len + 1] + lcpright(left[common_len + 1..])
      else
        left[..common_len]
  {
    if 0 < common_len {
      lcpCondition(left[1..], right[1..], common_len-1);
    }
  }

  method ComputelcpLen(left: Key, right: Key) returns (len: uint64)
  ensures len as nat == |lcp(left, right)|
  {
    var i: uint64 := 0;
    while
      && i < |left| as uint64
      && i < |right| as uint64
      && left[i] == right[i]
      invariant i as nat <= |left|
      invariant i as nat <= |right|
      invariant forall j | j < i :: left[j] == right[j]
    {
      i := i + 1;
    }
    lcpCondition(left, right, i as nat);

    if
      && i < |left| as uint64
      && i + 1 == |right| as uint64
      && left[i] < right[i]
      && left[i] + 1 == right[i] {
        i := i + 1;
        ghost var s := i;
        while
          && i < |left| as uint64
          && left[i] == 255
          invariant s as nat <= i as nat <= |left|
          invariant forall j | s <= j < i :: left[j] == 255
        {
          i := i + 1;
        }
        lcprightCondition(left[s..], i as nat - s as nat);
    }
    len := i;
  }

  method Computelcp(left: Key, right: Key) returns (prefix: Key)
  ensures prefix == lcp(left, right)
  {
    var len := ComputelcpLen(left, right);
    prefix := left[..len];
  }

  method ComputePivotLcpLen(left: Element, right: Element) returns (len: uint64)
  requires ElementIsKey(left)
  requires right.Element? ==> ElementIsKey(right)
  ensures len as nat == |PivotLcp(left, right)|
  {
    if right.Max_Element? {
      len := ComputelcprightLen(left.e);
    } else {
      len := ComputelcpLen(left.e, right.e);
    }
  }

  method ComputePivotLcp(left: Element, right: Element) returns (prefix: Key)
  requires ElementIsKey(left)
  requires right.Element? ==> ElementIsKey(right)
  ensures prefix == PivotLcp(left, right)
  {
    var len := ComputePivotLcpLen(left, right);
    prefix := left.e[..len];
  }

  method ComputeTranslatePrefixSet(pt: PivotTable, et: EdgeTable, key: Key, r: uint64) returns (pset: Option<PrefixSet>)
  requires |pt| < 0x4000_0000_0000_0000
  requires WFPivots(pt)
  requires BoundedKey(pt, key)
  requires WFEdges(et, pt)
  requires r as int == Route(pt, key)
  ensures pset == Translate(pt, et, key)
  {
    if et[r].Some? {
      var prefixlen := ComputePivotLcpLen(pt[r], pt[r+1]);
      PrefixOfLcpIsPrefixOfKey(pt[r], pt[r+1], pt[r].e[..prefixlen], key);
      pset := Some(PrefixSet(pt[r].e[..prefixlen], et[r].value));
    } else {
      pset := None;
    }
  }

  method ComputeTranslateKey(pt: PivotTable, et: EdgeTable, key: Key, r: uint64) returns (k: Key)
  requires |pt| < 0x4000_0000_0000_0000
  requires WFPivots(pt)
  requires BoundedKey(pt, key)
  requires WFEdges(et, pt)
  requires r as int == Route(pt, key)
  ensures k == TranslateKey(pt, et, key)
  {
    if et[r].Some? {
      var prefixlen := ComputePivotLcpLen(pt[r], pt[r+1]);
      PrefixOfLcpIsPrefixOfKey(pt[r], pt[r+1], pt[r].e[..prefixlen], key);
      k := changePrefix(pt[r].e[..prefixlen], et[r].value, key);
    } else {
      k := key;
    }
  }

  method ComputeComposePrefixSet(a: Option<PrefixSet>, b: Option<PrefixSet>) returns (c: Option<PrefixSet>)
  requires ComposePrefixSet.requires(a, b)
  ensures c == ComposePrefixSet(a, b)
  {
    if b.None? {
      c := a;
    } else if a.None? {
      c := Some(PrefixSet(b.value.newPrefix, b.value.prefix));
    } else if |a.value.prefix| as uint64 <= |b.value.prefix| as uint64 {
      reveal_IsPrefix();
      var newPrefix := ApplyPrefixSet(a, b.value.prefix);
      c := Some(PrefixSet(b.value.newPrefix, newPrefix));
    } else {
      var prefix := ApplyPrefixSet(b, a.value.prefix);
      c := Some(PrefixSet(prefix, a.value.newPrefix));
    }
  }

  method ComputeShortestUncommonPrefix(prefix: Key) returns (upper: Element)
  ensures upper == ShortestUncommonPrefix(prefix, |prefix|)
  {
    reveal_ShortestUncommonPrefix();
    var i: int64 := |prefix| as int64 - 1;
    while 0 <= i && prefix[i] == 255
      invariant -1 <= i as int < |prefix|
      invariant forall j | i as int < j < |prefix| :: prefix[j] == 255
      invariant ShortestUncommonPrefix(prefix, |prefix|) == ShortestUncommonPrefix(prefix, i as int + 1)
    {
      i := i - 1;
    }
    if i == -1 {
      upper := Keyspace.Max_Element;
    } else {
      var c := prefix[i] + 1;
      upper := Keyspace.Element(prefix[..i] + [c]);
    }
  }

  method ComputeTranslateElement(e: Element, prefix: Key, newPrefix: Key) returns (e': Element)
  requires ElementIsKey(e)
  requires IsPrefix(prefix, e.e)
  ensures e' == TranslateElement(e, prefix, newPrefix)
  {
    e' := Keyspace.Element(newPrefix + e.e[|prefix| as uint64..]);
  }

  method ComputeTranslatePivotPair(left: Key, right: Element, prefix: Key, newPrefix: Key)
  returns (left': Key, right': Element)
  requires right.Element? ==> ElementIsKey(right)
  requires IsPrefix(prefix, left)
  requires Keyspace.lt(KeyToElement(left), right)
  ensures var (l, r) := TranslatePivotPairInternal(KeyToElement(left), right, prefix, newPrefix);
    && l == KeyToElement(left')
    && r == right'
  {
    reveal_IsPrefix();
    left' := changePrefix(prefix, newPrefix, left);
    var isprefix := right.Element? && |prefix| as uint64 <= |right.e| as uint64 && prefix == right.e[..|prefix|];
    if right.Max_Element? || !isprefix {
      right' := ComputeShortestUncommonPrefix(newPrefix);
    } else {
      right' := ComputeTranslateElement(right, prefix, newPrefix);
    }
  }

  lemma TranslatePivotsCondition(pt: PivotTable, prefix: Key, newPrefix: Key, end: Element, idx: nat, pt': PivotTable)
    requires TranslatePivots.requires(pt, prefix, newPrefix, end, idx)
    requires |pt'| == |pt| - idx
    requires forall i | 0 <= i < |pt'| - 1 :: pt'[i] == TranslateElement(pt[idx + i], prefix, newPrefix)
    requires Last(pt') == end
    ensures pt' == TranslatePivots(pt, prefix, newPrefix, end, idx)
    decreases |pt'|
  {
    if idx + 1 == NumBuckets(pt) {
    } else {
      TranslatePivotsCondition(pt, prefix, newPrefix, end, idx+1, pt'[1..]);
    }
  }

  method ComputeTranslatePivots(pt: PivotTable, prefix: Key, newPrefix: Key, end: Element) returns (pt': PivotTable)
  requires |pt| < Uint64UpperBound()
  requires WFPivots(pt)
  requires forall i | 0 <= i < NumBuckets(pt) :: IsPrefix(prefix, pt[i].e)
  requires end.Element? ==> ElementIsKey(end)
  requires Keyspace.lt(TranslateElement(pt[|pt|-2], prefix, newPrefix), end)
  ensures pt' == TranslatePivots(pt, prefix, newPrefix, end, 0)
  {
    linear var result := seq_alloc_init(|pt| as uint64, end);

    var i := 0;
    while i < |pt| as uint64 - 1
      invariant 0 <= i <= |pt| as uint64 - 1
      invariant |result| == |pt|
      invariant forall j | 0 <= j < i :: result[j] == TranslateElement(pt[j], prefix, newPrefix)
      invariant Last(result) == end
    {
      var tmp := ComputeTranslateElement(pt[i], prefix, newPrefix);
      mut_seq_set(inout result, i, tmp);
      i := i + 1;
    }
    pt' := seq_unleash(result);
    TranslatePivotsCondition(pt, prefix, newPrefix, end, 0, pt');
  }

  lemma TranslateEdgesCondition(et: EdgeTable, pt: PivotTable, idx: int, et': EdgeTable)
    requires TranslateEdges.requires(et, pt, idx)
    requires |et'| == |et| - idx
    requires forall i | 0 <= i < |et'| :: et'[i] == if et[idx + i].Some? then et[idx + i] else Some(PivotLcp(pt[idx + i], pt[idx + i +1]))
    ensures et' == TranslateEdges(et, pt, idx)
    decreases |et'|
  {
  }

  method ComputeTranslateEdges(et: EdgeTable, pt: PivotTable) returns (et': EdgeTable)
  requires |et| < Uint64UpperBound()
  requires WFPivots(pt)
  requires WFEdges(et, pt)
  ensures et' == TranslateEdges(et, pt, 0)
  {
    linear var result := seq_alloc(|et| as uint64, None);

    var i := 0;
    while i < |et| as uint64
      invariant 0 <= i <= |et| as uint64
      invariant |result| == |et|
      invariant forall j | 0 <= j < i :: result[j] == if et[j].Some? then et[j] else Some(PivotLcp(pt[j], pt[j+1]));
    {
      if et[i].Some? {
        mut_seq_set(inout result, i, et[i]);
      } else {
        var newPrefix := ComputePivotLcp(pt[i], pt[i+1]);
        mut_seq_set(inout result, i, Some(newPrefix));
      }
      i := i + 1;
    }
    et' := seq_unleash(result);
    TranslateEdgesCondition(et, pt, 0, et');
  }

  function {:opaque} TranslateBucketSimple(bucket: Bucket, prefix: Key, newPrefix: Key, i: nat) : (result: Bucket)
    requires PreWFBucket(bucket)
    requires 0 <= i <= |bucket.keys|
    ensures |result.keys| <= i
    ensures PreWFBucket(result)
    ensures EncodableMessageSeq(bucket.msgs) ==> EncodableMessageSeq(result.msgs)
    decreases i
  {
    if i == 0 then
      EmptyBucket()
    else if IsPrefix(prefix, bucket.keys[i - 1]) then
      reveal_IsPrefix();
      var prefixBucket := TranslateBucketSimple(bucket, prefix, newPrefix, i - 1);
      var oldkey := bucket.keys[i - 1];
      var newKey := changePrefix(prefix, newPrefix, oldkey);
      Bucket(prefixBucket.keys + [ newKey ], prefixBucket.msgs + [ bucket.msgs[i - 1] ])
    else
      TranslateBucketSimple(bucket, prefix, newPrefix, i - 1)
  }

  lemma TranslateBucketSimpleEquivalence(bucket: Bucket, prefix: Key, newPrefix: Key)
    requires PreWFBucket(bucket)
    ensures TranslateBucketSimple(bucket, prefix, newPrefix, |bucket.keys|) == TranslateBucket(bucket, prefix, newPrefix)

  predicate {:opaque} WillFitInPkv(mbucket: MutBucket, prefix: Key, newPrefix: Key)
    requires mbucket.Inv()
  {
    && PackedKV.PSA.psaCanAppendSeq(PackedKV.PSA.EmptyPsa(), TranslateBucket(mbucket.I(), prefix, newPrefix).keys)
    && PackedKV.PSA.psaCanAppendSeq(PackedKV.PSA.EmptyPsa(), messageSeq_to_bytestringSeq(TranslateBucket(mbucket.I(), prefix, newPrefix).msgs))
    && var psaKeys := PackedKV.PSA.psaFromSeq(TranslateBucket(mbucket.I(), prefix, newPrefix).keys);
    && var psaMsgs := PackedKV.PSA.psaFromSeq(messageSeq_to_bytestringSeq(TranslateBucket(mbucket.I(), prefix, newPrefix).msgs));
    && PackedKV.WeightPkv(PackedKV.Pkv(psaKeys, psaMsgs)) as nat < Uint32UpperBound()
  }

  predicate TranslateBucketWillFit(bucket: Bucket, prefix: Key, newPrefix: Key)
  requires PreWFBucket(bucket)
  {
    || (|newPrefix| <= |prefix|)
    || (BucketWeights.WeightBucket(bucket) + 1024 * |bucket.keys| < Uint32UpperBound())
  }

  predicate TranslateBucketsWillFit(buckets: seq<Bucket>, prefix: Key, newPrefix: Key)
  requires forall i | 0 <= i < |buckets| :: PreWFBucket(buckets[i])
  {
    (forall i | 0 <= i < |buckets| :: TranslateBucketWillFit(buckets[i], prefix, newPrefix))
  }

  method ComputeTranslateBucketWillFit(shared mbucket: MutBucket, prefix: Key, newPrefix: Key)
  returns (b: bool)
  requires mbucket.Inv()
  ensures b == TranslateBucketWillFit(mbucket.I(), prefix, newPrefix)
  ensures b ==> WillFitInPkv(mbucket, prefix, newPrefix)
  {
    if |newPrefix| <= |prefix| {
      b := true;
    } else {
      // TODO: do different key length calculation based on format of bucket
      var pkv := mbucket.GetPkv();
      var size := PackedKV.NumKVPairs(pkv);

      b := (size * 1024 < 0x1_0000_0000) && ((mbucket.weight + size * 1024) < 0x1_0000_0000);
    }
    TranslateBucketWillFitImpliesWillFitInPkv(mbucket, prefix, newPrefix);
  }

  method ComputeTranslateBucketsWillFit(shared mbuckets: lseq<MutBucket>, prefix: Key, newPrefix: Key)
  returns (b: bool)
  requires MutBucket.InvLseq(mbuckets)
  ensures b == TranslateBucketsWillFit(MutBucket.ILseq(mbuckets), prefix, newPrefix)
  ensures b ==> (forall i | 0 <= i < |mbuckets| :: WillFitInPkv(lseqs(mbuckets)[i], prefix, newPrefix))
  {
    var i := 0;
    b := true;

    while i < lseq_length_as_uint64(mbuckets)
      invariant 0 <= i <= |mbuckets| as uint64
      invariant forall j | 0 <= j < i :: TranslateBucketWillFit(lseqs(mbuckets)[j].I(), prefix, newPrefix)
      invariant forall j | 0 <= j < i :: WillFitInPkv(lseqs(mbuckets)[j], prefix, newPrefix)
    {
      b := ComputeTranslateBucketWillFit(lseq_peek(mbuckets, i), prefix, newPrefix);
      if !b {
        return false;
      }
      i := i + 1;
    }
  }

  function {:opaque} MutBucketToPkv(mbucket: MutBucket) : (pkv: PackedKV.Pkv)
  requires mbucket.Inv()
  requires mbucket.format.BFTree?
  ensures PackedKV.WF(pkv)
  ensures PackedKV.I(pkv) == mbucket.I()
  {
    var b := mbucket.I();
    var tree := mbucket.format.tree;
    var treekeys := LKMB.Model.ToSeq(tree).0;
    var treemsgs := LKMB.Model.ToSeq(tree).1;

    LKMBPKVOps.ToSeqInterpretation(tree);
    LKMB.Model.ToSeqIsStrictlySorted(tree);
    assert Bucket(treekeys, treemsgs).as_map() == b.as_map();
    assert Lexi.IsStrictlySorted(treekeys);
    assert Lexi.IsStrictlySorted(b.keys);

    MapSeqs.SeqsEqOfMapsEq(treekeys, treemsgs, b.keys, b.msgs);
    assert b.keys == treekeys;
    assert b.msgs == treemsgs;

    LKMBPKVOps.WeightImpliesCanAppend(tree);
    assert EncodableMessageSeq(treemsgs);

    var treePsaKeys := PackedKV.PSA.psaFromSeq(treekeys);
    var treePsaMsgs := PackedKV.PSA.psaFromSeq(messageSeq_to_bytestringSeq(treemsgs));
    assert PackedKV.IMessages(treePsaMsgs) == treemsgs;

    var pkv := PackedKV.Pkv(treePsaKeys, treePsaMsgs);
    assert PackedKV.WF(pkv);
    LKMBPKVOps.ToPkvPreservesInterpretation(tree, pkv);

    pkv
  }

  lemma TranslateBucketWillFitImpliesWillFitInPkv(mbucket: MutBucket, prefix: Key, newPrefix: Key)
  requires mbucket.Inv()
  ensures TranslateBucketWillFit(mbucket.I(), prefix, newPrefix) ==> WillFitInPkv(mbucket, prefix, newPrefix)
  {
    var b := mbucket.I();
    var tb := TranslateBucket(b, prefix, newPrefix);
    var idxs := TranslateBucketInternal(b, prefix, newPrefix, 0).idxs;
    assert |tb.keys| == |tb.msgs|; // observe

    var pkv := if mbucket.format.BFPkv? then mbucket.format.pkv else MutBucketToPkv(mbucket);
    assert PackedKV.WF(pkv);
    assert b == PackedKV.I(pkv);
    assert PackedKV.PSA.I(pkv.keys) == b.keys;
    assert PackedKV.PSA.I(pkv.messages) == messageSeq_to_bytestringSeq(b.msgs);

    PackedKV.PSA.psaCanAppendI(pkv.keys);
    PackedKV.PSA.psaCanAppendI(pkv.messages);

    MutBucket.WeightBucketIs(pkv);
    assert PackedKV.I(pkv) == b;
    assert BucketWeights.WeightBucket(b) == PackedKV.WeightPkv(pkv) as int;
    assert PackedKV.WeightPkv(pkv) == mbucket.weight;
    assert PackedKV.WeightPkv(pkv) as nat < Uint32UpperBound();

    assert EncodableMessageSeq(b.msgs);
    assert PackedKV.PSA.psaCanAppendSeq(PackedKV.PSA.EmptyPsa(), b.keys);
    assert PackedKV.PSA.psaCanAppendSeq(PackedKV.PSA.EmptyPsa(), messageSeq_to_bytestringSeq(b.msgs));

    TranslateBucketMessageLt(b, tb, idxs, prefix, newPrefix);
    assert EncodableMessageSeq(tb.msgs);
    assert PackedKV.PSA.psaCanAppendSeq(PackedKV.PSA.EmptyPsa(), messageSeq_to_bytestringSeq(tb.msgs));

    // weight of translated bucket message is <= bucket's message
    var psaMsgs := PackedKV.PSA.psaFromSeq(messageSeq_to_bytestringSeq(tb.msgs));
    assert PackedKV.IMessages(psaMsgs) == tb.msgs;
    assert ValidMessageBytestrings(PackedKV.PSA.I(psaMsgs));
    assert IdentityMessage() !in PackedKV.IMessages(psaMsgs);

    assert |psaMsgs.offsets| <= |pkv.messages.offsets|;
    assert |psaMsgs.data| <= |pkv.messages.data|;
    
    if |newPrefix| <= |prefix| {
      TranslateBucketKeyLt(b, tb, idxs, prefix, newPrefix);
      assert PackedKV.PSA.psaCanAppendSeq(PackedKV.PSA.EmptyPsa(), tb.keys);

      var psaKeys := PackedKV.PSA.psaFromSeq(tb.keys);
      assert |psaKeys.offsets| <= |pkv.keys.offsets|;
      assert |psaKeys.data| <= |pkv.keys.data|;

      var pkv' := PackedKV.Pkv(psaKeys, psaMsgs);
      assert PackedKV.WF(pkv');

      assert PackedKV.WeightPkv(pkv') <= PackedKV.WeightPkv(pkv);
      assert PackedKV.WeightPkv(pkv') as nat < Uint32UpperBound();

      assert WillFitInPkv(mbucket, prefix, newPrefix) by {
        reveal_WillFitInPkv();
      }
    } else if (BucketWeights.WeightBucket(b) + 1024 * |b.keys|) < Uint32UpperBound() {
      FlattenLengthUpperBound(FlattenShape(tb.keys));
      assert PackedKV.PSA.psaCanAppendSeq(PackedKV.PSA.EmptyPsa(), tb.keys);

      var psaKeys := PackedKV.PSA.psaFromSeq(tb.keys);
      assert |psaKeys.offsets| <= |pkv.keys.offsets|;
      assert |psaKeys.data| <= 1024 * |psaKeys.offsets|;

      var pkv' := PackedKV.Pkv(psaKeys, psaMsgs);

      assert PackedKV.PSA.WF(pkv'.keys);
      assert PackedKV.PSA.WF(pkv'.messages);
      assert |pkv'.keys.offsets| == |pkv'.messages.offsets|;
      assert PackedKV.WF(pkv');

      assert PackedKV.WeightPkv(pkv') as nat < Uint32UpperBound();
      assert WillFitInPkv(mbucket, prefix, newPrefix) by {
        reveal_WillFitInPkv();
      }
    }
  }

  lemma FlattenLengthUpperBound(len: seq<nat>)
  requires forall i | 0 <= i < |len| :: len[i] <= 1024
  ensures FlattenLength(len) <= |len| * 1024
  decreases |len|
  {
    reveal_FlattenLength();

    if |len| > 0 {
      FlattenLengthUpperBound(len[1..]);
      FlattenLengthAdditive([len[0]], len[1..]);
      assert [len[0]] + len[1..] == len;
    }
  }

  lemma TranslateBucketKeyLt(bucket: Bucket, bucket': Bucket, idxs: seq<int>, prefix: Key, newPrefix: Key)
  requires WFBucket(bucket)
  requires |newPrefix| <= |prefix|
  requires WFTBucket(bucket, TBucket(bucket', idxs), prefix, newPrefix, 0)
  ensures FlattenLength(FlattenShape(bucket'.keys)) <= FlattenLength(FlattenShape(bucket.keys))
  {
    reveal_WFTBucket();
    var keylen := FlattenShape(bucket.keys);
    var keylen' := FlattenShape(bucket'.keys);

    TranslateBucketFlattenLengthLt(keylen, keylen', idxs);
    if |idxs| > 0 {
      FlattenLengthSubSeq(keylen, idxs[0], |keylen|);
      assert keylen[idxs[0]..] == keylen[idxs[0]..|keylen|];
    }
  }

  lemma TranslateBucketMessageLt(bucket: Bucket, bucket': Bucket, idxs: seq<int>, prefix: Key, newPrefix: Key)
  requires WFBucket(bucket)
  requires WFTBucket(bucket, TBucket(bucket', idxs), prefix, newPrefix, 0)
  ensures EncodableMessageSeq(bucket'.msgs)
  ensures FlattenLength(FlattenShape(messageSeq_to_bytestringSeq(bucket'.msgs)))
     <= FlattenLength(FlattenShape(messageSeq_to_bytestringSeq(bucket.msgs)))
  {
    reveal_WFTBucket();

    var msglen := FlattenShape(messageSeq_to_bytestringSeq(bucket.msgs));
    var msglen' := FlattenShape(messageSeq_to_bytestringSeq(bucket'.msgs));

    TranslateBucketFlattenLengthLt(msglen, msglen', idxs);
    if |idxs| > 0 {
      FlattenLengthSubSeq(msglen, idxs[0], |msglen|);
      assert msglen[idxs[0]..] == msglen[idxs[0]..|msglen|];
    }
  }

  lemma TranslateBucketFlattenLengthLt(len: seq<nat>, len': seq<nat>, idxs: seq<int>)
  requires |idxs| == |len'| <= |len|
  requires forall i | 0 <= i < |idxs| :: 0 <= idxs[i] < |len|
  requires forall i | 0 <= i < |idxs| :: len[idxs[i]] >= len'[i]
  requires forall i, j | 0 <= i < j < |idxs| :: idxs[i] < idxs[j]
  ensures |idxs| > 0 ==> FlattenLength(len') <= FlattenLength(len[idxs[0]..])
  ensures |idxs| == 0 ==> FlattenLength(len') == 0
  decreases |idxs|
  {
    reveal_FlattenLength();

    if |len'| > 0 {
      var i := idxs[0];
      TranslateBucketFlattenLengthLt(len, len'[1..], idxs[1..]);

      FlattenLengthAdditive([len'[0]], len'[1..]);
      FlattenLengthAdditive([len[i]], len[i+1..]);
      assert [len'[0]] + len'[1..] == len';
      assert [len[i]] + len[i+1..] == len[i..];

      if |idxs| > 1{
        FlattenLengthAdditive([len[i]], len[i+1..idxs[1]]);
        FlattenLengthAdditive(len[i..idxs[1]], len[idxs[1]..]);
        assert [len[i]] + len[i+1..idxs[1]] == len[i..idxs[1]];
        assert len[i..idxs[1]] + len[idxs[1]..] == len[i..];
      }
    }
  }

  lemma TranslateBucketSubSeqLeft(bucket: Bucket, bucket': Bucket, idx: int, end: int, prefix: Key, newPrefix: Key)
  requires PreWFBucket(bucket)
  requires PreWFBucket(bucket')
  requires 0 <= idx <= end <= |bucket.keys|
  requires bucket.keys[..end] == bucket'.keys
  requires bucket.msgs[..end] == bucket'.msgs
  ensures
    var tb := TranslateBucketInternal(bucket, prefix, newPrefix, idx).b;
    var tb' := TranslateBucketInternal(bucket', prefix, newPrefix, idx).b;
    && |tb'.keys| <= |tb.keys|
    && tb.keys[..|tb'.keys|] == tb'.keys
    && tb.msgs[..|tb'.msgs|] == tb'.msgs
  decreases |bucket.keys| - idx
  {
    if idx < end {
      assert bucket.keys[idx] == bucket'.keys[idx];
      TranslateBucketSubSeqLeft(bucket, bucket', idx + 1, end, prefix, newPrefix);
    }
  }

  lemma BucketSubSeqWillFitInPkv(bucket: MutBucket, bucket': MutBucket, 
    tbucket: Bucket, tbucket': Bucket, prefix: Key, newPrefix: Key)
  requires bucket.Inv()
  requires bucket'.Inv()
  requires WillFitInPkv(bucket, prefix, newPrefix)
  requires TranslateBucket(bucket.I(), prefix, newPrefix) == tbucket
  requires TranslateBucket(bucket'.I(), prefix, newPrefix) == tbucket'
  requires |tbucket'.keys| <= |tbucket.keys|
  requires tbucket.keys[..|tbucket'.keys|] == tbucket'.keys 
        || tbucket.keys[|tbucket.keys|-|tbucket'.keys|..] == tbucket'.keys
  requires tbucket.msgs[..|tbucket'.msgs|] == tbucket'.msgs 
        || tbucket.msgs[|tbucket.keys|-|tbucket'.keys|..] == tbucket'.msgs
  requires PackedKV.PSA.psaCanAppendSeq(PackedKV.PSA.EmptyPsa(), tbucket'.keys)
  requires PackedKV.PSA.psaCanAppendSeq(PackedKV.PSA.EmptyPsa(), messageSeq_to_bytestringSeq(tbucket'.msgs))
  requires |Flatten(tbucket'.keys)| <= |Flatten(tbucket.keys)|
  requires |Flatten(messageSeq_to_bytestringSeq(tbucket'.msgs))| 
        <= |Flatten(messageSeq_to_bytestringSeq(tbucket.msgs))|
  ensures WillFitInPkv(bucket', prefix, newPrefix)
  {
    var psaKeys := PackedKV.PSA.psaFromSeq(tbucket'.keys);
    var psaMsgs := PackedKV.PSA.psaFromSeq(messageSeq_to_bytestringSeq(tbucket'.msgs));
    assert PackedKV.IMessages(psaMsgs) == tbucket'.msgs;
    assert IdentityMessage() !in tbucket'.msgs; // observe

    assert PackedKV.WF(PackedKV.Pkv(psaKeys, psaMsgs)) by { reveal_WillFitInPkv(); }
    assert WillFitInPkv(bucket', prefix, newPrefix) by { reveal_WillFitInPkv(); }
  }

  lemma SplitLeftWillFitInPkv(bucket: MutBucket, bucket': MutBucket, prefix: Key, newPrefix: Key, pivot: Key)
  requires bucket.Inv()
  requires bucket'.Inv()
  requires bucket'.I() == SplitBucketLeft(bucket.I(), pivot)
  ensures WillFitInPkv(bucket, prefix, newPrefix) ==> WillFitInPkv(bucket', prefix, newPrefix)
  {
    var tb := TranslateBucket(bucket.I(), prefix, newPrefix);
    var tb' := TranslateBucket(bucket'.I(), prefix, newPrefix);

    reveal_SplitBucketLeft();
    var i := Lexi.binarySearchIndexOfFirstKeyGte(bucket.I().keys, pivot);
    TranslateBucketSubSeqLeft(bucket.I(), bucket'.I(), 0, i, prefix, newPrefix);
    assert tb'.keys + tb.keys[|tb'.keys|..] == tb.keys;
    assert tb'.msgs + tb.msgs[|tb'.msgs|..] == tb.msgs;

    FlattenAdditive(tb'.keys,  tb.keys[|tb'.keys|..]);
    messageSeq_to_bytestringSeq_Additive(tb'.msgs, tb.msgs[|tb'.msgs|..]);
    FlattenAdditive(messageSeq_to_bytestringSeq(tb'.msgs), messageSeq_to_bytestringSeq(tb.msgs[|tb'.msgs|..]));

    if WillFitInPkv(bucket, prefix, newPrefix) {
      reveal_WillFitInPkv();
      BucketSubSeqWillFitInPkv(bucket, bucket', tb, tb', prefix, newPrefix);
    }
  }

  lemma TranslateBucketIndexEquiv(bucket: Bucket, bucket': Bucket, idx: int, start: int, prefix: Key, newPrefix: Key)
  requires PreWFBucket(bucket)
  requires PreWFBucket(bucket')
  requires 0 <= start <= idx <= |bucket.keys|
  requires bucket.keys[start..] == bucket'.keys
  requires bucket.msgs[start..] == bucket'.msgs
  ensures TranslateBucketInternal(bucket, prefix, newPrefix, idx).b
    == TranslateBucketInternal(bucket', prefix, newPrefix, idx-start).b
  decreases |bucket.keys| - idx
  {
    if idx < |bucket.keys| {
      assert bucket.keys[idx] == bucket'.keys[idx-start];
      TranslateBucketIndexEquiv(bucket, bucket', idx + 1, start, prefix, newPrefix);
    } 
  }

  lemma TranslateBucketSubSeqRight(bucket: Bucket, bucket': Bucket, idx: int, start: int, prefix: Key, newPrefix: Key)
  requires PreWFBucket(bucket)
  requires PreWFBucket(bucket')
  requires 0 <= idx <= start <= |bucket.keys|
  requires bucket.keys[start..] == bucket'.keys
  requires bucket.msgs[start..] == bucket'.msgs
  ensures
    var tb := TranslateBucketInternal(bucket, prefix, newPrefix, idx).b;
    var tb' := TranslateBucketInternal(bucket', prefix, newPrefix, 0).b; 
    && |tb'.keys| <= |tb.keys|
    && tb.keys[|tb.keys| - |tb'.keys|..] == tb'.keys
    && tb.msgs[|tb.msgs| - |tb'.msgs|..] == tb'.msgs
  decreases |bucket.keys| - idx
  {
    if idx < start {
      TranslateBucketSubSeqRight(bucket, bucket', idx + 1, start, prefix, newPrefix);
    } else {
      TranslateBucketIndexEquiv(bucket, bucket', idx, start, prefix, newPrefix);
    }
  }

  lemma SplitRightWillFitInPkv(bucket: MutBucket, bucket': MutBucket, prefix: Key, newPrefix: Key, pivot: Key)
  requires bucket.Inv()
  requires bucket'.Inv()
  requires bucket'.I() == SplitBucketRight(bucket.I(), pivot)
  ensures WillFitInPkv(bucket, prefix, newPrefix) ==> WillFitInPkv(bucket', prefix, newPrefix)
  {
    var tb := TranslateBucket(bucket.I(), prefix, newPrefix);
    var tb' := TranslateBucket(bucket'.I(), prefix, newPrefix);

    reveal_SplitBucketRight();
    var i := Lexi.binarySearchIndexOfFirstKeyGte(bucket.I().keys, pivot);
    TranslateBucketSubSeqRight(bucket.I(), bucket'.I(), 0, i, prefix, newPrefix);

    assert |tb'.keys| <= |tb.keys|;
    var end := |tb.keys| - |tb'.keys|;
    assert tb.keys[..end] + tb'.keys == tb.keys;
    assert tb.msgs[..end] + tb'.msgs == tb.msgs;

    FlattenAdditive(tb.keys[..end], tb'.keys);
    messageSeq_to_bytestringSeq_Additive(tb.msgs[..end], tb'.msgs);
    FlattenAdditive(messageSeq_to_bytestringSeq(tb.msgs[..end]), messageSeq_to_bytestringSeq(tb'.msgs));

    if WillFitInPkv(bucket, prefix, newPrefix) {
      reveal_WillFitInPkv();
      BucketSubSeqWillFitInPkv(bucket, bucket', tb, tb', prefix, newPrefix);
    }
  }
  
  method {:timeLimitMultiplier 2} ComputeTranslateBucket(shared mbucket: MutBucket, prefix: Key, newPrefix: Key) returns (linear mbucket': MutBucket)
  requires mbucket.Inv()
  requires WillFitInPkv(mbucket, prefix, newPrefix);
  ensures mbucket'.Inv()
  ensures mbucket'.I() == TranslateBucket(mbucket.I(), prefix, newPrefix)
  {
    reveal_WillFitInPkv();
    ghost var bucket := mbucket.I();
    assert EncodableMessageSeq(bucket.msgs);
    reveal_IsPrefix();

    var pkv := mbucket.GetPkv();
    var len := PackedKV.NumKVPairs(pkv);
    linear var result_keys := seq_alloc_init(len, []);
    linear var result_msgs := seq_alloc_init(len, []);
    var result_len := 0;

    var i := 0;
    while i < len
      invariant 0 <= i <= len
      invariant 0 <= result_len <= i
      invariant |result_keys| == len as nat
      invariant |result_msgs| == len as nat
      invariant result_keys[..result_len] == TranslateBucketSimple(bucket, prefix, newPrefix, i as nat).keys
      invariant forall j | 0 <= j < result_len :: |result_msgs[j]| < 0x1_0000_0000
      invariant result_msgs[..result_len] == messageSeq_to_bytestringSeq(TranslateBucketSimple(bucket, prefix, newPrefix, i as nat).msgs)
    {
      var key: seq<byte> := PackedKV.GetKey(pkv, i);
      var msg := PackedKV.PSA.psaElement(pkv.messages, i);
      if |prefix| as uint64 <= |key| as uint64 && prefix == key[..|prefix| as uint64] {
        var k := changePrefix(prefix, newPrefix, key);
        mut_seq_set(inout result_keys, result_len, k);
        mut_seq_set(inout result_msgs, result_len, msg);
        result_len := result_len + 1;
        calc {
          result_keys[..result_len];
          { reveal_TranslateBucketSimple(); }
          TranslateBucketSimple(bucket, prefix, newPrefix, i as nat + 1).keys;
        }
        calc {
          result_msgs[..result_len];
          // result_msgs[..result_len-1] + [result_msgs[result_len-1]];
          // messageSeq_to_bytestringSeq(TranslateBucketSimple(bucket, prefix, newPrefix, i as nat).msgs) + [result_msgs[result_len-1]];
          // messageSeq_to_bytestringSeq(TranslateBucketSimple(bucket, prefix, newPrefix, i as nat).msgs) + [PackedKV.PSA.psaElement(pkv.messages, i)];
          messageSeq_to_bytestringSeq(TranslateBucketSimple(bucket, prefix, newPrefix, i as nat).msgs) + [PackedKV.PSA.I(pkv.messages)[i]];
          // messageSeq_to_bytestringSeq(TranslateBucketSimple(bucket, prefix, newPrefix, i as nat).msgs) + [Message_to_bytestring(bucket.msgs[i])];
          // messageSeq_to_bytestringSeq(TranslateBucketSimple(bucket, prefix, newPrefix, i as nat).msgs) + messageSeq_to_bytestringSeq([bucket.msgs[i]]);
          { messageSeq_to_bytestringSeq_Additive(TranslateBucketSimple(bucket, prefix, newPrefix, i as nat).msgs, [bucket.msgs[i]]); }
          messageSeq_to_bytestringSeq(TranslateBucketSimple(bucket, prefix, newPrefix, i as nat).msgs + [bucket.msgs[i]]);
          { reveal_TranslateBucketSimple(); }
          messageSeq_to_bytestringSeq(TranslateBucketSimple(bucket, prefix, newPrefix, i as nat + 1).msgs);
        }
      } else {
        reveal_TranslateBucketSimple();
      }
      i := i + 1;
    }
 
    var result_keys' := seq_unleash(result_keys);
    var result_msgs' := seq_unleash(result_msgs);

    ghost var tbucket_simple := TranslateBucketSimple(bucket, prefix, newPrefix, i as nat);
    ghost var tbucket := TranslateBucket(bucket, prefix, newPrefix);

    assert i as nat == |bucket.keys|;
    TranslateBucketSimpleEquivalence(bucket, prefix, newPrefix);
    assert tbucket_simple == tbucket;
    assert result_keys'[..result_len] == tbucket_simple.keys;
    assert result_keys'[..result_len] == tbucket.keys;
    assert result_msgs'[..result_len] == messageSeq_to_bytestringSeq(tbucket_simple.msgs);
    assert result_msgs'[..result_len] == messageSeq_to_bytestringSeq(tbucket.msgs);

    var result_keys_psa := PackedKV.PSA.FromSeq(result_keys'[..result_len]);
    var result_msgs_psa := PackedKV.PSA.FromSeq(result_msgs'[..result_len]);
    calc {
      result_keys_psa;
      { PackedKV.PSA.psaCanAppendI(result_keys_psa); }
      PackedKV.PSA.psaFromSeq(result_keys'[..result_len]);
      PackedKV.PSA.psaFromSeq(tbucket.keys);
    }
    calc {
      result_msgs_psa;
      { PackedKV.PSA.psaCanAppendI(result_msgs_psa); }
      PackedKV.PSA.psaFromSeq(result_msgs'[..result_len]);
      PackedKV.PSA.psaFromSeq(messageSeq_to_bytestringSeq(tbucket.msgs));
    }

    ghost var tpkv := PackedKV.Pkv(result_keys_psa, result_msgs_psa);
    assert PackedKV.PSA.psaFromSeq(tbucket.keys) == result_keys_psa;
    assert PackedKV.PSA.psaFromSeq(messageSeq_to_bytestringSeq(tbucket.msgs)) == result_msgs_psa;
    assert PackedKV.WF(tpkv);
    assert PackedKV.I(tpkv) == tbucket;

    mbucket' := MutBucket.AllocPkv(PackedKV.Pkv(result_keys_psa, result_msgs_psa), mbucket.sorted);
  }

  // method ComputeTranslateBuckets(shared blist: lseq<MutBucket>, prefix: Key, newPrefix: Key) returns (linear blist': lseq<MutBucket>)
  // requires MutBucket.InvLseq(blist)
  // requires forall i | 0 <= i < |blist| :: WillFitInPkv(blist[i], prefix, newPrefix)
  // ensures MutBucket.InvLseq(blist')
  // ensures MutBucket.ILseq(blist') == TranslateBuckets(MutBucket.ILseq(blist), prefix, newPrefix)
  // {
  //   ghost var iblist := MutBucket.ILseq(blist);

  //   blist' := lseq_alloc(lseq_length_as_uint64(blist));

  //   var i := 0;
  //   while i < lseq_length_as_uint64(blist)
  //     invariant 0 <= i <= |blist| as uint64
  //     invariant |blist'| == |blist|
  //     invariant forall j | 0 <= j < |blist| as uint64 :: lseq_has(blist')[j] <==> (j < i)
  //     invariant MutBucket.InvSeq(lseqs(blist')[..i])
  //     invariant MutBucket.ISeq(lseqs(blist')[..i]) == TranslateBuckets(iblist[..i], prefix, newPrefix)
  //   {
  //     linear var tmp := ComputeTranslateBucket(lseq_peek(blist, i), prefix, newPrefix);
  //     lseq_give_inout(inout blist', i, tmp);
  //     i := i + 1;

  //     assert lseqs(blist')[..i] == lseqs(blist')[..i-1] + [lseqs(blist')[i-1]];
  //   }
  //   assert lseqs(blist') == lseqs(blist')[..i];
  //   assert iblist == iblist[..i];
  // }

  method ComputeTranslateSingleBucketList(linear bucket: MutBucket, prefix: Key, newPrefix: Key)
  returns (linear blist: lseq<MutBucket>)
  requires bucket.Inv()
  requires WillFitInPkv(bucket, prefix, newPrefix)
  ensures MutBucket.InvLseq(blist)
  ensures MutBucket.ILseq(blist) == TranslateBuckets([bucket.I()], prefix, newPrefix)
  {
    blist := lseq_alloc(1);
    linear var tbucket := ComputeTranslateBucket(bucket, prefix, newPrefix);
    lseq_give_inout(inout blist, 0, tbucket);
    assert MutBucket.ILseq(blist) == TranslateBuckets([bucket.I()], prefix, newPrefix);
    var _ := FreeMutBucket(bucket);
  }

  method ComputeTranslateCutOffKeepRightBuckets(shared blist: lseq<MutBucket>, linear bucket: MutBucket, 
    prefix: Key, newPrefix: Key, cRight: uint64) returns (linear blist': lseq<MutBucket>)
  requires bucket.Inv()
  requires MutBucket.InvLseq(blist)
  requires WillFitInPkv(bucket, prefix, newPrefix)
  requires forall i | 0 <= i < |blist| :: WillFitInPkv(blist[i], prefix, newPrefix)
  requires 0 <= cRight as int < |blist|
  requires |blist| < 0x1_0000_0000_0000_0000
  ensures MutBucket.InvLseq(blist')
  ensures MutBucket.ILseq(blist') == TranslateBuckets([bucket.I()]+ MutBucket.ILseq(blist)[cRight+1..], prefix, newPrefix)
  {
    ghost var iblist := [bucket.I()] + MutBucket.ILseq(blist)[cRight+1..];
    blist' := lseq_alloc(lseq_length_as_uint64(blist)-cRight);

    linear var b := ComputeTranslateBucket(bucket, prefix, newPrefix);
    lseq_give_inout(inout blist', 0, b);
    var _ := FreeMutBucket(bucket);

    var i := 1;
    while i < lseq_length_as_uint64(blist')
      invariant 1 <= i as int <= |blist'|
      invariant |blist'| == |iblist|
      invariant |blist'| + cRight as int == |blist|
      invariant forall j | 0 as int <= j < |blist| :: lseq_has(blist)[j]
      invariant forall j | 0 as int <= j < |blist| :: lseqs(blist)[j].Inv()
      invariant forall j | 1 <= j < |iblist| :: iblist[j] == lseqs(blist)[j+cRight as int].I()
      invariant forall j | 0 <= j < |blist'| :: lseq_has(blist')[j] <==> j < i as int
      invariant forall j | 0 <= j < i :: lseqs(blist')[j].Inv()   
      invariant forall j | 0 <= j < i :: lseqs(blist')[j].I() == TranslateBucket(iblist[j], prefix, newPrefix)
    {
      linear var tmp := ComputeTranslateBucket(lseq_peek(blist, i+cRight), prefix, newPrefix);
      assert lseqs(blist)[i+cRight].I() == iblist[i];
      assert tmp.I() == TranslateBucket(iblist[i], prefix, newPrefix);

      lseq_give_inout(inout blist', i, tmp);
      i := i + 1;
    }
  }

  method ComputeTranslateCutOffNodeBuckets(shared blist: lseq<MutBucket>, linear left: MutBucket, linear right: MutBucket,
    prefix: Key, newPrefix: Key, cLeft: uint64, cRight: uint64) returns (linear blist': lseq<MutBucket>)
  requires left.Inv()
  requires right.Inv()
  requires MutBucket.InvLseq(blist)
  requires 0 <= cRight as int < cLeft as int < |blist|
  requires WillFitInPkv(left, prefix, newPrefix)
  requires WillFitInPkv(right, prefix, newPrefix)
  requires forall i | cRight as int+1 <= i < cLeft as int :: WillFitInPkv(blist[i], prefix, newPrefix)
  requires |blist| < 0x1_0000_0000_0000_0000
  ensures MutBucket.InvLseq(blist')
  ensures MutBucket.ILseq(blist') == 
    TranslateBuckets([left.I()]+ MutBucket.ILseq(blist)[cRight+1..cLeft] + [right.I()], prefix, newPrefix) 
  {
    ghost var iblist := [left.I()] + MutBucket.ILseq(blist)[cRight+1..cLeft] + [right.I()];
    blist' := lseq_alloc(cLeft-cRight+1);

    linear var b1 := ComputeTranslateBucket(left, prefix, newPrefix);
    lseq_give_inout(inout blist', 0, b1);
    var _ := FreeMutBucket(left);

    var i := 1;
    while i < lseq_length_as_uint64(blist')-1
      invariant 1 <= i as int < |blist'|
      invariant |blist'| == |iblist|
      invariant |blist'| == cLeft as int - cRight as int +1
      invariant forall j | 0 as int <= j < |blist| :: lseq_has(blist)[j]
      invariant forall j | 0 as int <= j < |blist| :: lseqs(blist)[j].Inv()
      invariant forall j | 1 <= j < |iblist|-1 :: iblist[j] == lseqs(blist)[j+cRight as int].I()
      invariant forall j | 0 <= j < |blist'| :: lseq_has(blist')[j] <==> j < i as int
      invariant forall j | 0 <= j < i :: lseqs(blist')[j].Inv()   
      invariant forall j | 0 <= j < i :: lseqs(blist')[j].I() == TranslateBucket(iblist[j], prefix, newPrefix)
    {
      linear var tmp := ComputeTranslateBucket(lseq_peek(blist, i+cRight), prefix, newPrefix);
      assert tmp.I() == TranslateBucket(iblist[i], prefix, newPrefix);

      lseq_give_inout(inout blist', i, tmp);
      i := i + 1;
    }

    linear var b2 := ComputeTranslateBucket(right, prefix, newPrefix);
    lseq_give_inout(inout blist', i, b2);
    var _ := FreeMutBucket(right);
  }

  method ComputeParentKeysInChildRange(parentpivots: PivotTable, parentedges: EdgeTable, childpivots: PivotTable, slot: uint64)
  returns (b: bool)
  requires WFPivots(parentpivots)
  requires WFPivots(childpivots)
  requires WFEdges(parentedges, parentpivots)
  requires 0 <= slot as int < |parentedges|
  requires |parentpivots| < Uint64UpperBound()
  requires |childpivots| < 0x4000_0000_0000_0000
  ensures b == ParentKeysInChildRange(parentpivots, parentedges, childpivots, slot as int)
  {
    Keyspace.reveal_IsStrictlySorted();
    if parentedges[slot].None? {
      b := ComputeContainsRange(childpivots, parentpivots[slot], parentpivots[slot+1]);
    } else {
      var prefix := ComputePivotLcp(parentpivots[slot], parentpivots[slot + 1]);
      var newPrefix := parentedges[slot].value;
      var left, right := ComputeTranslatePivotPair(parentpivots[slot].e, parentpivots[slot + 1], prefix, newPrefix);
      b := ComputeContainsRange(childpivots, Keyspace.Element(left), right);
    }
  }
}
