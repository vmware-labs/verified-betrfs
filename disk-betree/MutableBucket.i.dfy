include "../lib/tttree.i.dfy"
include "KVList.i.dfy"
include "KVListPartialFlush.i.dfy"
include "Bounds.i.dfy"

module MutableBucket {
  import TTT = TwoThreeTree
  import KVList
  import KVListPartialFlush
  import opened ValueMessage`Internal
  import opened Lexicographic_Byte_Order
  import opened Sequences
  import opened Options
  import opened Maps
  import opened BucketsLib
  import opened Bounds
  import opened BucketWeights
  import opened NativeTypes
  import Native
  import Pivots = PivotsLib

  type Key = Element
  type Kvl = KVList.Kvl
  type TreeMap = TTT.Tree<Message>

  method tree_to_kvl(tree: TreeMap)
  returns (kvl : Kvl)
  requires TTT.TTTree(tree)
  ensures KVList.WF(kvl)
  ensures KVList.I(kvl) == TTT.I(tree)
  {
    assume false;
    var s := TTT.AsSeq(tree);
    kvl := KVList.KvlOfSeq(s, TTT.I(tree));
  }

  method kvl_to_tree(kvl : Kvl)
  returns (tree: TreeMap)
  requires KVList.WF(kvl)
  ensures TTT.TTTree(tree)
  ensures KVList.I(kvl) == TTT.I(tree)
  {
    assume false;
    if (|kvl.keys| as uint64 == 0) {
      return TTT.EmptyTree;
    }

    var ar := new (Key, TTT.Node)[|kvl.keys| as uint64];
    var j := 0;
    while j < |kvl.keys| as uint64 {
      ar[j] := (kvl.keys[j], TTT.Leaf(kvl.keys[j], kvl.values[j]));
      j := j + 1;
    }
    var len := |kvl.keys| as uint64;
    while len > 1 {
      var k := 0;
      var newlen := 0;
      while k < len - 4 {
        ar[newlen] := (ar[k].0, TTT.ThreeNode(ar[k].1, ar[k+1].0, ar[k+1].1, ar[k+2].0, ar[k+2].1));
        k := k + 3;
        newlen := newlen + 1;
      }
      if (k == len - 4) {
        ar[newlen] := (ar[k].0, TTT.TwoNode(ar[k].1, ar[k+1].0, ar[k+1].1));
        newlen := newlen + 1;
        ar[newlen] := (ar[k+2].0, TTT.TwoNode(ar[k+2].1, ar[k+3].0, ar[k+3].1));
        newlen := newlen + 1;
      } else if (k == len - 3) {
        ar[newlen] := (ar[k].0, TTT.ThreeNode(ar[k].1, ar[k+1].0, ar[k+1].1, ar[k+2].0, ar[k+2].1));
        newlen := newlen + 1;
      } else {
        ar[newlen] := (ar[k].0, TTT.TwoNode(ar[k].1, ar[k+1].0, ar[k+1].1));
        newlen := newlen + 1;
      }
      len := newlen;
    }
    tree := TTT.NonEmptyTree(ar[0].1);
  }

  class MutBucket {
    var is_tree: bool;

    var tree: TreeMap;
    var kvl: Kvl;

    var Weight: uint64;

    ghost var Repr: set<object>;
    ghost var Bucket: map<Key, Message>;

    protected predicate Inv()
    reads this, Repr
    ensures Inv() ==> this in Repr
    ensures Inv() ==> Weight as int == WeightBucket(Bucket)
    ensures Inv() ==> WFBucket(Bucket)
    {
      && Repr == {this}
      && (!is_tree ==> (
        && KVList.WF(kvl)
        && Weight as int == WeightBucket(KVList.I(kvl))
        && Bucket == KVList.I(kvl)
      ))
      && (is_tree ==> (
        && TTT.TTTree(tree)
        && Weight as int == WeightBucket(TTT.I(tree))
        && Bucket == TTT.I(tree)
      ))
      && WFBucket(Bucket)
    }

    constructor(kv: Kvl)
    requires KVList.WF(kv)
    requires WeightBucket(KVList.I(kv)) < 0x1_0000_0000_0000_0000
    ensures Bucket == KVList.I(kv)
    ensures Inv()
    ensures fresh(Repr)
    {
      this.is_tree := false;
      this.kvl := kv;
      this.Repr := {this};
      var w := KVList.computeWeightKvl(kv);
      this.Weight := w;
      this.Bucket := KVList.I(kv);
      KVList.WFImpliesWFBucket(kv);
    }

    method GetKvl() returns (kv: Kvl)
    requires Inv()
    ensures KVList.WF(kv)
    ensures KVList.I(kv) == Bucket
    {
      if (is_tree) {
        kv := tree_to_kvl(tree);
      } else {
        kv := kvl;
      }
    }

    static function {:opaque} ReprSeq(s: seq<MutBucket>) : set<object>
    reads s
    {
      set i, o | 0 <= i < |s| && o in s[i].Repr :: o
    }

    static predicate {:opaque} InvSeq(s: seq<MutBucket>)
    reads s
    reads ReprSeq(s)
    // Yes this is dumb, to opaque the function and then specify it here anyway,
    // but this keeps the reveal_ReprSeq() from escaping
    ensures InvSeq(s) == (forall i | 0 <= i < |s| :: s[i].Inv())
    {
      reveal_ReprSeq();
      forall i | 0 <= i < |s| :: s[i].Inv()
    }

    static function I(s: MutBucket) : Bucket
    reads s
    {
      s.Bucket
    }

    static protected function ISeq(s: seq<MutBucket>) : (bs : seq<Bucket>)
    reads s
    reads ReprSeq(s)
    ensures |bs| == |s|
    ensures forall i | 0 <= i < |s| :: bs[i] == s[i].Bucket
    decreases |s|
    {
      reveal_ReprSeq();
      if |s| == 0 then [] else ISeq(DropLast(s)) + [I(Last(s))]
    }

    static lemma ISeqInduction(s: seq<MutBucket>)
    requires |s| > 0
    ensures ISeq(s) == ISeq(DropLast(s)) + [I(Last(s))]

    static predicate {:opaque} ReprSeqDisjoint(buckets: seq<MutBucket>)
    reads set i | 0 <= i < |buckets| :: buckets[i]
    {
      forall i, j | 0 <= i < |buckets| && 0 <= j < |buckets| && i != j ::
          buckets[i].Repr !! buckets[j].Repr
    }

    static lemma ReprSeqDisjointOfLen1(buckets: seq<MutBucket>)
    requires |buckets| <= 1
    ensures ReprSeqDisjoint(buckets)
    {
      reveal_ReprSeqDisjoint();
    }

    static lemma ReprSeqDisjointOfLen2(buckets: seq<MutBucket>)
    requires |buckets| == 2
    requires buckets[0].Repr !! buckets[1].Repr
    ensures ReprSeqDisjoint(buckets)
    {
      reveal_ReprSeqDisjoint();
    }

    static lemma ListReprOfLen1(buckets: seq<MutBucket>)
    requires |buckets| == 1
    ensures ReprSeq(buckets) == buckets[0].Repr
    {
      reveal_ReprSeq();
    }

    static lemma ListReprOfLen2(buckets: seq<MutBucket>)
    requires |buckets| == 2
    ensures ReprSeq(buckets) == buckets[0].Repr + buckets[1].Repr
    {
      reveal_ReprSeq();
    }

    static lemma LemmaReprBucketLeReprSeq(buckets: seq<MutBucket>, i: int)
    requires 0 <= i < |buckets|
    ensures buckets[i].Repr <= ReprSeq(buckets)

    static method kvlSeqToMutBucketSeq(kvls: seq<Kvl>)
    returns (buckets : seq<MutBucket>)
    requires |kvls| < 0x1_0000_0000_0000_0000
    {
      assume false;
      var ar := new MutBucket?[|kvls| as uint64];
      var j: uint64 := 0;
      while j < |kvls| as uint64
      {
        ar[j] := new MutBucket(kvls[j]);
        j := j + 1;
      }
      return ar[..];
    }

    static method mutBucketSeqToKvlSeq(buckets: seq<MutBucket>)
    returns (kvls : seq<Kvl>)
    requires |buckets| < 0x1_0000_0000_0000_0000
    {
      assume false;
      var ar := new Kvl[|buckets| as uint64];
      var j: uint64 := 0;
      while j < |buckets| as uint64
      {
        ar[j] := buckets[j].GetKvl();
        j := j + 1;
      }
      return ar[..];
    }

    static method PartialFlush(parent: MutBucket, children: seq<MutBucket>, pivots: seq<Key>)
    returns (newParent: MutBucket, newChildren: seq<MutBucket>)
    requires parent.Inv()
    requires InvSeq(children)
    requires WFBucketList(ISeq(children), pivots)
    requires WeightBucket(I(parent)) <= MaxTotalBucketWeight() as int
    requires WeightBucketList(ISeq(children)) <= MaxTotalBucketWeight() as int
    ensures newParent.Inv()
    ensures InvSeq(newChildren)
    ensures fresh(newParent.Repr)
    ensures fresh(ReprSeq(newChildren))
    ensures newParent.Repr !! ReprSeq(newChildren)
    ensures ReprSeqDisjoint(newChildren)
    ensures KVListPartialFlush.bucketPartialFlush(parent.Bucket, ISeq(children), pivots)
        == (newParent.Bucket, ISeq(newChildren))
    {
      assume false;
      var kvlParent := parent.GetKvl();
      var kvlChildren := mutBucketSeqToKvlSeq(children);
      var kvlNewParent, kvlNewChildren := KVListPartialFlush.PartialFlush(kvlParent, kvlChildren, pivots);
      newParent := new MutBucket(kvlNewParent);
      newChildren := kvlSeqToMutBucketSeq(kvlNewChildren);
    }

    method Insert(key: Key, value: Message)
    requires Inv()
    requires Weight as int + WeightKey(key) + WeightMessage(value) < 0x1_0000_0000_0000_0000
    modifies Repr
    ensures Inv()
    ensures Bucket == BucketInsert(old(Bucket), key, value)
    ensures forall o | o in Repr :: o in old(Repr) || fresh(o)
    {
      if !is_tree {
        is_tree := true;
        tree := kvl_to_tree(kvl);
        kvl := KVList.Kvl([], []); // not strictly necessary, but frees memory
      }

      assume false;

      if value.Define? {
        // TODO reduce this to just one lookup
        var cur := TTT.Query(tree, key);
        tree := TTT.Insert(tree, key, value);
        if (cur.ValueForKey?) {
          Weight := Weight - WeightMessageUint64(cur.value) + WeightMessageUint64(value) as uint64;
        } else {
          Weight := Weight + WeightKeyUint64(key) + WeightMessageUint64(value);
        }
      }

      Bucket := TTT.I(tree);
    }

    method Query(key: Key)
    returns (m: Option<Message>)
    requires Inv()
    ensures m.None? ==> key !in Bucket
    ensures m.Some? ==> key in Bucket && Bucket[key] == m.value
    {
      if is_tree {
        var res := TTT.Query(tree, key);
        if res.ValueForKey? {
          m := Some(res.value);
        } else {
          m := None;
        }
      } else {
        KVList.lenKeysLeWeightOver8(kvl);
        m := KVList.Query(kvl, key);
      }
    }

    method SplitLeft(pivot: Key)
    returns (left: MutBucket)
    requires Inv()
    ensures left.Inv()
    ensures left.Bucket == SplitBucketLeft(Bucket, pivot)
    ensures fresh(left.Repr)
    {
      var kv;
      if is_tree {
        kv := tree_to_kvl(tree);
      } else {
        kv := kvl;
      }

      KVList.splitLeftCorrect(kv, pivot);
      WeightSplitBucketLeft(Bucket, pivot);
      KVList.lenKeysLeWeightOver8(kv);
      var kvlLeft := KVList.SplitLeft(kv, pivot);
      left := new MutBucket(kvlLeft);
    }

    method SplitRight(pivot: Key)
    returns (right: MutBucket)
    requires Inv()
    ensures right.Inv()
    ensures right.Bucket == SplitBucketRight(Bucket, pivot)
    ensures fresh(right.Repr)
    {
      var kv;
      if is_tree {
        kv := tree_to_kvl(tree);
      } else {
        kv := kvl;
      }

      KVList.splitRightCorrect(kv, pivot);
      WeightSplitBucketRight(Bucket, pivot);
      KVList.lenKeysLeWeightOver8(kv);
      var kvlRight := KVList.SplitRight(kv, pivot);
      right := new MutBucket(kvlRight);
    }

    method SplitLeftRight(pivot: Key)
    returns (left: MutBucket, right: MutBucket)
    requires Inv()
    ensures left.Inv()
    ensures right.Inv()
    ensures left.Bucket == SplitBucketLeft(Bucket, pivot)
    ensures right.Bucket == SplitBucketRight(Bucket, pivot)
    ensures fresh(left.Repr)
    ensures fresh(right.Repr)
    ensures left.Repr !! right.Repr
    {
      left := SplitLeft(pivot);
      right := SplitRight(pivot);
    }

    static method SplitOneInList(buckets: seq<MutBucket>, slot: uint64, pivot: Key)
    returns (buckets' : seq<MutBucket>)
    requires InvSeq(buckets)
    requires 0 <= slot as int < |buckets|
    ensures InvSeq(buckets')
    ensures ReprSeqDisjoint(buckets')
    ensures ISeq(buckets') == old(SplitBucketInList(ISeq(buckets), slot as int, pivot))
    ensures forall o | o in ReprSeq(buckets') :: o in old(ReprSeq(buckets)) || fresh(o)
    {
      assume false;
      var l, r := buckets[slot].SplitLeftRight(pivot);
      buckets' := replace1with2(buckets, l, r, slot as int);
    }

    static method computeWeightOfSeq(buckets: seq<MutBucket>)
    returns (weight: uint64)
    requires forall i | 0 <= i < |buckets| :: buckets[i].Inv()
    requires WeightBucketList(ISeq(buckets)) < 0x1_0000_0000_0000_0000
    ensures weight as int == WeightBucketList(old(ISeq(buckets)))
    {
      assume false;
      var w := 0;
      var j: uint64 := 0;
      while j < |buckets| as uint64
      {
        w := w + buckets[j].Weight;
        j := j + 1;
      }
      return w;
    }

    static lemma Islice(buckets: seq<MutBucket>, a: int, b: int)
    requires 0 <= a <= b <= |buckets|
    requires forall i | 0 <= i < |buckets| :: buckets[i].Inv()
    ensures forall i | 0 <= i < |buckets[a..b]| :: buckets[a..b][i].Inv()
    ensures ISeq(buckets[a..b]) == ISeq(buckets)[a..b]
    {
      if b == |buckets| {
        if (a == b) {
        } else {
          Islice(DropLast(buckets), a, b - 1);
        }
      } else {
        Islice(DropLast(buckets), a, b);
      }
    }

    static lemma Isuffix(buckets: seq<MutBucket>, a: int)
    requires 0 <= a <= |buckets|
    requires forall i | 0 <= i < |buckets| :: buckets[i].Inv()
    ensures forall i | 0 <= i < |buckets[a..]| :: buckets[a..][i].Inv()
    ensures ISeq(buckets[a..]) == ISeq(buckets)[a..]
    {
      Islice(buckets, a, |buckets|);
    }

    method Clone() returns (bucket': MutBucket)
    requires Inv()
    ensures bucket'.Inv()
    ensures fresh(bucket'.Repr)
    ensures this.Bucket == bucket'.Bucket
    {
      var kv;
      if is_tree {
        kv := tree_to_kvl(tree);
      } else {
        kv := kvl;
      }
      bucket' := new MutBucket(kv);
    }

    static method CloneSeq(buckets: seq<MutBucket>) returns (buckets': seq<MutBucket>)
    requires InvSeq(buckets)
    ensures InvSeq(buckets')
    ensures fresh(ReprSeq(buckets'))
    ensures |buckets'| == |buckets|
    ensures ISeq(buckets) == ISeq(buckets')
    ensures ReprSeqDisjoint(buckets')
    {
      assume false;
      var ar := new MutBucket?[|buckets| as uint64];
      var j: uint64 := 0;
      while j < |buckets| as uint64
      {
        ar[j] := buckets[j].Clone();
        j := j + 1;
      }
      buckets' := ar[..];
    }
  }
}
