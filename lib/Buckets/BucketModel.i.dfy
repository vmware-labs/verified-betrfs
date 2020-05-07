include "BucketsLib.i.dfy"
include "PivotsLib.i.dfy"
include "BucketWeights.i.dfy"
include "../Base/Message.i.dfy"
include "../Base/Maps.s.dfy"
include "../Base/total_order.i.dfy"
include "../../MapSpec/UI.s.dfy"
include "../../MapSpec/MapSpec.s.dfy"
include "../../PivotBetree/Bounds.i.dfy"

module BucketModel {
  import opened BucketsLib
  import opened BucketWeights
  import opened PivotsLib
  import opened Lexicographic_Byte_Order
  import Keyspace = Lexicographic_Byte_Order
  import opened ValueMessage
  import opened Maps
  import opened Sequences
  import opened KeyType
  import opened Options
  import UI
  import MS = MapSpec
  import opened Bounds
  import opened NativeTypes
  
  datatype singleMergeResult =
    | MergeCompleted(
        keys: seq<Key>,
        msgs: seq<Message>,
        slack: nat)
    | SlackExhausted(
        keys: seq<Key>,
        msgs: seq<Message>,
        end: nat,
        slack: nat)
  {
    function bucketMap() : BucketMap
    requires |this.keys| == |this.msgs|
    {
      BucketMapOfSeq(this.keys, this.msgs)
    }

    function flushedKeys(
      top_keys: seq<Key>,
      top_msgs: seq<Message>,
      from: nat,
      to: nat) : set<Key>
    requires 0 <= from <= to <= |top_keys| == |top_msgs|
    requires this.SlackExhausted? ==> from <= this.end <= |top_keys|
    {
      if this.MergeCompleted? then
        set key | key in top_keys[from..to]
      else
        set key | key in top_keys[from..this.end]
    }

    function flushedMap(
      top_keys: seq<Key>,
      top_msgs: seq<Message>,
      from: nat,
      to: nat) : BucketMap
    requires 0 <= from <= to <= |top_keys| == |top_msgs|
    requires this.SlackExhausted? ==> from <= this.end <= |top_keys|
    {
      var top := BucketMapOfSeq(
            top_keys[from..to], top_msgs[from..to]);
      map key | key in top
        && key in this.flushedKeys(top_keys, top_msgs, from, to)
        :: top[key]
    }
  }

  function mergeToOneChild(
      top_keys: seq<Key>,
      top_msgs: seq<Message>,
      from: nat,
      to: nat,
      bot_keys: seq<Key>,
      bot_msgs: seq<Message>,
      bot_from: nat,
      acc_keys: seq<Key>,
      acc_msgs: seq<Message>,
      slack: nat
    ) : (result: singleMergeResult)
  requires |top_keys| == |top_msgs|
  requires |bot_keys| == |bot_msgs|
  requires |acc_keys| == |acc_msgs|
  requires from <= to <= |top_keys|
  requires bot_from <= |bot_keys|
  decreases |top_keys| + |bot_keys| - from - bot_from
  ensures |result.keys| == |result.msgs|
  ensures result.SlackExhausted? ==> from <= result.end <= |top_keys|
  {
    if from == to then
      MergeCompleted(
        acc_keys + bot_keys[bot_from..],
        acc_msgs + bot_msgs[bot_from..],
        slack)
    else if |bot_keys| == bot_from then
      MergeCompleted(
        acc_keys + top_keys[from..to],
        acc_msgs + top_msgs[from..to],
        slack)
    else if top_keys[from] == bot_keys[bot_from] then
      var key := top_keys[from];
      var topmsg := top_msgs[from];
      var botmsg := bot_msgs[bot_from];
      var msg := ValueMessage.Merge(topmsg, botmsg);
      if msg == IdentityMessage() then
        mergeToOneChild(
            top_keys, top_msgs, from+1, to,
            bot_keys, bot_msgs, bot_from+1,
            acc_keys, acc_msgs,
            slack + WeightKey(key) + WeightMessage(botmsg))
      else (
        var delta := WeightMessage(msg) - WeightMessage(botmsg);
        if delta > slack then
          SlackExhausted(acc_keys+bot_keys[bot_from..], acc_msgs+bot_msgs[bot_from..], from, slack)
        else
          mergeToOneChild(
              top_keys, top_msgs, from+1, to,
              bot_keys, bot_msgs, bot_from+1,
              acc_keys + [key], acc_msgs + [msg],
              slack - delta)
      )
    else if Keyspace.lt(top_keys[from], bot_keys[bot_from]) then
      var key := top_keys[from];
      var msg := top_msgs[from];
      var delta := WeightKey(key) + WeightMessage(msg);
      if delta > slack then
        SlackExhausted(acc_keys+bot_keys[bot_from..], acc_msgs+bot_msgs[bot_from..], from, slack)
      else
        mergeToOneChild(
            top_keys, top_msgs, from+1, to,
            bot_keys, bot_msgs, bot_from,
            acc_keys + [key], acc_msgs + [msg],
            slack - delta)
    else
      var key := bot_keys[bot_from];
      var msg := bot_msgs[bot_from];
      mergeToOneChild(
          top_keys, top_msgs, from, to,
          bot_keys, bot_msgs, bot_from+1,
          acc_keys + [key], acc_msgs + [msg],
          slack)
  }

  datatype partialFlushResult = partialFlushResult(
    newParent: Bucket,
    newChildren: seq<Bucket>,
    flushedKeys: set<Key>)

  /*function {:opaque} partialFlush(parent: Bucket, children: seq<Bucket>, pivots: seq<Key>) : (res: partialFlushResult)
    requires WFBucket(parent)
    requires PivotsLib.WFPivots(pivots)
    requires |pivots| + 1 == |children|
    requires WeightBucketList(children) <= MaxTotalBucketWeight()
    requires forall i | 0 <= i < |children| :: WFBucket(children[i])
    requires BucketWellMarshalled(parent)
    requires BucketListWellMarshalled(children)
    ensures WFBucket(res.newParent)
    ensures (forall i | 0 <= i < |res.newChildren| :: WFBucket(res.newChildren[i]))
    ensures res.newParent == BucketComplement(parent, res.flushedKeys)
    ensures res.newChildren == BucketListFlush(BucketIntersect(parent, res.flushedKeys), children, pivots)
    ensures WeightBucket(res.newParent) <= WeightBucket(parent)
    ensures WeightBucketList(res.newChildren) <= MaxTotalBucketWeight()
  {
    assume false;
    partialFlushResult(parent, [], {}) // FIXME
  }*/

  function topBotAccMergeForKey(
    top: BucketMap,
    bot: BucketMap,
    acc: BucketMap,
    key: Key) : Message
  {
    var topmsg := if key in top then top[key] else IdentityMessage();
    var botmsg := if key in acc then acc[key] else
        if key in bot then bot[key] else IdentityMessage();
    ValueMessage.Merge(topmsg, botmsg)
  }

  function topBotAccMerge(
    top: BucketMap,
    bot: BucketMap,
    acc: BucketMap) : BucketMap
  {
    map key | key in top.Keys + bot.Keys + acc.Keys
      && topBotAccMergeForKey(top, bot, acc, key) != IdentityMessage()
      :: topBotAccMergeForKey(top, bot, acc, key)
  }

  lemma BucketMapOfSeqPushBack(
      keys: seq<Key>, msgs: seq<Message>, key: Key, msg: Message)
  requires |keys| == |msgs|
  requires IsStrictlySorted(keys)
  requires forall k | k in keys :: Keyspace.lt(k, key)
  ensures BucketMapOfSeq(keys + [key], msgs + [msg])
       == BucketMapOfSeq(keys, msgs)[key := msg]
  ensures key !in BucketMapOfSeq(keys, msgs)
  {
    reveal_BucketMapOfSeq();
    if key in BucketMapOfSeq(keys, msgs) {
      var i := BucketMapOfSeqGetIndex(keys, msgs, key);
      assert Keyspace.lt(keys[i], key);
    }
  }

  lemma BucketMapOfSeqPopFront(
      keys: seq<Key>, msgs: seq<Message>, i: int)
  requires |keys| == |msgs|
  requires 0 <= i < |keys|
  requires IsStrictlySorted(keys)
  ensures BucketMapOfSeq(keys[i+1..], msgs[i+1..])[keys[i] := msgs[i]]
       == BucketMapOfSeq(keys[i..], msgs[i..])
  ensures keys[i] !in BucketMapOfSeq(keys[i+1..], msgs[i+1..])
  {
    var a := BucketMapOfSeq(keys[i+1..], msgs[i+1..])[keys[i] := msgs[i]];
    var b := BucketMapOfSeq(keys[i..], msgs[i..]);
    forall k | k in a
    ensures k in b
    ensures a[k] == b[k]
    {
      reveal_IsStrictlySorted();
      if k == keys[i] {
        BucketMapOfSeqMapsIndex(keys[i..], msgs[i..], 0);
        assert a[k] == b[k];
      } else {
        var j := BucketMapOfSeqGetIndex(keys[i+1..], msgs[i+1..], k);
        BucketMapOfSeqMapsIndex(keys[i..], msgs[i..], j+1);
        assert a[k] == b[k];
      }
    }
    forall k | k in b
    ensures k in a
    {
    }
    reveal_IsStrictlySorted();
  }

  lemma flushedMapPopFront(res: singleMergeResult,
    top_keys: seq<Key>, top_msgs: seq<Message>, from: int, to: int)
  requires |top_keys| == |top_msgs|
  requires 0 <= from < to <= |top_keys|
  requires res.SlackExhausted? ==> from+1 <= res.end <= |top_keys|
  requires IsStrictlySorted(top_keys)
  ensures res.flushedMap(top_keys, top_msgs, from, to)
      == res.flushedMap(top_keys, top_msgs, from+1, to)
              [top_keys[from] := top_msgs[from]]
  ensures top_keys[from] !in res.flushedMap(top_keys, top_msgs, from+1, to)
  {
    var a := BucketMapOfSeq(top_keys[from+1..to], top_msgs[from+1..to])[top_keys[from] := top_msgs[from]];
    var b := BucketMapOfSeq(top_keys[from..to], top_msgs[from..to]);
    forall k | k in a
    ensures k in b
    ensures a[k] == b[k]
    {
      reveal_IsStrictlySorted();
      if k == top_keys[from] {
        BucketMapOfSeqMapsIndex(top_keys[from..to], top_msgs[from..to], 0);
        assert a[k] == b[k];
      } else {
        var j := BucketMapOfSeqGetIndex(top_keys[from+1..to], top_msgs[from+1..to], k);
        BucketMapOfSeqMapsIndex(top_keys[from..to], top_msgs[from..to], j+1);
        assert a[k] == b[k];
      }
    }
    forall k | k in b
    ensures k in a
    {
    }
    assert BucketMapOfSeq(top_keys[from+1..to], top_msgs[from+1..to])[top_keys[from] := top_msgs[from]]
        ==  BucketMapOfSeq(top_keys[from..to], top_msgs[from..to]);
    reveal_IsStrictlySorted();
  }

  predicate seq_lt(a: seq<Key>, b: seq<Key>, start: int)
  requires 0 <= start <= |b|
  {
    forall i, j | 0 <= i < |a| && start <= j < |b| ::
      Keyspace.lt(a[i], b[j])
  }

  lemma topBotAccMerge_concat_lists(
      acc_keys: seq<Key>, acc_msgs: seq<Message>,
      bot_keys: seq<Key>, bot_msgs: seq<Message>,
      from: int)
  requires |acc_keys| == |acc_msgs|
  requires |bot_keys| == |bot_msgs|
  requires 0 <= from <= |bot_keys|
  requires IsStrictlySorted(acc_keys)
  requires IsStrictlySorted(bot_keys)
  requires forall i | 0 <= i < |acc_msgs| :: acc_msgs[i] != IdentityMessage()
  requires forall i | 0 <= i < |bot_msgs| :: bot_msgs[i] != IdentityMessage()
  requires seq_lt(acc_keys, bot_keys, from)
  ensures
    topBotAccMerge(map[],
      BucketMapOfSeq(bot_keys[from..], bot_msgs[from..]),
      BucketMapOfSeq(acc_keys, acc_msgs))
    == BucketMapOfSeq(acc_keys + bot_keys[from..], acc_msgs + bot_msgs[from..])
  {
    var x := 
      topBotAccMerge(map[],
        BucketMapOfSeq(bot_keys[from..], bot_msgs[from..]),
        BucketMapOfSeq(acc_keys, acc_msgs));
    var y := BucketMapOfSeq(acc_keys + bot_keys[from..], acc_msgs + bot_msgs[from..]);
    forall k: Key | k in y
    ensures k in x
    ensures x[k] == y[k]
    {
      reveal_IsStrictlySorted();
      var i := BucketMapOfSeqGetIndex(acc_keys + bot_keys[from..], acc_msgs + bot_msgs[from..], k);
      if i < |acc_keys| {
        BucketMapOfSeqMapsIndex(acc_keys, acc_msgs, i);
        assert k !in BucketMapOfSeq(bot_keys[from..], bot_msgs[from..]);
      } else {
        BucketMapOfSeqMapsIndex(bot_keys[from..], bot_msgs[from..], i - |acc_keys|);
        assert k !in BucketMapOfSeq(acc_keys, acc_msgs);
      }
    }
    forall k | k in x
    ensures k in y
    {
    }
  }

  lemma mergeToOneOneChild_eq_topBotAccMerge(
      top_keys: seq<Key>,
      top_msgs: seq<Message>,
      from: nat,
      to: nat,
      bot_keys: seq<Key>,
      bot_msgs: seq<Message>,
      bot_from: nat,
      acc_keys: seq<Key>,
      acc_msgs: seq<Message>,
      slack: nat)
  requires |top_keys| == |top_msgs|
  requires |bot_keys| == |bot_msgs|
  requires |acc_keys| == |acc_msgs|
  requires from <= to <= |top_keys|
  requires bot_from <= |bot_keys|
  requires IsStrictlySorted(acc_keys)
  requires IsStrictlySorted(top_keys)
  requires IsStrictlySorted(bot_keys)
  requires seq_lt(acc_keys, top_keys, from)
  requires seq_lt(acc_keys, bot_keys, bot_from)
  requires forall i | 0 <= i < |bot_msgs| :: bot_msgs[i] != IdentityMessage()
  requires forall i | 0 <= i < |top_msgs| :: top_msgs[i] != IdentityMessage()
  requires forall i | 0 <= i < |acc_msgs| :: acc_msgs[i] != IdentityMessage()
  decreases |top_keys| + |bot_keys| - from - bot_from
  ensures
      var res := mergeToOneChild(
            top_keys, top_msgs, from, to,
            bot_keys, bot_msgs, bot_from,
            acc_keys, acc_msgs, slack);
      var top := BucketMapOfSeq(
            top_keys[from..to], top_msgs[from..to]);
      var bot := BucketMapOfSeq(
            bot_keys[bot_from..], bot_msgs[bot_from..]);
      var acc := BucketMapOfSeq(acc_keys, acc_msgs);
      res.bucketMap() == topBotAccMerge(
        res.flushedMap(top_keys, top_msgs, from, to),
        bot, acc)
  {
    var res := mergeToOneChild(
          top_keys, top_msgs, from, to,
          bot_keys, bot_msgs, bot_from,
          acc_keys, acc_msgs, slack);
    var top := BucketMapOfSeq(
          top_keys[from..to], top_msgs[from..to]);
    var bot := BucketMapOfSeq(
          bot_keys[bot_from..], bot_msgs[bot_from..]);
    var acc := BucketMapOfSeq(acc_keys, acc_msgs);

    assert IsStrictlySorted(bot_keys[bot_from..]) by { reveal_IsStrictlySorted(); }
    assert IsStrictlySorted(top_keys[from..to]) by { reveal_IsStrictlySorted(); }

    if from == to {
      var a := res.bucketMap();
      var b := topBotAccMerge(
        res.flushedMap(top_keys, top_msgs, from, to),
        bot, acc);
      forall k | k in a
      ensures k in b
      ensures a[k] == b[k]
      {
        var i := BucketMapOfSeqGetIndex(res.keys, res.msgs, k);
        if i < |acc_keys| {
          BucketMapOfSeqMapsIndex(acc_keys, acc_msgs, i);
        } else {
          BucketMapOfSeqMapsIndex(bot_keys[bot_from..],
              bot_msgs[bot_from..], i-|acc_keys|);
        }
      }
      forall k | k in b
      ensures k in a
      {
      }
      assert a == b;
    } else if |bot_keys| == bot_from {
      var a := res.bucketMap();
      var b := topBotAccMerge(
        res.flushedMap(top_keys, top_msgs, from, to),
        bot, acc);
      forall k | k in a
      ensures k in b
      ensures a[k] == b[k]
      {
        var i := BucketMapOfSeqGetIndex(res.keys, res.msgs, k);
        if i < |acc_keys| {
          BucketMapOfSeqMapsIndex(acc_keys, acc_msgs, i);
          /*assert acc_msgs[i] != IdentityMessage();
          assert k !in bot;
          assert k !in top;
          assert k !in res.flushedMap(top_keys, top_msgs, from, to);
          assert k in acc;
          assert k in acc.Keys;
          assert topBotAccMergeForKey(
            res.flushedMap(top_keys, top_msgs, from, to),
            bot, acc, k)
              == acc_msgs[i];
          assert topBotAccMergeForKey(
            res.flushedMap(top_keys, top_msgs, from, to),
            bot, acc, k) != IdentityMessage();*/
          assert k in b;
        } else {
          BucketMapOfSeqMapsIndex(top_keys[from..to], top_msgs[from..to], i - |acc_keys|);
          assert k in res.flushedMap(top_keys, top_msgs, from, to);
          assert k in b;
        }
      }
      forall k | k in b
      ensures k in a
      {
      }
      assert a == b;
    } else if top_keys[from] == bot_keys[bot_from] {
      var key := top_keys[from];
      var topmsg := top_msgs[from];
      var botmsg := bot_msgs[bot_from];
      var msg := ValueMessage.Merge(topmsg, botmsg);
      if msg == IdentityMessage() {
        calc {
          res.bucketMap();
          {
            mergeToOneOneChild_eq_topBotAccMerge(
                top_keys, top_msgs, from+1, to,
                bot_keys, bot_msgs, bot_from+1,
                acc_keys, acc_msgs,
                slack + WeightKey(key) + WeightMessage(botmsg));
          }
          topBotAccMerge(
            res.flushedMap(top_keys, top_msgs, from+1, to),
            BucketMapOfSeq(bot_keys[bot_from+1..], bot_msgs[bot_from+1..]),
            BucketMapOfSeq(acc_keys, acc_msgs));
          {
            flushedMapPopFront(res, top_keys, top_msgs, from, to);
            assert res.flushedMap(top_keys, top_msgs, from, to)
                == res.flushedMap(top_keys, top_msgs, from+1, to)[key := topmsg];
            BucketMapOfSeqPopFront(bot_keys, bot_msgs, bot_from);
            assert BucketMapOfSeq(bot_keys[bot_from..], bot_msgs[bot_from..])
                == BucketMapOfSeq(bot_keys[bot_from+1..], bot_msgs[bot_from+1..])[key := botmsg];
            assert key !in acc;
            assert key !in BucketMapOfSeq(bot_keys[bot_from+1..], bot_msgs[bot_from+1..]);
            assert key !in res.flushedMap(top_keys, top_msgs, from+1, to);
          }
          topBotAccMerge(
            res.flushedMap(top_keys, top_msgs, from, to),
            bot, acc);
        }
      } else {
        var delta := WeightMessage(msg) - WeightMessage(botmsg);
        if delta > slack {
          calc {
            res.bucketMap();
            {
              assert res.flushedMap(top_keys, top_msgs, from, to)
                  == map[];
              topBotAccMerge_concat_lists(acc_keys, acc_msgs, bot_keys, bot_msgs, bot_from);
            }
            topBotAccMerge(
              res.flushedMap(top_keys, top_msgs, from, to),
              bot, acc);
          }
        } else {
          calc {
            res.bucketMap();
            {
              reveal_IsStrictlySorted();
              mergeToOneOneChild_eq_topBotAccMerge(
                  top_keys, top_msgs, from+1, to,
                  bot_keys, bot_msgs, bot_from+1,
                  acc_keys + [key], acc_msgs + [msg],
                  slack - delta);
            }
            topBotAccMerge(
              res.flushedMap(top_keys, top_msgs, from+1, to),
              BucketMapOfSeq(
                  bot_keys[bot_from+1..], bot_msgs[bot_from+1..]),
              BucketMapOfSeq(acc_keys + [key], acc_msgs + [msg])
            );
            {
              BucketMapOfSeqPushBack(acc_keys, acc_msgs, key, msg);
              flushedMapPopFront(res, top_keys, top_msgs, from, to);
              BucketMapOfSeqPopFront(bot_keys, bot_msgs, bot_from);
            }
            topBotAccMerge(
              res.flushedMap(top_keys, top_msgs, from, to),
              bot, acc);
          }
        }
      }
    } else if Keyspace.lt(top_keys[from], bot_keys[bot_from]) {
      var key := top_keys[from];
      var msg := top_msgs[from];
      var delta := WeightKey(key) + WeightMessage(msg);
      if delta > slack {
        calc {
          res.bucketMap();
          {
            assert res.flushedMap(top_keys, top_msgs, from, to)
                == map[];
            topBotAccMerge_concat_lists(acc_keys, acc_msgs, bot_keys, bot_msgs, bot_from);
          }
          topBotAccMerge(
            res.flushedMap(top_keys, top_msgs, from, to),
            bot, acc);
        }
      } else {
        calc {
          res.bucketMap();
          {
            //StrictlySortedAugment(acc_keys, key);
            reveal_IsStrictlySorted();
            mergeToOneOneChild_eq_topBotAccMerge(
                top_keys, top_msgs, from+1, to,
                bot_keys, bot_msgs, bot_from,
                acc_keys + [key], acc_msgs + [msg],
                slack - delta);
          }
          topBotAccMerge(
            res.flushedMap(top_keys, top_msgs, from+1, to),
            bot, BucketMapOfSeq(acc_keys + [key], acc_msgs + [msg]));
          {
            BucketMapOfSeqPushBack(acc_keys, acc_msgs, key, msg);
            flushedMapPopFront(res, top_keys, top_msgs, from, to);
          }
          topBotAccMerge(
            res.flushedMap(top_keys, top_msgs, from, to),
            bot, acc);
        }
      }
    } else {
      var key := bot_keys[bot_from];
      var msg := bot_msgs[bot_from];

      calc {
        res.bucketMap();
        {
          reveal_IsStrictlySorted();
          mergeToOneOneChild_eq_topBotAccMerge(
              top_keys, top_msgs, from, to,
              bot_keys, bot_msgs, bot_from+1,
              acc_keys + [key], acc_msgs + [msg],
              slack);
        }
        topBotAccMerge(
          res.flushedMap(top_keys, top_msgs, from, to),
          BucketMapOfSeq(
              bot_keys[bot_from+1..], bot_msgs[bot_from+1..]),
          BucketMapOfSeq(acc_keys + [key], acc_msgs + [msg]));
        {
          BucketMapOfSeqPopFront(bot_keys, bot_msgs, bot_from);
          BucketMapOfSeqPushBack(acc_keys, acc_msgs, key, msg);
        }
        topBotAccMerge(
          res.flushedMap(top_keys, top_msgs, from, to),
          bot,
          acc);
      }
    }
  }

  function bucketStartIdx(top_keys: seq<Key>, pivots: PivotTable, r: int) : int
  requires 0 <= r <= |pivots|
  {
    if r == 0 then 0 else binarySearchIndexOfFirstKeyGte(top_keys, pivots[r-1])
  }

  function bucketEndIdx(top_keys: seq<Key>, pivots: PivotTable, r: int) : int
  requires 0 <= r <= |pivots|
  {
    if r < |pivots| then binarySearchIndexOfFirstKeyGte(top_keys, pivots[r]) else |top_keys|
  }

  lemma mergeToOneOneChild_eq_BucketList(
      top_keys: seq<Key>,
      top_msgs: seq<Message>,
      from: nat,
      to: nat,
      bot_keys: seq<Key>,
      bot_msgs: seq<Message>,
      slack: nat,
      pivots: PivotTable,
      r: int)
  requires |top_keys| == |top_msgs|
  requires |bot_keys| == |bot_msgs|
  requires from <= to <= |top_keys|
  requires 0 <= r <= |pivots|
  requires from == bucketStartIdx(top_keys, pivots, r)
  requires to == bucketStartIdx(top_keys, pivots, r)
  requires IsStrictlySorted(top_keys)
  requires IsStrictlySorted(bot_keys)
  requires forall i | 0 <= i < |bot_msgs| :: bot_msgs[i] != IdentityMessage()
  requires forall i | 0 <= i < |top_msgs| :: top_msgs[i] != IdentityMessage()
  requires WFPivots(pivots)
  requires forall i | 0 <= i < |bot_keys| :: Route(pivots, bot_keys[i]) == r
  ensures
      var res := mergeToOneChild(
            top_keys, top_msgs, from, to,
            bot_keys, bot_msgs, 0,
            [], [], slack);
      var top := BucketMapOfSeq(top_keys, top_msgs);
      var bot := BucketMapOfSeq(bot_keys, bot_msgs);
      BucketListItemFlush(
          BucketIntersect(B(top), res.flushedKeys(top_keys, top_msgs, from, to)),
          B(bot), pivots, r).b
        == res.bucketMap()
  {

    var res := mergeToOneChild(
          top_keys, top_msgs, from, to,
          bot_keys, bot_msgs, 0,
          [], [], slack);
    var top := BucketMapOfSeq(top_keys, top_msgs);
    var bot := BucketMapOfSeq(bot_keys, bot_msgs);

    var itop := BucketIntersect(B(top), res.flushedKeys(top_keys, top_msgs, from, to));

    calc {
      BucketListItemFlush(itop, B(bot), pivots, r).b;
      {
        var a := BucketListItemFlush(itop, B(bot), pivots, r).b;
        var b := topBotAccMerge(itop.b, bot, map[]);
        forall k | k in a
        ensures k in b
        ensures a[k] == b[k]
        {
        }
        forall k | k in b
        ensures k in a
        {
          reveal_BucketIntersect();
          RouteIs(pivots, k, r);
        }
      }
      topBotAccMerge(itop.b, bot, map[]);
      topBotAccMerge(
        itop.b,
        BucketMapOfSeq(bot_keys, bot_msgs),
        map[]);
      {
        reveal_BucketIntersect();
        assert itop.b == res.flushedMap(top_keys, top_msgs, from, to);
      }
      topBotAccMerge(
        res.flushedMap(top_keys, top_msgs, from, to),
        BucketMapOfSeq(bot_keys, bot_msgs),
        map[]);
      topBotAccMerge(
        res.flushedMap(top_keys, top_msgs, from, to),
        BucketMapOfSeq(bot_keys, bot_msgs),
        BucketMapOfSeq([], []));
      {
        mergeToOneOneChild_eq_topBotAccMerge(
          top_keys, top_msgs, from, to, bot_keys, bot_msgs, 0,
          [], [], slack);
      }
      res.bucketMap();
    }
  }

  function pivotIndexes(top_keys: seq<Key>, pivots: seq<Key>) : (res: seq<int>)
  ensures |res| == |pivots|
  ensures forall i | 0 <= i < |res| :: res[i]
      == binarySearchIndexOfFirstKeyGte(top_keys, pivots[i])
  {
    if |pivots| == 0 then (
      []
    ) else (
      pivotIndexes(top_keys, DropLast(pivots)) +
        [binarySearchIndexOfFirstKeyGte(top_keys, Last(pivots))]
    )
  }

  datatype mergeResult = mergeResult(
    top: Bucket,
    bots: seq<Bucket>,
    slack: nat)

  function mergeToChildrenIter(
      top: Bucket,
      pivots: seq<Key>,
      bots: seq<Bucket>,
      idxs: seq<int>,
      tmp: singleMergeResult,
      i: int,
      results: seq<Bucket>) : (res : mergeResult)
  requires WFBucket(top)
  requires forall i | 0 <= i < |bots| :: WFBucket(bots[i])
  requires 0 < |bots| == |pivots| + 1
  requires |results| == i
  requires |idxs| == |pivots|
  requires 0 <= i <= |bots|
  requires forall i | 0 <= i < |idxs| :: 0 <= idxs[i] <= |top.keys|
  requires tmp.SlackExhausted? ==> 0 <= tmp.end <= |top.keys|
  decreases |bots| - i
  ensures |res.bots| == |bots|
  {
    if i == |bots| then (
      if tmp.SlackExhausted? then (
        var leftover_top := B(BucketMapOfSeq(top.keys[tmp.end..], top.msgs[tmp.end..]));
        mergeResult(leftover_top, results, tmp.slack)
      ) else (
        mergeResult(B(map[]), results, tmp.slack)
      )
    ) else (
      if tmp.MergeCompleted? then (
        var from := if i == 0 then 0 else idxs[i-1];
        var to1 := if i == |idxs| then |top.keys| else idxs[i];
        var to := if to1 < from then from else to1;
        var tmp' := mergeToOneChild(
            top.keys, top.msgs, from, to,
            bots[i].keys, bots[i].msgs, 0,
            [], [], tmp.slack);
        var results' := results + [B(tmp'.bucketMap())];
        mergeToChildrenIter(top, pivots, bots, idxs, tmp', i+1, results')
      ) else (
        var results' := results + [bots[i]];
        mergeToChildrenIter(top, pivots, bots, idxs, tmp, i+1, results')
      )
    )
  }
 
  function mergeToChildren(
      top: Bucket,
      pivots: seq<Key>,
      bots: seq<Bucket>,
      slack: nat) : (result: mergeResult)
  requires WFBucket(top)
  requires forall i | 0 <= i < |bots| :: WFBucket(bots[i])
  requires 0 < |bots| == |pivots| + 1
  {
    var idxs := pivotIndexes(top.keys, pivots);
    var tmp := MergeCompleted([], [], slack);
    mergeToChildrenIter(top, pivots, bots, idxs, tmp, 0, [])
  }

}
