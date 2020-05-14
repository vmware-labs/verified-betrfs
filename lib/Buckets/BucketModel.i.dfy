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
        ghost keys: seq<Key>,
        ghost msgs: seq<Message>,
        ghost slack: nat)
    | SlackExhausted(
        ghost keys: seq<Key>,
        ghost msgs: seq<Message>,
        ghost end: nat,
        ghost slack: nat)
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

  function {:opaque} mergeToOneChild(
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
  ensures result.SlackExhausted? ==> from <= result.end <= to
  {
    if from == to then
      MergeCompleted(
        acc_keys + bot_keys[bot_from..],
        acc_msgs + bot_msgs[bot_from..],
        slack)
    //else if |bot_keys| == bot_from then
    //  MergeCompleted(
    //    acc_keys + top_keys[from..to],
    //    acc_msgs + top_msgs[from..to],
    //    slack)
    else if bot_from < |bot_keys| &&
        top_keys[from] == bot_keys[bot_from] then
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
    else if bot_from == |bot_keys| ||
        Keyspace.lt(top_keys[from], bot_keys[bot_from]) then
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
      && IsStrictlySorted(res.keys)
      && res.bucketMap() == topBotAccMerge(
        res.flushedMap(top_keys, top_msgs, from, to),
        bot, acc)
  {
    reveal_mergeToOneChild();
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
      assert IsStrictlySorted(res.keys) by {
        reveal_IsStrictlySorted();
      }
    /*} else if |bot_keys| == bot_from {
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
    */
    } else if bot_from < |bot_keys| && top_keys[from] == bot_keys[bot_from] {
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
          assert IsStrictlySorted(res.keys) by {
            reveal_IsStrictlySorted();
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
          assert IsStrictlySorted(res.keys) by {
            reveal_IsStrictlySorted();
            mergeToOneOneChild_eq_topBotAccMerge(
                top_keys, top_msgs, from+1, to,
                bot_keys, bot_msgs, bot_from+1,
                acc_keys + [key], acc_msgs + [msg],
                slack - delta);
          }
        }
      }
    } else if bot_from == |bot_keys| || Keyspace.lt(top_keys[from], bot_keys[bot_from]) {
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
        assert IsStrictlySorted(res.keys) by {
          reveal_IsStrictlySorted();
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
        assert IsStrictlySorted(res.keys) by {
          reveal_IsStrictlySorted();
          mergeToOneOneChild_eq_topBotAccMerge(
              top_keys, top_msgs, from+1, to,
              bot_keys, bot_msgs, bot_from,
              acc_keys + [key], acc_msgs + [msg],
              slack - delta);
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
      assert IsStrictlySorted(res.keys) by {
        reveal_IsStrictlySorted();
        mergeToOneOneChild_eq_topBotAccMerge(
            top_keys, top_msgs, from, to,
            bot_keys, bot_msgs, bot_from+1,
            acc_keys + [key], acc_msgs + [msg],
            slack);
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
  requires to == bucketEndIdx(top_keys, pivots, r)
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
      && IsStrictlySorted(res.keys)
      && BucketListItemFlush(
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
        var x := itop.b;
        var y := res.flushedMap(top_keys, top_msgs, from, to);
        forall k | k in x
        ensures k in y
        ensures x[k] == y[k]
        {
          var i := BucketMapOfSeqGetIndex(
              top_keys[from..to], top_msgs[from..to], k);
          BucketMapOfSeqMapsIndex(top_keys, top_msgs, from+i);
        }
        forall k | k in y
        ensures k in x
        {
        }
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

    assert IsStrictlySorted(res.keys) by {
      mergeToOneOneChild_eq_topBotAccMerge(
        top_keys, top_msgs, from, to, bot_keys, bot_msgs, 0,
        [], [], slack);
    }
  }

  lemma bots_weight_pop_back(bot_keys: seq<Key>, bot_msgs: seq<Message>, i: int)
  requires 0 <= i < |bot_keys| == |bot_msgs|
  ensures WeightKeyList(bot_keys[i..]) == WeightKeyList(bot_keys[i+1..]) + WeightKey(bot_keys[i])
  ensures WeightMessageList(bot_msgs[i..]) == WeightMessageList(bot_msgs[i+1..]) + WeightMessage(bot_msgs[i])
  {
    WeightKeyListPushFront(bot_keys[i], bot_keys[i+1..]);
    assert [bot_keys[i]] + bot_keys[i+1..] == bot_keys[i..];
    WeightMessageListPushFront(bot_msgs[i], bot_msgs[i+1..]);
    assert [bot_msgs[i]] + bot_msgs[i+1..] == bot_msgs[i..];
  }

  lemma mergeToOneChildSlack(
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
    )
  requires |top_keys| == |top_msgs|
  requires |bot_keys| == |bot_msgs|
  requires |acc_keys| == |acc_msgs|
  requires from <= to <= |top_keys|
  requires bot_from <= |bot_keys|
  requires (forall i | 0 <= i < |bot_msgs| :: bot_msgs[i] != IdentityMessage())
  requires (forall i | 0 <= i < |top_msgs| :: top_msgs[i] != IdentityMessage())
  requires (forall i | 0 <= i < |acc_msgs| :: acc_msgs[i] != IdentityMessage())
  ensures
    var res := mergeToOneChild(
          top_keys, top_msgs, from, to,
          bot_keys, bot_msgs, bot_from,
          acc_keys, acc_msgs, slack);
    && (forall i | 0 <= i < |res.msgs| :: res.msgs[i] != IdentityMessage())
    && WeightKeyList(res.keys) + WeightMessageList(res.msgs) + res.slack
      == WeightKeyList(acc_keys) + WeightMessageList(acc_msgs)
       + WeightKeyList(bot_keys[bot_from..]) + WeightMessageList(bot_msgs[bot_from..])
       + slack
  decreases |top_keys| + |bot_keys| - from - bot_from
  {
    reveal_mergeToOneChild();

    WeightKeyListAdditive(acc_keys, bot_keys[bot_from..]);
    WeightMessageListAdditive(acc_msgs, bot_msgs[bot_from..]);

    if from == to {
    } else if bot_from < |bot_keys| &&
        top_keys[from] == bot_keys[bot_from] {
      bots_weight_pop_back(bot_keys, bot_msgs, bot_from);

      var key := top_keys[from];
      var topmsg := top_msgs[from];
      var botmsg := bot_msgs[bot_from];
      var msg := ValueMessage.Merge(topmsg, botmsg);
      if msg == IdentityMessage() {
        mergeToOneChildSlack(
            top_keys, top_msgs, from+1, to,
            bot_keys, bot_msgs, bot_from+1,
            acc_keys, acc_msgs,
            slack + WeightKey(key) + WeightMessage(botmsg));
      } else {
        var delta := WeightMessage(msg) - WeightMessage(botmsg);
        if delta > slack {
        } else {
          WeightKeyListPushBack(acc_keys, key);
          WeightMessageListPushBack(acc_msgs, msg);
          mergeToOneChildSlack(
              top_keys, top_msgs, from+1, to,
              bot_keys, bot_msgs, bot_from+1,
              acc_keys + [key], acc_msgs + [msg],
              slack - delta);
        }
      }
    } else if bot_from == |bot_keys| ||
        Keyspace.lt(top_keys[from], bot_keys[bot_from]) {
      var key := top_keys[from];
      var msg := top_msgs[from];
      var delta := WeightKey(key) + WeightMessage(msg);
      if delta > slack {
      } else {
        WeightKeyListPushBack(acc_keys, key);
        WeightMessageListPushBack(acc_msgs, msg);
        mergeToOneChildSlack(
            top_keys, top_msgs, from+1, to,
            bot_keys, bot_msgs, bot_from,
            acc_keys + [key], acc_msgs + [msg],
            slack - delta);
      }
    } else {
      var key := bot_keys[bot_from];
      var msg := bot_msgs[bot_from];

      bots_weight_pop_back(bot_keys, bot_msgs, bot_from);

      WeightKeyListPushBack(acc_keys, key);
      WeightMessageListPushBack(acc_msgs, msg);

      mergeToOneChildSlack(
          top_keys, top_msgs, from, to,
          bot_keys, bot_msgs, bot_from+1,
          acc_keys + [key], acc_msgs + [msg],
          slack);
    }
  }

  lemma mergeToOneChildPreservesSorted(
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
    )
  requires |top_keys| == |top_msgs|
  requires |bot_keys| == |bot_msgs|
  requires |acc_keys| == |acc_msgs|
  requires from <= to <= |top_keys|
  requires bot_from <= |bot_keys|
  requires IsStrictlySorted(top_keys)
  requires IsStrictlySorted(bot_keys)
  requires IsStrictlySorted(acc_keys)
  requires seq_lt(acc_keys, bot_keys, bot_from)
  requires seq_lt(acc_keys, top_keys, from)
  ensures
    var res := mergeToOneChild(
          top_keys, top_msgs, from, to,
          bot_keys, bot_msgs, bot_from,
          acc_keys, acc_msgs, slack);
    && IsStrictlySorted(res.keys)
  decreases |top_keys| + |bot_keys| - from - bot_from
  {
    reveal_mergeToOneChild();
    reveal_IsStrictlySorted();

    if from == to {
    } else if bot_from < |bot_keys| &&
        top_keys[from] == bot_keys[bot_from] {
      bots_weight_pop_back(bot_keys, bot_msgs, bot_from);

      var key := top_keys[from];
      var topmsg := top_msgs[from];
      var botmsg := bot_msgs[bot_from];
      var msg := ValueMessage.Merge(topmsg, botmsg);
      if msg == IdentityMessage() {
        mergeToOneChildPreservesSorted(
            top_keys, top_msgs, from+1, to,
            bot_keys, bot_msgs, bot_from+1,
            acc_keys, acc_msgs,
            slack + WeightKey(key) + WeightMessage(botmsg));
      } else {
        var delta := WeightMessage(msg) - WeightMessage(botmsg);
        if delta > slack {
        } else {
          mergeToOneChildPreservesSorted(
              top_keys, top_msgs, from+1, to,
              bot_keys, bot_msgs, bot_from+1,
              acc_keys + [key], acc_msgs + [msg],
              slack - delta);
        }
      }
    } else if bot_from == |bot_keys| ||
        Keyspace.lt(top_keys[from], bot_keys[bot_from]) {
      var key := top_keys[from];
      var msg := top_msgs[from];
      var delta := WeightKey(key) + WeightMessage(msg);
      if delta > slack {
      } else {
        mergeToOneChildPreservesSorted(
            top_keys, top_msgs, from+1, to,
            bot_keys, bot_msgs, bot_from,
            acc_keys + [key], acc_msgs + [msg],
            slack - delta);
      }
    } else {
      var key := bot_keys[bot_from];
      var msg := bot_msgs[bot_from];

      mergeToOneChildPreservesSorted(
          top_keys, top_msgs, from, to,
          bot_keys, bot_msgs, bot_from+1,
          acc_keys + [key], acc_msgs + [msg],
          slack);
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
    ghost top: Bucket,
    ghost bots: seq<Bucket>,
    ghost slack: nat)

  function mergeToChildrenIter(
      top: Bucket,
      bots: seq<Bucket>,
      idxs: seq<int>,
      tmp: singleMergeResult,
      i: int,
      results: seq<Bucket>) : (res : mergeResult)
  requires WFBucket(top)
  requires forall i | 0 <= i < |bots| :: WFBucket(bots[i])
  requires 0 < |bots|
  requires |results| == i
  requires 0 <= i <= |bots|
  requires |idxs| == |bots| - 1
  requires forall i | 0 <= i < |idxs| :: 0 <= idxs[i] <= |top.keys|
  requires tmp.SlackExhausted? ==> 0 <= tmp.end <= |top.keys|
  decreases |bots| - i
  ensures |res.bots| == |bots|
  {
    if i == |bots| then (
      if tmp.SlackExhausted? then (
        var leftover_top := BucketOfSeq(top.keys[tmp.end..], top.msgs[tmp.end..]);
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
        var results' := results + [BucketOfSeq(tmp'.keys, tmp'.msgs)];
        mergeToChildrenIter(top, bots, idxs, tmp', i+1, results')
      ) else (
        var results' := results + [bots[i]];
        mergeToChildrenIter(top, bots, idxs, tmp, i+1, results')
      )
    )
  }
 
  function {:opaque} mergeToChildren(
      top: Bucket,
      pivots: seq<Key>,
      bots: seq<Bucket>,
      slack: nat) : (result: mergeResult)
  requires WFBucket(top)
  requires forall i | 0 <= i < |bots| :: WFBucket(bots[i])
  requires 0 < |bots| == |pivots| + 1
  ensures |result.bots| == |bots|
  {
    var idxs := pivotIndexes(top.keys, pivots);
    var tmp := MergeCompleted([], [], slack);
    mergeToChildrenIter(top, bots, idxs, tmp, 0, [])
  }

  function getFlushedKeys(tmp: singleMergeResult, top: Bucket) : set<Key>
  requires tmp.SlackExhausted? ==> tmp.end <= |top.keys|
  {
    if tmp.SlackExhausted? then (
      set i | 0 <= i < tmp.end :: top.keys[i]
    ) else (
      set i | 0 <= i < |top.keys| :: top.keys[i]
    )
  }

  lemma BucketMapOfSeqKeysComplement(top: Bucket, tmp: singleMergeResult)
  requires tmp.SlackExhausted?
  requires WFBucket(top)
  requires |top.keys| == |top.msgs|
  requires 0 <= tmp.end <= |top.keys|
  requires IsStrictlySorted(top.keys)
  requires BucketMapOfSeq(top.keys, top.msgs) == top.b
  ensures BucketComplement(top, getFlushedKeys(tmp, top))
      == BucketOfSeq(top.keys[tmp.end..], top.msgs[tmp.end..])
  {
    reveal_BucketComplement();
    reveal_IsStrictlySorted();

    var a := BucketComplement(top, getFlushedKeys(tmp, top));
    var b := BucketMapOfSeq(top.keys[tmp.end..], top.msgs[tmp.end..]);
    forall k | k in a.b
    ensures k in b
    ensures a.b[k] == b[k]
    {
      assert k in top.b;
      var i := BucketMapOfSeqGetIndex(top.keys, top.msgs, k);
      assert i >= tmp.end;
      BucketMapOfSeqMapsIndex(top.keys[tmp.end..],
          top.msgs[tmp.end..], i - tmp.end);
    }
    forall k | k in b
    ensures k in a.b
    {
    }
    assert a.b == b;

    WFBucketComplement(top, getFlushedKeys(tmp, top));
    WellMarshalledBucketsEq(BucketComplement(top, getFlushedKeys(tmp, top)),
      BucketOfSeq(top.keys[tmp.end..], top.msgs[tmp.end..]));
  }

  lemma all_msgs_not_eq_identity(bucket: Bucket)
  requires WFBucket(bucket)
  requires IsStrictlySorted(bucket.keys)
  ensures forall i | 0 <= i < |bucket.msgs| ::
      bucket.msgs[i] != IdentityMessage()
  {
    forall i | 0 <= i < |bucket.msgs|
    ensures bucket.msgs[i] != IdentityMessage()
    {
      BucketMapOfSeqMapsIndex(bucket.keys, bucket.msgs, i);
    }
  }

  lemma BucketListItemFlush_eq(top: Bucket, keys1: set<Key>, keys2: set<Key>, bot: Bucket, pivots: seq<Key>, i: int)
  requires 0 <= i <= |pivots|
  requires WFBucket(top)
  requires WFBucket(bot)
  requires WFPivots(pivots)
  requires forall k | Route(pivots, k) == i && k in keys1 :: k in keys2
  requires forall k | Route(pivots, k) == i && k in keys2 :: k in keys1
  ensures BucketListItemFlush(BucketIntersect(top, keys1), bot, pivots, i)
       == BucketListItemFlush(BucketIntersect(top, keys2), bot, pivots, i)
  {
    reveal_BucketIntersect();
  }

  lemma mergeToChildrenIterCorrect(
      top: Bucket,
      pivots: seq<Key>,
      bots: seq<Bucket>,
      idxs: seq<int>,
      tmp: singleMergeResult,
      i: int,
      results: seq<Bucket>)
  returns (flushedKeys: set<Key>)
  requires WFBucket(top)
  requires forall i | 0 <= i < |bots| :: WFBucket(bots[i])
  requires 0 < |bots| == |pivots| + 1
  requires |results| == i
  requires |idxs| == |pivots|
  requires 0 <= i <= |bots|
  requires forall i | 0 <= i < |idxs| ::
    idxs[i] == binarySearchIndexOfFirstKeyGte(top.keys, pivots[i])
  requires tmp.SlackExhausted? ==> 0 <= tmp.end <= |top.keys|
  requires IsStrictlySorted(top.keys)
  requires forall i | 0 <= i < |bots| :: IsStrictlySorted(bots[i].keys)
  requires WFPivots(pivots)
  requires WFBucketListProper(bots, pivots)
  requires i <= |pivots| ==> tmp.SlackExhausted? ==> tmp.end <= bucketStartIdx(top.keys, pivots, i)
  requires forall r | 0 <= r < i :: results[r] ==
      BucketListItemFlush(BucketIntersect(top, getFlushedKeys(tmp, top)), bots[r], pivots, r)

  decreases |bots| - i

  ensures var res :=
    mergeToChildrenIter(top, bots, idxs, tmp, i, results);
    && res.top == BucketComplement(top, flushedKeys)
    && forall r | 0 <= r < |res.bots| :: res.bots[r] ==
      BucketListItemFlush(BucketIntersect(top, flushedKeys), bots[r], pivots, r)
  {
    if i == |bots| {
      flushedKeys := getFlushedKeys(tmp, top);
      if tmp.SlackExhausted? {
        var leftover_top := BucketOfSeq(top.keys[tmp.end..], top.msgs[tmp.end..]);
        var res := mergeResult(leftover_top, results, tmp.slack);
        assert res.top == BucketComplement(top, flushedKeys) by {
          BucketMapOfSeqKeysComplement(top, tmp);
        }
      } else {
        var res := mergeResult(B(map[]), results, tmp.slack);
        calc {
          res.top;
          B(map[]);
          {
            reveal_BucketComplement();
            assert forall key | key in top.b :: key in flushedKeys;
            assert BucketComplement(top, flushedKeys).b
                == map[];
          }
          BucketComplement(top, flushedKeys);
        }
      }
    } else {
      if tmp.MergeCompleted? {
        var from := if i == 0 then 0 else idxs[i-1];
        var to1 := if i == |idxs| then |top.keys| else idxs[i];

        assert from == bucketStartIdx(top.keys, pivots, i);
        assert to1 == bucketEndIdx(top.keys, pivots, i);
        assert from <= to1 by { reveal_IsStrictlySorted(); }

        var to := if to1 < from then from else to1;
        assert to == to1;

        var tmp' := mergeToOneChild(
            top.keys, top.msgs, from, to,
            bots[i].keys, bots[i].msgs, 0,
            [], [], tmp.slack);

        all_msgs_not_eq_identity(top);
        all_msgs_not_eq_identity(bots[i]);
        forall j | 0 <= j < |bots[i].keys|
        ensures Route(pivots, bots[i].keys[j]) == i
        {
          assert WFBucketAt(bots[i], pivots, i);
          assert bots[i].keys[j] in bots[i].b;
        }
        mergeToOneOneChild_eq_BucketList(top.keys, top.msgs, from, to,
            bots[i].keys, bots[i].msgs, tmp.slack, pivots, i);

        var results' := results + [BucketOfSeq(tmp'.keys, tmp'.msgs)];
        var res := mergeToChildrenIter(top, bots, idxs, tmp', i+1, results');

        forall r | 0 <= r < i
        ensures results[r] ==
          BucketListItemFlush(BucketIntersect(top, getFlushedKeys(tmp', top)), bots[r], pivots, r)
        {
          calc {
            results[r];
            BucketListItemFlush(BucketIntersect(top, getFlushedKeys(tmp, top)), bots[r], pivots, r);
            {
              if tmp'.SlackExhausted? {
                assert tmp'.end >= from;
              }
              reveal_BucketIntersect();
              assert WFBucketAt(bots[r], pivots, r);
              forall k | Route(pivots, k) == r
                && k in getFlushedKeys(tmp', top)
              ensures k in getFlushedKeys(tmp, top)
              {
              }
              forall k | Route(pivots, k) == r
                && k in getFlushedKeys(tmp, top)
              ensures k in getFlushedKeys(tmp', top)
              {
              }
              BucketListItemFlush_eq(top, 
                getFlushedKeys(tmp', top),
                getFlushedKeys(tmp, top),
                bots[r], pivots, r);
            }
            BucketListItemFlush(BucketIntersect(top, getFlushedKeys(tmp', top)), bots[r], pivots, r);
          }
        }
        calc {
          results'[i];
          {
            reveal_BucketIntersect();
            WellMarshalledBucketsEq(results'[i],
              BucketListItemFlush(
                BucketIntersect(
                  BucketOfSeq(top.keys, top.msgs),
                  tmp'.flushedKeys(top.keys, top.msgs, from, to)
                ),
                BucketOfSeq(bots[i].keys, bots[i].msgs),
                pivots, i
              ));
          }
          BucketListItemFlush(
            BucketIntersect(
              BucketOfSeq(top.keys, top.msgs),
              tmp'.flushedKeys(top.keys, top.msgs, from, to)
            ),
            BucketOfSeq(bots[i].keys, bots[i].msgs),
            pivots, i
          );
          {
            WellMarshalledBucketsEq(top,
              BucketOfSeq(top.keys, top.msgs));
            WellMarshalledBucketsEq(bots[i],
              BucketOfSeq(bots[i].keys, bots[i].msgs));
          }
          BucketListItemFlush(
            BucketIntersect(
              top,
              tmp'.flushedKeys(top.keys, top.msgs, from, to)
            ),
            bots[i],
            pivots, i
          );
          {
            if tmp'.SlackExhausted? {
              assert tmp'.end >= from;
            }
            assert WFBucketAt(bots[i], pivots, i);
            forall k | Route(pivots, k) == i
              && k in getFlushedKeys(tmp', top)
            ensures k in tmp'.flushedKeys(top.keys, top.msgs, from, to)
            {
            }
            forall k | Route(pivots, k) == i
              && k in tmp'.flushedKeys(top.keys, top.msgs, from, to)
            ensures k in getFlushedKeys(tmp', top)
            {
            }
            BucketListItemFlush_eq(top, 
              getFlushedKeys(tmp', top),
              tmp'.flushedKeys(top.keys, top.msgs, from, to),
              bots[i], pivots, i);
          }
          BucketListItemFlush(
            BucketIntersect(
              top,
              getFlushedKeys(tmp', top)
            ),
            bots[i],
            pivots, i
          );
        }

        flushedKeys := mergeToChildrenIterCorrect(top, pivots, bots, idxs, tmp', i+1, results');
      } else {
        var results' := results + [bots[i]];
        var res := mergeToChildrenIter(top, bots, idxs, tmp, i+1, results');

        forall r | 0 <= r < i
        ensures results[r] ==
          BucketListItemFlush(BucketIntersect(top, getFlushedKeys(tmp, top)), bots[r], pivots, r)
        {
        }
        calc {
          results'[i];
          bots[i];
          {
            assert WFBucketAt(bots[i], pivots, i);
            forall k | k in bots[i].b
            ensures Route(pivots, k) == i
            ensures bots[i].b[k] != IdentityMessage()
            {
              RouteIs(pivots, k, i);
            }
            WellMarshalledBucketsEq(bots[i],
                BucketListItemFlush(B(map[]), bots[i], pivots, i));
          }
          BucketListItemFlush(B(map[]), bots[i], pivots, i);
          {
            reveal_BucketIntersect();
            assert BucketIntersect(top, {}).b == map[];
          }
          BucketListItemFlush(BucketIntersect(top, {}), bots[i], pivots, i);
          {
            BucketListItemFlush_eq(top, 
              getFlushedKeys(tmp, top),
              {},
              bots[i], pivots, i);
          }
          BucketListItemFlush(BucketIntersect(top, getFlushedKeys(tmp, top)), bots[i], pivots, i);
        }

        if i+1 <= |pivots| {
          assert bucketStartIdx(top.keys, pivots, i)
              <= bucketStartIdx(top.keys, pivots, i+1) by {
            reveal_IsStrictlySorted();
          }
        }

        flushedKeys := mergeToChildrenIterCorrect(top, pivots, bots, idxs, tmp, i+1, results');
      }
    }
  }

  lemma mergeToChildrenIterSlack(
      top: Bucket,
      bots: seq<Bucket>,
      idxs: seq<int>,
      tmp: singleMergeResult,
      i: int,
      results: seq<Bucket>)
  requires WFBucket(top)
  requires forall i | 0 <= i < |bots| :: WFBucket(bots[i])
  requires forall i | 0 <= i < |results| :: WFBucket(results[i])
  requires 0 < |bots|
  requires |results| == i
  requires 0 <= i <= |bots|
  requires |idxs| == |bots| - 1
  requires forall i | 0 <= i < |idxs| :: 0 <= idxs[i] <= |top.keys|
  requires tmp.SlackExhausted? ==> 0 <= tmp.end <= |top.keys|

  decreases |bots| - i

  ensures var res := mergeToChildrenIter(top, bots, idxs, tmp, i, results);
    && WFBucket(res.top)
    && |res.bots| == |bots|
    && (forall i | 0 <= i < |res.bots| :: WFBucket(res.bots[i]))
    && WeightBucket(res.top) <= WeightBucket(top)
    && WeightBucketList(results) + WeightBucketList(bots[i..]) + tmp.slack
        == WeightBucketList(res.bots) + res.slack
  {
    var res := mergeToChildrenIter(top, bots, idxs, tmp, i, results);
    if i == |bots| {
      assert {:split_here} true;
      if tmp.SlackExhausted? {
        var leftover_top := BucketOfSeq(top.keys[tmp.end..], top.msgs[tmp.end..]);

        assert WeightBucket(res.top) <= WeightBucket(top) by {
          WeightKeyListAdditive(top.keys[..tmp.end], top.keys[tmp.end..]);
          WeightMessageListAdditive(top.msgs[..tmp.end], top.msgs[tmp.end..]);
          assert top.keys[..tmp.end] + top.keys[tmp.end..] == top.keys;
          assert top.msgs[..tmp.end] + top.msgs[tmp.end..] == top.msgs;
        }
      } else {
      }
      assert bots[i..] == [];
      assert WeightBucketList([]) == 0 by { reveal_WeightBucketList(); }
      WFBucketMapOfWFMessageSeq(res.top.keys, res.top.msgs);
    } else {
      assert {:split_here} true;
      calc {
        WeightBucketList(bots[i..]);
        {
          WeightBucketListConcat([bots[i]], bots[i+1..]);
          assert [bots[i]] + bots[i+1..] == bots[i..];
          assert WeightBucketList([bots[i]]) == WeightBucket(bots[i]) by { reveal_WeightBucketList(); }
        }
        WeightBucketList(bots[i+1..]) + WeightBucket(bots[i]);
        {
          //WeightBucket_eq_WeightSeqs(bots[i]);
        }
        WeightBucketList(bots[i+1..]) + WeightKeyList(bots[i].keys) + WeightMessageList(bots[i].msgs);
      }

      assert WeightBucketList([]) == 0 by { reveal_WeightBucketList(); }

      if tmp.MergeCompleted? {
        var from := if i == 0 then 0 else idxs[i-1];
        var to1 := if i == |idxs| then |top.keys| else idxs[i];
        var to := if to1 < from then from else to1;

        var tmp' := mergeToOneChild(
            top.keys, top.msgs, from, to,
            bots[i].keys, bots[i].msgs, 0,
            [], [], tmp.slack);
        mergeToOneChildSlack(
            top.keys, top.msgs, from, to,
            bots[i].keys, bots[i].msgs, 0,
            [], [], tmp.slack);
        var results' := results + [BucketOfSeq(tmp'.keys, tmp'.msgs)];
        WFBucketMapOfWFMessageSeq(tmp'.keys, tmp'.msgs);
        mergeToChildrenIterSlack(top, bots, idxs, tmp', i+1, results');

        calc {
          WeightBucketList(results) + WeightKeyList(tmp'.keys) + WeightMessageList(tmp'.msgs);
          {
            reveal_WeightBucketList();
            assert DropLast(results') == results;
            assert Last(results') == BucketOfSeq(tmp'.keys, tmp'.msgs);
            //WeightBucket_eq_WeightSeqs(results'[i]);
          }
          WeightBucketList(results');
        }

        var res := mergeToChildrenIter(top, bots, idxs, tmp, i, results);
        calc {
          WeightBucketList(results) + WeightBucketList(bots[i..]) + tmp.slack;
          WeightBucketList(results') + WeightBucketList(bots[i+1..]) + tmp'.slack;
          WeightBucketList(res.bots) + res.slack;
        }
      } else {
        var results' := results + [bots[i]];
        mergeToChildrenIterSlack(top, bots, idxs, tmp, i+1, results');

        calc {
          WeightBucketList(results) + WeightKeyList(bots[i].keys) + WeightMessageList(bots[i].msgs);
          {
            reveal_WeightBucketList();
            //WeightBucket_eq_WeightSeqs(results'[i]);
          }
          WeightBucketList(results');
        }
      }
    }
  }

  lemma mergeToChildrenIterPreservesSorted(
      top: Bucket,
      bots: seq<Bucket>,
      idxs: seq<int>,
      tmp: singleMergeResult,
      i: int,
      results: seq<Bucket>)
  requires WFBucket(top)
  requires forall i | 0 <= i < |bots| :: WFBucket(bots[i])
  requires IsStrictlySorted(top.keys)
  requires forall i | 0 <= i < |bots| :: IsStrictlySorted(bots[i].keys)
  requires forall i | 0 <= i < |results| :: IsStrictlySorted(results[i].keys)
  requires 0 < |bots|
  requires |results| == i
  requires 0 <= i <= |bots|
  requires |idxs| == |bots| - 1
  requires forall i | 0 <= i < |idxs| :: 0 <= idxs[i] <= |top.keys|
  requires tmp.SlackExhausted? ==> 0 <= tmp.end <= |top.keys|

  decreases |bots| - i

  ensures var res := mergeToChildrenIter(top, bots, idxs, tmp, i, results);
      && IsStrictlySorted(res.top.keys)
      && forall i | 0 <= i < |res.bots| :: IsStrictlySorted(res.bots[i].keys)
  {
    reveal_IsStrictlySorted();
    var res := mergeToChildrenIter(top, bots, idxs, tmp, i, results);
    if i == |bots| {
      if tmp.SlackExhausted? {
        var leftover_top := BucketOfSeq(top.keys[tmp.end..], top.msgs[tmp.end..]);
      } else {
      }
      assert bots[i..] == [];
      WFBucketMapOfWFMessageSeq(res.top.keys, res.top.msgs);
    } else {
      if tmp.MergeCompleted? {
        var from := if i == 0 then 0 else idxs[i-1];
        var to1 := if i == |idxs| then |top.keys| else idxs[i];
        var to := if to1 < from then from else to1;

        var tmp' := mergeToOneChild(
            top.keys, top.msgs, from, to,
            bots[i].keys, bots[i].msgs, 0,
            [], [], tmp.slack);
        mergeToOneChildPreservesSorted(
            top.keys, top.msgs, from, to,
            bots[i].keys, bots[i].msgs, 0,
            [], [], tmp.slack);
        var results' := results + [BucketOfSeq(tmp'.keys, tmp'.msgs)];
        mergeToChildrenIterPreservesSorted(top, bots, idxs, tmp', i+1, results');

        var res := mergeToChildrenIter(top, bots, idxs, tmp, i, results);
      } else {
        var results' := results + [bots[i]];
        mergeToChildrenIterPreservesSorted(top, bots, idxs, tmp, i+1, results');
      }
    }
  }

 
  lemma mergeToChildrenCorrect(
      top: Bucket,
      pivots: seq<Key>,
      bots: seq<Bucket>,
      slack: nat)
  returns (flushedKeys: set<Key>)

  requires WFBucket(top)
  requires forall i | 0 <= i < |bots| :: WFBucket(bots[i])
  requires 0 < |bots| == |pivots| + 1
  requires BucketWellMarshalled(top)
  requires forall i | 0 <= i < |bots| :: BucketWellMarshalled(bots[i])
  requires WFPivots(pivots)
  requires WFBucketListProper(bots, pivots)

  ensures var res := mergeToChildren(top, pivots, bots, slack);
    && res.top == BucketComplement(top, flushedKeys)
    && res.bots ==
      BucketListFlush(BucketIntersect(top, flushedKeys), bots, pivots)
  {
    reveal_mergeToChildren();
    var idxs := pivotIndexes(top.keys, pivots);
    var tmp := MergeCompleted([], [], slack);
    flushedKeys :=
      mergeToChildrenIterCorrect(top, pivots, bots, idxs, tmp, 0, []);

    var res := mergeToChildren(top, pivots, bots, slack);

    /*var a := res.bots;
    var b := BucketListFlush(BucketIntersect(top, flushedKeys), bots, pivots);
    assert |a| == |b|;
    forall i | 0 <= i < |a|
    ensures a[i] == b[i]
    {
      calc {
        a[i];
        res.bots[i];
        BucketListItemFlush(
          BucketIntersect(top, flushedKeys), bots[i], pivots, i);
        b[i];
      }
    }*/
  }
 
  lemma mergeToChildrenSlack(
      top: Bucket,
      pivots: seq<Key>,
      bots: seq<Bucket>,
      slack: nat)
  requires WFBucket(top)
  requires forall i | 0 <= i < |bots| :: WFBucket(bots[i])
  requires 0 < |bots| == |pivots| + 1
  ensures var res := mergeToChildren(top, pivots, bots, slack);
    && WFBucket(res.top)
    && |res.bots| == |bots|
    && (forall i | 0 <= i < |res.bots| :: WFBucket(res.bots[i]))
    && WeightBucket(res.top) <= WeightBucket(top)
    && WeightBucketList(bots) + slack == WeightBucketList(res.bots) + res.slack
  {
    reveal_mergeToChildren();
    var idxs := pivotIndexes(top.keys, pivots);
    var tmp := MergeCompleted([], [], slack);
    assert WeightBucketList([]) == 0 by { reveal_WeightBucketList(); }
    mergeToChildrenIterSlack(top, bots, idxs, tmp, 0, []);
  }
 
  lemma mergeToChildrenPreservesSorted(
      top: Bucket,
      pivots: seq<Key>,
      bots: seq<Bucket>,
      slack: nat)
  requires WFBucket(top)
  requires forall i | 0 <= i < |bots| :: WFBucket(bots[i])
  requires IsStrictlySorted(top.keys)
  requires forall i | 0 <= i < |bots| :: IsStrictlySorted(bots[i].keys)
  requires 0 < |bots| == |pivots| + 1
  ensures var res := mergeToChildren(top, pivots, bots, slack);
      && IsStrictlySorted(res.top.keys)
      && forall i | 0 <= i < |res.bots| :: IsStrictlySorted(res.bots[i].keys)
  {
    reveal_mergeToChildren();
    var idxs := pivotIndexes(top.keys, pivots);
    var tmp := MergeCompleted([], [], slack);
    mergeToChildrenIterPreservesSorted(top, bots, idxs, tmp, 0, []);
  }

  datatype partialFlushResult = partialFlushResult(top: Bucket, bots: seq<Bucket>)

  function {:opaque} partialFlush(
      top: Bucket,
      pivots: seq<Key>,
      bots: seq<Bucket>) : (res : partialFlushResult)
  requires WFBucket(top)
  requires forall i | 0 <= i < |bots| :: WFBucket(bots[i])
  requires 0 < |bots| == |pivots| + 1
  requires WeightBucketList(bots) <= MaxTotalBucketWeight()
  ensures |res.bots| == |bots|
  {
    var res := mergeToChildren(
        top, pivots, bots, MaxTotalBucketWeight() - WeightBucketList(bots));
    partialFlushResult(res.top, res.bots)
  }

  lemma partialFlushCorrect(
      top: Bucket,
      pivots: seq<Key>,
      bots: seq<Bucket>)
  returns (flushedKeys: set<Key>)
  requires WFBucket(top)
  requires forall i | 0 <= i < |bots| :: WFBucket(bots[i])
  requires 0 < |bots| == |pivots| + 1
  requires BucketWellMarshalled(top)
  requires forall i | 0 <= i < |bots| :: BucketWellMarshalled(bots[i])
  requires WFPivots(pivots)
  requires WFBucketListProper(bots, pivots)
  requires WeightBucketList(bots) <= MaxTotalBucketWeight()
  ensures var res := partialFlush(top, pivots, bots);
    && res.top == BucketComplement(top, flushedKeys)
    && res.bots ==
      BucketListFlush(BucketIntersect(top, flushedKeys), bots, pivots)
  {
    reveal_partialFlush();
    flushedKeys := mergeToChildrenCorrect(
      top, pivots, bots, MaxTotalBucketWeight() - WeightBucketList(bots));
  }

  lemma partialFlushWeightBound(
      top: Bucket,
      pivots: seq<Key>,
      bots: seq<Bucket>)
  requires WFBucket(top)
  requires forall i | 0 <= i < |bots| :: WFBucket(bots[i])
  requires 0 < |bots| == |pivots| + 1
  requires WeightBucketList(bots) <= MaxTotalBucketWeight()
  ensures var res := partialFlush(top, pivots, bots);
      && WFBucket(res.top)
      && |res.bots| == |bots|
      && (forall i | 0 <= i < |res.bots| :: WFBucket(res.bots[i]))
      && WeightBucket(res.top) <= WeightBucket(top)
      && WeightBucketList(res.bots) <= MaxTotalBucketWeight()
  {
    reveal_partialFlush();
    mergeToChildrenSlack(
        top, pivots, bots, MaxTotalBucketWeight() - WeightBucketList(bots));
  }

  lemma partialFlushWeightPreservesSorted(
      top: Bucket,
      pivots: seq<Key>,
      bots: seq<Bucket>)
  requires WFBucket(top)
  requires forall i | 0 <= i < |bots| :: WFBucket(bots[i])
  requires 0 < |bots| == |pivots| + 1
  requires IsStrictlySorted(top.keys)
  requires forall i | 0 <= i < |bots| :: IsStrictlySorted(bots[i].keys)
  requires WeightBucketList(bots) <= MaxTotalBucketWeight()
  ensures var res := partialFlush(top, pivots, bots);
      && IsStrictlySorted(res.top.keys)
      && forall i | 0 <= i < |res.bots| :: IsStrictlySorted(res.bots[i].keys)
  {
    reveal_partialFlush();
    mergeToChildrenPreservesSorted(
        top, pivots, bots, MaxTotalBucketWeight() - WeightBucketList(bots));
  }
}
