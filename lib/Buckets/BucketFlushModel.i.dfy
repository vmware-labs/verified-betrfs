// Copyright 2018-2021 VMware, Inc.
// SPDX-License-Identifier: BSD-2-Clause

include "BucketsLib.i.dfy"
include "BucketWeights.i.dfy"
include "../Base/Message.i.dfy"
include "../Base/Maps.i.dfy"
include "../Base/total_order.i.dfy"
include "../../MapSpec/UI.s.dfy"
include "../../MapSpec/MapSpec.s.dfy"
include "../../PivotBetree/Bounds.i.dfy"

// TODO rename this file to be BucketFlushing or something

module BucketFlushModel {
  import opened BucketMaps
  import opened BucketsLib
  import opened BucketWeights
  import opened BoundedPivotsLib
  import opened Lexi = Lexicographic_Byte_Order
  import opened ValueMessage
  import opened Maps
  import opened Sequences
  import opened KeyType
  import opened Options
  import UI
  import MS = MapSpec
  import opened Bounds
  import opened NativeTypes
  import opened MapSeqs
  
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
      map_of_seqs(this.keys, this.msgs)
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
      var top := map_of_seqs(
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
    // case 1: all relevant keys in the parent bucket is merged
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
    // case 2: mergeable key at the child's bucket
    // same key in parent and child, can merge message
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
    // case 3: no more keys to go through at the child, just take parent key, msg
    else if bot_from == |bot_keys| ||
        Lexi.lt(top_keys[from], bot_keys[bot_from]) then
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
    // case 4: no mergeable keys from parent, just take child key and message
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
    var a := map_of_seqs(top_keys[from+1..to], top_msgs[from+1..to])[top_keys[from] := top_msgs[from]];
    var b := map_of_seqs(top_keys[from..to], top_msgs[from..to]);
    forall k | k in a
    ensures k in b
    ensures a[k] == b[k]
    {
      reveal_IsStrictlySorted();
      if k == top_keys[from] {
        MapMapsIndex(top_keys[from..to], top_msgs[from..to], 0);
        assert a[k] == b[k];
      } else {
        var j := GetIndex(top_keys[from+1..to], top_msgs[from+1..to], k);
        MapMapsIndex(top_keys[from..to], top_msgs[from..to], j+1);
        assert a[k] == b[k];
      }
    }
    forall k | k in b
    ensures k in a
    {
      reveal_IsStrictlySorted();
      var j := GetIndex(top_keys[from..to], top_msgs[from..to], k);
      if (j == 0) {
      } else {
        MapMapsIndex(top_keys[from+1..to], top_msgs[from+1..to], j-1);
      }
    }
    assert map_of_seqs(top_keys[from+1..to], top_msgs[from+1..to])[top_keys[from] := top_msgs[from]]
        ==  map_of_seqs(top_keys[from..to], top_msgs[from..to]);
    reveal_IsStrictlySorted();
  }

  predicate seq_lt(a: seq<Key>, b: seq<Key>, start: int)
  requires 0 <= start <= |b|
  {
    forall i, j | 0 <= i < |a| && start <= j < |b| ::
      Lexi.lt(a[i], b[j])
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
      map_of_seqs(bot_keys[from..], bot_msgs[from..]),
      map_of_seqs(acc_keys, acc_msgs))
    == map_of_seqs(acc_keys + bot_keys[from..], acc_msgs + bot_msgs[from..])
  {
    var x := 
      topBotAccMerge(map[],
        map_of_seqs(bot_keys[from..], bot_msgs[from..]),
        map_of_seqs(acc_keys, acc_msgs));
    var y := map_of_seqs(acc_keys + bot_keys[from..], acc_msgs + bot_msgs[from..]);
    forall k: Key | k in y
    ensures k in x
    ensures x[k] == y[k]
    {
      reveal_IsStrictlySorted();
      var i := GetIndex(acc_keys + bot_keys[from..], acc_msgs + bot_msgs[from..], k);
      if i < |acc_keys| {
        MapMapsIndex(acc_keys, acc_msgs, i);
        if k in map_of_seqs(bot_keys[from..], bot_msgs[from..]) {
          var j := GetIndex(bot_keys[from..], bot_msgs[from..], k);
          assert false;
        }
      } else {
        MapMapsIndex(bot_keys[from..], bot_msgs[from..], i - |acc_keys|);
        if k in map_of_seqs(acc_keys, acc_msgs) {
          var j := GetIndex(acc_keys, acc_msgs, k);
          assert false;
        }
      }
    }
    forall k | k in x
    ensures k in y
    {
      reveal_IsStrictlySorted();
      if k in map_of_seqs(bot_keys[from..], bot_msgs[from..]) {
        var j := GetIndex(bot_keys[from..], bot_msgs[from..], k);
        MapMapsIndex(acc_keys + bot_keys[from..], acc_msgs + bot_msgs[from..], j + |acc_keys|);
      } else {
        assert k in map_of_seqs(acc_keys, acc_msgs);
        var j := GetIndex(acc_keys, acc_msgs, k);
        MapMapsIndex(acc_keys + bot_keys[from..], acc_msgs + bot_msgs[from..], j);
      }
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
      var top := map_of_seqs(
            top_keys[from..to], top_msgs[from..to]);
      var bot := map_of_seqs(
            bot_keys[bot_from..], bot_msgs[bot_from..]);
      var acc := map_of_seqs(acc_keys, acc_msgs);
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
    var top := map_of_seqs(
          top_keys[from..to], top_msgs[from..to]);
    var bot := map_of_seqs(
          bot_keys[bot_from..], bot_msgs[bot_from..]);
    var acc := map_of_seqs(acc_keys, acc_msgs);

    assert IsStrictlySorted(bot_keys[bot_from..]) by { reveal_IsStrictlySorted(); }
    assert IsStrictlySorted(top_keys[from..to]) by { reveal_IsStrictlySorted(); }

    if from == to {
      var a := res.bucketMap();
      var b := topBotAccMerge(
        res.flushedMap(top_keys, top_msgs, from, to),
        bot, acc);
      assert res.flushedMap(top_keys, top_msgs, from, to) == map[];
      forall k | k in a
      ensures k in b
      ensures a[k] == b[k]
      {
        var i := GetIndex(res.keys, res.msgs, k);
        if i < |acc_keys| {
          MapMapsIndex(acc_keys, acc_msgs, i);
          if k in map_of_seqs(bot_keys[bot_from..], bot_msgs[bot_from..]) {
            var j := GetIndex(bot_keys[bot_from..], bot_msgs[bot_from..], k);
          }
        } else {
          MapMapsIndex(bot_keys[bot_from..],
              bot_msgs[bot_from..], i-|acc_keys|);
          if k in map_of_seqs(acc_keys, acc_msgs) {
            var j := GetIndex(acc_keys, acc_msgs, k);
          }
        }
      }
      forall k | k in b
      ensures k in a
      {
        assert IsStrictlySorted(res.keys) by { reveal_IsStrictlySorted(); }
        if k in res.flushedMap(top_keys, top_msgs, from, to) {
          assert false; // because from == to
        } else if k in acc {
          var j := GetIndex(acc_keys, acc_msgs, k);
          MapMapsIndex(res.keys, res.msgs, j);
          assert k == res.keys[j];
        } else {
          assert k in bot;
          var j := GetIndex(bot_keys[bot_from..], bot_msgs[bot_from..], k);
          MapMapsIndex(res.keys, res.msgs, j + |acc_keys|);
        }
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
        var i := GetIndex(res.keys, res.msgs, k);
        if i < |acc_keys| {
          MapMapsIndex(acc_keys, acc_msgs, i);
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
          MapMapsIndex(top_keys[from..to], top_msgs[from..to], i - |acc_keys|);
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
            map_of_seqs(bot_keys[bot_from+1..], bot_msgs[bot_from+1..]),
            map_of_seqs(acc_keys, acc_msgs));
          {
            flushedMapPopFront(res, top_keys, top_msgs, from, to);
            assert res.flushedMap(top_keys, top_msgs, from, to)
                == res.flushedMap(top_keys, top_msgs, from+1, to)[key := topmsg];
            map_of_seqs_pop_front(bot_keys, bot_msgs, bot_from);
            assert map_of_seqs(bot_keys[bot_from..], bot_msgs[bot_from..])
                == map_of_seqs(bot_keys[bot_from+1..], bot_msgs[bot_from+1..])[key := botmsg];
            assert key !in acc;
            assert key !in map_of_seqs(bot_keys[bot_from+1..], bot_msgs[bot_from+1..]);
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
              map_of_seqs(
                  bot_keys[bot_from+1..], bot_msgs[bot_from+1..]),
              map_of_seqs(acc_keys + [key], acc_msgs + [msg])
            );
            {
              map_of_seqs_push_back(acc_keys, acc_msgs, key, msg);
              flushedMapPopFront(res, top_keys, top_msgs, from, to);
              map_of_seqs_pop_front(bot_keys, bot_msgs, bot_from);
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
    } else if bot_from == |bot_keys| || Lexi.lt(top_keys[from], bot_keys[bot_from]) {
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
            bot, map_of_seqs(acc_keys + [key], acc_msgs + [msg]));
          {
            map_of_seqs_push_back(acc_keys, acc_msgs, key, msg);
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
          map_of_seqs(
              bot_keys[bot_from+1..], bot_msgs[bot_from+1..]),
          map_of_seqs(acc_keys + [key], acc_msgs + [msg]));
        {
          map_of_seqs_pop_front(bot_keys, bot_msgs, bot_from);
          map_of_seqs_push_back(acc_keys, acc_msgs, key, msg);
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

  function bucketStartIdx(top_keys: seq<Key>, pivots: PivotTable, r: int) : (i: int)
  requires WFPivots(pivots)
  requires 0 <= r < NumBuckets(pivots)
  {
    Keyspace.binarySearchIndexOfFirstKeyGte(KeysToElements(top_keys), pivots[r])
  }

  function bucketEndIdx(top_keys: seq<Key>, pivots: PivotTable, r: int) : (i: int)
  requires WFPivots(pivots)
  requires 0 <= r < NumBuckets(pivots)
  {
    Keyspace.binarySearchIndexOfFirstKeyGte(KeysToElements(top_keys), pivots[r+1])
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
  requires 0 <= r < NumBuckets(pivots)
  requires WFPivots(pivots)
  requires from == bucketStartIdx(top_keys, pivots, r)
  requires to == bucketEndIdx(top_keys, pivots, r)
  requires IsStrictlySorted(top_keys)
  requires IsStrictlySorted(bot_keys)
  requires forall i | 0 <= i < |bot_msgs| :: bot_msgs[i] != IdentityMessage()
  requires forall i | 0 <= i < |top_msgs| :: top_msgs[i] != IdentityMessage()
  requires forall i | 0 <= i < |bot_keys| :: BoundedKey(pivots, bot_keys[i]) && Route(pivots, bot_keys[i]) == r
  ensures
      var res := mergeToOneChild(
            top_keys, top_msgs, from, to,
            bot_keys, bot_msgs, 0,
            [], [], slack);
      var top := map_of_seqs(top_keys, top_msgs);
      var bot := map_of_seqs(bot_keys, bot_msgs);
      && IsStrictlySorted(res.keys)
      && BucketListItemFlush(
          BucketIntersect(top, res.flushedKeys(top_keys, top_msgs, from, to)),
          bot, pivots, r)
        == res.bucketMap()
  {
    var res := mergeToOneChild(
          top_keys, top_msgs, from, to,
          bot_keys, bot_msgs, 0,
          [], [], slack);
    var top := map_of_seqs(top_keys, top_msgs);
    var bot := map_of_seqs(bot_keys, bot_msgs);

    var itop := BucketIntersect(top, res.flushedKeys(top_keys, top_msgs, from, to));

    calc {
      BucketListItemFlush(itop, bot, pivots, r);
      {
        var a := BucketListItemFlush(itop, bot, pivots, r);
        var b := topBotAccMerge(itop, bot, map[]);
        forall k | k in a
        ensures k in b
        ensures a[k] == b[k]
        {
        }
        forall k | k in b
        ensures k in a
        {
          if k in itop {
            reveal_BucketIntersect();
            reveal_IsStrictlySorted();
            RouteIs(pivots, k, r);
          } else {
            var j := GetIndex(bot_keys, bot_msgs, k);
            assert Route(pivots, bot_keys[j]) == r;
          }
        }
      }
      topBotAccMerge(itop, bot, map[]);
      topBotAccMerge(
        itop,
        map_of_seqs(bot_keys, bot_msgs),
        map[]);
      {
        reveal_BucketIntersect();
        var x := itop;
        var y := res.flushedMap(top_keys, top_msgs, from, to);
        forall k | k in x
        ensures k in y
        ensures x[k] == y[k]
        {
          var i := GetIndex(top_keys, top_msgs, k);
          reveal_IsStrictlySorted();
          MapMapsIndex(top_keys[from..to], top_msgs[from..to], i - from);
        }
        forall k | k in y
        ensures k in x
        {
          var i := GetIndex(top_keys[from..to], top_msgs[from..to], k);
          MapMapsIndex(top_keys, top_msgs, from+i);
        }
        assert itop == res.flushedMap(top_keys, top_msgs, from, to);
      }
      topBotAccMerge(
        res.flushedMap(top_keys, top_msgs, from, to),
        map_of_seqs(bot_keys, bot_msgs),
        map[]);
      topBotAccMerge(
        res.flushedMap(top_keys, top_msgs, from, to),
        map_of_seqs(bot_keys, bot_msgs),
        map_of_seqs([], []));
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
        Lexi.lt(top_keys[from], bot_keys[bot_from]) {
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
        Lexi.lt(top_keys[from], bot_keys[bot_from]) {
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

 function pivotIndexes(top_keys: seq<Key>, pivots: PivotTable) : (res: seq<int>)
  ensures |res| == |pivots|
  ensures forall i | 0 <= i < |res| :: res[i]
      == Keyspace.binarySearchIndexOfFirstKeyGte(KeysToElements(top_keys), pivots[i])
  decreases |pivots|
  {
    if |pivots| == 0 
    then []
    else (
      pivotIndexes(top_keys, DropLast(pivots)) +
      [ Keyspace.binarySearchIndexOfFirstKeyGte(KeysToElements(top_keys), Last(pivots)) ]
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
  requires |idxs| == |bots|+1
  requires forall i | 0 <= i < |idxs| :: 0 <= idxs[i] <= |top.keys|
  requires tmp.SlackExhausted? ==> 0 <= tmp.end <= |top.keys|
  decreases |bots| - i
  ensures |res.bots| == |bots|
  {
    if i == |bots| then (
      if tmp.SlackExhausted? then (
        var leftover_top := Bucket(top.keys[tmp.end..], top.msgs[tmp.end..]);
        mergeResult(leftover_top, results, tmp.slack)
      ) else (
        mergeResult(EmptyBucket(), results, tmp.slack)
      )
    ) else (
      if tmp.MergeCompleted? then (
        var from := idxs[i];
        var to1 := idxs[i+1];
        var to := if to1 < from then from else to1;
        var tmp' := mergeToOneChild(
            top.keys, top.msgs, from, to,
            bots[i].keys, bots[i].msgs, 0,
            [], [], tmp.slack);
        var results' := results + [Bucket(tmp'.keys, tmp'.msgs)];
        mergeToChildrenIter(top, bots, idxs, tmp', i+1, results')
      ) else (
        var results' := results + [bots[i]];
        mergeToChildrenIter(top, bots, idxs, tmp, i+1, results')
      )
    )
  }
 
  function {:opaque} mergeToChildren(
      top: Bucket,
      pivots: PivotTable,
      bots: seq<Bucket>,
      slack: nat) : (result: mergeResult)
  requires WFBucket(top)
  requires forall i | 0 <= i < |bots| :: WFBucket(bots[i])
  requires 0 < |bots| == NumBuckets(pivots)
  ensures |result.bots| == |bots|
  {
    var idxs := pivotIndexes(top.keys, pivots);
    var tmp := MergeCompleted([], [], slack);
    mergeToChildrenIter(top, bots, idxs, tmp, 0, [])
  }

  function getFlushedKeys(tmp: singleMergeResult, top: Bucket) : (keys: set<Key>)
  requires tmp.SlackExhausted? ==> tmp.end <= |top.keys|
  ensures forall k | k in keys :: k in top.keys
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
  ensures BucketComplement(top.as_map(), getFlushedKeys(tmp, top))
      == map_of_seqs(top.keys[tmp.end..], top.msgs[tmp.end..])
  {
    reveal_BucketComplement();
    reveal_IsStrictlySorted();

    var a := BucketComplement(top.as_map(), getFlushedKeys(tmp, top));
    var b := map_of_seqs(top.keys[tmp.end..], top.msgs[tmp.end..]);
    forall k | k in a
    ensures k in b
    ensures a[k] == b[k]
    {
      assert k in top.as_map();
      var i := GetIndex(top.keys, top.msgs, k);
      assert i >= tmp.end;
      MapMapsIndex(top.keys[tmp.end..],
          top.msgs[tmp.end..], i - tmp.end);
    }
    forall k | k in b
    ensures k in a
    {
      var j := GetIndex(top.keys[tmp.end..], top.msgs[tmp.end..], k);
      MapMapsIndex(top.keys, top.msgs, j + tmp.end);
    }
    assert a == b;

    //WFBucketComplement(top, getFlushedKeys(tmp, top));
    //WellMarshalledBucketsEq(BucketComplement(top, getFlushedKeys(tmp, top)),
    //  Bucket(top.keys[tmp.end..], top.msgs[tmp.end..]));
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
      MapMapsIndex(bucket.keys, bucket.msgs, i);
    }
  }

  lemma BucketListItemFlush_eq(top: Bucket, keys1: set<Key>, keys2: set<Key>, bot: Bucket, pivots: PivotTable, i: int)
  requires 0 <= i < NumBuckets(pivots)
  requires WFBucket(top)
  requires WFBucket(bot)
  requires WFPivots(pivots)
  requires forall k | BoundedKey(pivots, k) && Route(pivots, k) == i && k in keys1 :: k in keys2
  requires forall k | BoundedKey(pivots, k) && Route(pivots, k) == i && k in keys2 :: k in keys1
  ensures BucketListItemFlush(BucketIntersect(top.as_map(), keys1), bot.as_map(), pivots, i)
       == BucketListItemFlush(BucketIntersect(top.as_map(), keys2), bot.as_map(), pivots, i)
  {
    reveal_BucketIntersect();
  }

  lemma mergeToChildrenIterCorrect(
      top: Bucket,
      pivots: PivotTable,
      bots: seq<Bucket>,
      idxs: seq<int>,
      tmp: singleMergeResult,
      i: int,
      results: seq<Bucket>)
  returns (flushedKeys: set<Key>)
  requires WFPivots(pivots)
  requires WFBucket(top)
  requires forall k | k in top.keys :: BoundedKey(pivots, k)
  requires forall i | 0 <= i < |bots| :: WFBucket(bots[i])
  requires 0 < |bots| == NumBuckets(pivots)
  requires |results| == i
  requires |idxs| == |bots|+1
  requires 0 <= i <= |bots|
  requires forall i | 0 <= i < |idxs| ::
    idxs[i] == Keyspace.binarySearchIndexOfFirstKeyGte(KeysToElements(top.keys), pivots[i])
  requires tmp.SlackExhausted? ==> 0 <= tmp.end <= |top.keys|
  requires IsStrictlySorted(top.keys)
  requires forall i | 0 <= i < |bots| :: IsStrictlySorted(bots[i].keys)
  requires WFBucketListProper(bots, pivots)
  requires i < NumBuckets(pivots) ==> tmp.SlackExhausted? ==> tmp.end <= bucketStartIdx(top.keys, pivots, i)
  requires forall r | 0 <= r < i :: |results[r].keys| == |results[r].msgs|
  requires forall r | 0 <= r < i :: results[r].as_map() ==
      BucketListItemFlush(BucketIntersect(top.as_map(), getFlushedKeys(tmp, top)), bots[r].as_map(), pivots, r)

  decreases |bots| - i

  ensures var res :=
    mergeToChildrenIter(top, bots, idxs, tmp, i, results);
    && |res.top.keys| == |res.top.msgs|
    && res.top.as_map() == BucketComplement(top.as_map(), flushedKeys)
    && (forall r | 0 <= r < |res.bots| :: |res.bots[r].keys| == |res.bots[r].msgs|)
    && (forall r | 0 <= r < |res.bots| :: res.bots[r].as_map() ==
      BucketListItemFlush(BucketIntersect(top.as_map(), flushedKeys), bots[r].as_map(), pivots, r))
  ensures forall k | k in flushedKeys :: k in top.keys
  {
    if i == |bots| {
      flushedKeys := getFlushedKeys(tmp, top);
      if tmp.SlackExhausted? {
        var leftover_top := Bucket(top.keys[tmp.end..], top.msgs[tmp.end..]);
        var res := mergeResult(leftover_top, results, tmp.slack);
        assert res.top.as_map() == BucketComplement(top.as_map(), flushedKeys) by {
          BucketMapOfSeqKeysComplement(top, tmp);
        }
      } else {
        var res := mergeResult(EmptyBucket(), results, tmp.slack);
        calc {
          res.top.as_map();
          map[];
          {
            reveal_BucketComplement();
            forall key | key in top.as_map()
            ensures key in flushedKeys;
            {
              var i := GetIndex(top.keys, top.msgs, key);
            }
            assert BucketComplement(top.as_map(), flushedKeys)
                == map[];
          }
          BucketComplement(top.as_map(), flushedKeys);
        }
      }
    } else {
      if tmp.MergeCompleted? {
        var from := idxs[i];
        var to := idxs[i+1];
        assert from == bucketStartIdx(top.keys, pivots, i);
        assert to == bucketEndIdx(top.keys, pivots, i);
        assert from <= to by {
          reveal_IsStrictlySorted(); 
          Keyspace.reveal_IsStrictlySorted(); 
        }

        var tmp' := mergeToOneChild(
            top.keys, top.msgs, from, to,
            bots[i].keys, bots[i].msgs, 0,
            [], [], tmp.slack);
        all_msgs_not_eq_identity(top);
        all_msgs_not_eq_identity(bots[i]);
        mergeToOneOneChild_eq_BucketList(top.keys, top.msgs, from, to,
            bots[i].keys, bots[i].msgs, tmp.slack, pivots, i);

        // show tmp' key range
        forall k | k in top.keys && Route(pivots, k) < i 
        ensures k in getFlushedKeys(tmp', top)
        {
          if tmp'.SlackExhausted? && tmp'.end < |top.keys| {
            reveal_IsStrictlySorted();
          }
        }
        // show previous results hold up
        var results' := results + [Bucket(tmp'.keys, tmp'.msgs)];
        forall r | 0 <= r < i
        ensures results'[r].as_map() ==
          BucketListItemFlush(BucketIntersect(top.as_map(), getFlushedKeys(tmp', top)), bots[r].as_map(), pivots, r) {
          BucketListItemFlush_eq(top, 
            getFlushedKeys(tmp', top),
            getFlushedKeys(tmp, top), 
            bots[r], pivots, r);
        }
        // show current result
        calc {
          results'[i].as_map();
          {
            reveal_BucketIntersect();
            /*WellMarshalledBucketsEq(results'[i],
              BucketListItemFlush(
                BucketIntersect(
                  top.as_map(),
                  tmp'.flushedKeys(top.keys, top.msgs, from, to)
                ),
                bots[i].as_map(),
                pivots, i
              ));*/
          }
          BucketListItemFlush(
            BucketIntersect(
              top.as_map(),
              tmp'.flushedKeys(top.keys, top.msgs, from, to)
            ),
            bots[i].as_map(),
            pivots, i
          );
          {
            if tmp'.SlackExhausted? {
              assert tmp'.end >= from;
            }
            assert WFBucketAt(bots[i], pivots, i);
            forall k | BoundedKey(pivots, k) && Route(pivots, k) == i
              && k in getFlushedKeys(tmp', top)
            ensures k in tmp'.flushedKeys(top.keys, top.msgs, from, to)
            {
              reveal_IsStrictlySorted();
            }
            forall k | BoundedKey(pivots, k) && Route(pivots, k) == i
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
              top.as_map(),
              getFlushedKeys(tmp', top)
            ),
            bots[i].as_map(),
            pivots, i
          );
        }
        flushedKeys := mergeToChildrenIterCorrect(top, pivots, bots, idxs, tmp', i+1, results');
      } else {
        var results' := results + [bots[i]];
        var res := mergeToChildrenIter(top, bots, idxs, tmp, i+1, results');
        calc {
          results'[i].as_map();
          bots[i].as_map();
          {
            assert WFBucketAt(bots[i], pivots, i);
            forall k | k in bots[i].as_map()
            ensures BoundedKey(pivots, k)
            ensures Route(pivots, k) == i
            ensures bots[i].as_map()[k] != IdentityMessage()
            {
              var j := GetIndex(bots[i].keys, bots[i].msgs, k);
            }
          }
          BucketListItemFlush(map[], bots[i].as_map(), pivots, i);
          {
            reveal_BucketIntersect();
            assert BucketIntersect(top.as_map(), {}) == map[];
          }
          BucketListItemFlush(BucketIntersect(top.as_map(), {}), bots[i].as_map(), pivots, i);
          {
            reveal_IsStrictlySorted();
            BucketListItemFlush_eq(top,
              getFlushedKeys(tmp, top),
              {},
              bots[i], pivots, i);
          }
          BucketListItemFlush(BucketIntersect(top.as_map(), getFlushedKeys(tmp, top)), bots[i].as_map(), pivots, i);
        }

        if i+1 < NumBuckets(pivots) {
          assert bucketStartIdx(top.keys, pivots, i) <= bucketStartIdx(top.keys, pivots, i+1)
          by {
            reveal_IsStrictlySorted();
            Keyspace.reveal_IsStrictlySorted();
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
  requires |idxs| == |bots|+1
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
        var leftover_top := Bucket(top.keys[tmp.end..], top.msgs[tmp.end..]);

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
      //WFBucketMapOfWFMessageSeq(res.top.keys, res.top.msgs);
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
        var from := idxs[i];
        var to1 := idxs[i+1];
        var to := if to1 < from then from else to1;

        var tmp' := mergeToOneChild(
            top.keys, top.msgs, from, to,
            bots[i].keys, bots[i].msgs, 0,
            [], [], tmp.slack);
        mergeToOneChildSlack(
            top.keys, top.msgs, from, to,
            bots[i].keys, bots[i].msgs, 0,
            [], [], tmp.slack);
        var results' := results + [Bucket(tmp'.keys, tmp'.msgs)];
        mergeToChildrenIterSlack(top, bots, idxs, tmp', i+1, results');

        calc {
          WeightBucketList(results) + WeightKeyList(tmp'.keys) + WeightMessageList(tmp'.msgs);
          {
            reveal_WeightBucketList();
            assert DropLast(results') == results;
            assert Last(results') == Bucket(tmp'.keys, tmp'.msgs);
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
  requires |idxs| == |bots|+1
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
        var leftover_top := Bucket(top.keys[tmp.end..], top.msgs[tmp.end..]);
      } else {
      }
      assert bots[i..] == [];
    } else {
      if tmp.MergeCompleted? {
        var from := idxs[i];
        var to1 := idxs[i+1];
        var to := if to1 < from then from else to1;

        var tmp' := mergeToOneChild(
            top.keys, top.msgs, from, to,
            bots[i].keys, bots[i].msgs, 0,
            [], [], tmp.slack);
        mergeToOneChildPreservesSorted(
            top.keys, top.msgs, from, to,
            bots[i].keys, bots[i].msgs, 0,
            [], [], tmp.slack);
        var results' := results + [Bucket(tmp'.keys, tmp'.msgs)];
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
      pivots: PivotTable,
      bots: seq<Bucket>,
      slack: nat)
  returns (flushedKeys: set<Key>)

  requires WFBucket(top)
  requires forall i | 0 <= i < |bots| :: WFBucket(bots[i])
  requires 0 < |bots| == NumBuckets(pivots)
  requires BucketWellMarshalled(top)
  requires forall i | 0 <= i < |bots| :: BucketWellMarshalled(bots[i])
  requires WFPivots(pivots)
  requires WFBucketListProper(bots, pivots)
  requires forall k | k in top.keys :: BoundedKey(pivots, k)

  // NOTE: might be cleaner to just say
  // flushedKeys == top keys - res.top keys

  ensures var res := mergeToChildren(top, pivots, bots, slack);
    && |res.top.keys| == |res.top.msgs|
    && res.top.as_map() == BucketComplement(top.as_map(), flushedKeys)
    && |res.bots| == |bots|
    && (forall i | 0 <= i < |res.bots| :: |res.bots[i].keys| == |res.bots[i].msgs|)
    && (forall i | 0 <= i < |res.bots| ::
          res.bots[i].as_map() ==
      BucketListItemFlush(BucketIntersect(top.as_map(), flushedKeys), bots[i].as_map(), pivots, i)
    )
  ensures forall k | k in flushedKeys :: k in top.keys
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
      pivots: PivotTable,
      bots: seq<Bucket>,
      slack: nat)
  requires WFPivots(pivots)
  requires WFBucket(top)
  requires forall i | 0 <= i < |bots| :: WFBucket(bots[i])
  requires 0 < |bots| == NumBuckets(pivots)
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
      pivots: PivotTable,
      bots: seq<Bucket>,
      slack: nat)
  requires WFPivots(pivots)
  requires WFBucket(top)
  requires forall i | 0 <= i < |bots| :: WFBucket(bots[i])
  requires IsStrictlySorted(top.keys)
  requires forall i | 0 <= i < |bots| :: IsStrictlySorted(bots[i].keys)
  requires 0 < |bots| == NumBuckets(pivots)
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
      pivots: PivotTable,
      bots: seq<Bucket>) : (res : partialFlushResult)
  requires WFBucket(top)
  requires forall i | 0 <= i < |bots| :: WFBucket(bots[i])
  requires 0 < |bots| == NumBuckets(pivots)
  requires WeightBucketList(bots) <= MaxTotalBucketWeight()
  ensures |res.bots| == |bots|
  {
    var res := mergeToChildren(
        top, pivots, bots, MaxTotalBucketWeight() - WeightBucketList(bots));
    partialFlushResult(res.top, res.bots)
  }

  lemma partialFlushCorrect(
      top: Bucket,
      pivots: PivotTable,
      bots: seq<Bucket>)
  returns (flushedKeys: set<Key>)
  requires WFPivots(pivots)
  requires WFBucket(top)
  requires forall i | 0 <= i < |bots| :: WFBucket(bots[i])
  requires 0 < |bots| == NumBuckets(pivots)
  requires BucketWellMarshalled(top)
  requires forall i | 0 <= i < |bots| :: BucketWellMarshalled(bots[i])
  requires WFPivots(pivots)
  requires WFBucketListProper(bots, pivots)
  requires WeightBucketList(bots) <= MaxTotalBucketWeight()
  requires forall k | k in top.keys :: BoundedKey(pivots, k)
  ensures var res := partialFlush(top, pivots, bots);
    && |res.top.keys| == |res.top.msgs|
    && res.top.as_map() == BucketComplement(top.as_map(), flushedKeys)
    && |res.bots| == |bots|
    && (forall i | 0 <= i < |res.bots| :: |res.bots[i].keys| == |res.bots[i].msgs|)
    && (forall i | 0 <= i < |res.bots| ::
          res.bots[i].as_map() ==
      BucketListItemFlush(BucketIntersect(top.as_map(), flushedKeys), bots[i].as_map(), pivots, i)
    )
  ensures forall k | k in flushedKeys :: k in top.keys
  {
    reveal_partialFlush();
    flushedKeys := mergeToChildrenCorrect(
      top, pivots, bots, MaxTotalBucketWeight() - WeightBucketList(bots));
  }

  lemma partialFlushWeightBound(
      top: Bucket,
      pivots: PivotTable,
      bots: seq<Bucket>)
  requires WFPivots(pivots)
  requires WFBucket(top)
  requires forall i | 0 <= i < |bots| :: WFBucket(bots[i])
  requires 0 < |bots| == NumBuckets(pivots)
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

  lemma partialFlushPreservesSorted(
      top: Bucket,
      pivots: PivotTable,
      bots: seq<Bucket>)
  requires WFPivots(pivots)
  requires WFBucket(top)
  requires forall i | 0 <= i < |bots| :: WFBucket(bots[i])
  requires 0 < |bots| == NumBuckets(pivots)
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
