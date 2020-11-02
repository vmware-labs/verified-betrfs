include "../Base/KeyType.s.dfy"
include "../Base/Message.i.dfy"
include "../Base/total_order.i.dfy"

module MapSeqs {
  import opened KeyType
  import opened ValueMessage
  import opened Sequences
  import opened Lexicographic_Byte_Order
  import opened Maps
  import opened Options

  protected function map_of_seqs(keys: seq<Key>, msgs: seq<Message>) : map<Key, Message>
  requires |keys| == |msgs|
  {
    if |keys| == 0 then
      map[]
    else
      map_of_seqs(DropLast(keys), DropLast(msgs))[Last(keys) := Last(msgs)]
  }

  function maximumKey(b: set<Key>) : Option<Key>
  {
    var m := Lexicographic_Byte_Order.maximumOpt(b);
    if m.Some? then
      assert |m.value| <= KeyType.MaxLen() as nat;
      var k: Key := m.value;
      Some(k)
    else
      None
  } 

  datatype SeqPair = SeqPair(keys: seq<Key>, msgs: seq<Message>)

  protected function seqs_of_map(m: map<Key, Message>) : (res : SeqPair)
  ensures |res.keys| == |res.msgs|
  {
    var keyOpt := maximumKey(m.Keys);
    match keyOpt {
      case None => SeqPair([], [])
      case Some(key) => (
        var m' := MapRemove1(m, key);
        var SeqPair(keys', msgs') := seqs_of_map(m');
        SeqPair(keys' + [key], msgs' + [m[key]])
      )
    }
  }

  lemma IsStrictlySorted_seqs_of_map(m: map<Key, Message>)
  ensures IsStrictlySorted(seqs_of_map(m).keys)
  {
    var keyOpt := maximumKey(m.Keys);
    match keyOpt {
      case None => {
        reveal_IsStrictlySorted();
      }
      case Some(key) => {
        var m' := MapRemove1(m, key);
        var SeqPair(keys', msgs') := seqs_of_map(m');
        IsStrictlySorted_seqs_of_map(m');
        StrictlySortedAugment(keys', key);
      }
    }
  }

  lemma MapMapsIndex(keys: seq<Key>, msgs: seq<Message>, i: int)
  requires |keys| == |msgs|
  requires 0 <= i < |keys|
  requires IsStrictlySorted(keys)
  ensures keys[i] in map_of_seqs(keys, msgs)
  ensures map_of_seqs(keys, msgs)[keys[i]] == msgs[i]
  {
    if i == |keys| - 1 {
    } else {
      reveal_IsStrictlySorted();
      //calc {
      //  msgs[i];
      //  {
          MapMapsIndex(DropLast(keys), DropLast(msgs), i);
      //  }
      //  map_of_seqs(DropLast(keys), DropLast(msgs))[keys[i]];
      //  map_of_seqs(DropLast(keys), DropLast(msgs))[Last(keys) := Last(msgs)][keys[i]];
      //  map_of_seqs(keys, msgs)[keys[i]];
      //}
    }
  }

  lemma map_of_seqs_of_seqs_of_map(m: map<Key, Message>)
  ensures
    var a := seqs_of_map(m);
    map_of_seqs(a.keys, a.msgs) == m
  {
    assume false;
  }

  lemma GetIndex(keys: seq<Key>, msgs: seq<Message>, key: Key)
  returns (i: int)
  requires |keys| == |msgs|
  requires key in map_of_seqs(keys, msgs)
  ensures 0 <= i < |keys|
  ensures keys[i] == key
  ensures msgs[i] == map_of_seqs(keys, msgs)[key]
  {
    if keys[|keys| - 1] == key {
      i := |keys| - 1;
    } else {
      i := GetIndex(DropLast(keys), DropLast(msgs), key);
    }
  }

  lemma GetIndexOfVal(keys: seq<Key>, msgs: seq<Message>, key: Key, m: Message)
  returns (i: int)
  requires |keys| == |msgs|
  requires key in map_of_seqs(keys, msgs)
  requires map_of_seqs(keys, msgs)[key] == m
  ensures 0 <= i < |keys|
  ensures keys[i] == key
  ensures msgs[i] == m
  {
    if keys[|keys| - 1] == key && msgs[|msgs| - 1] == m {
      i := |keys| - 1;
    } else {
      i := GetIndex(DropLast(keys), DropLast(msgs), key);
    }
  }

  lemma lemma_maxkey_not_in_map_of_seqs_drop_last(keys: seq<Key>, msgs: seq<Message>)
  requires |keys| == |msgs|
  requires IsStrictlySorted(keys)
  requires |keys| > 0
  ensures keys[|keys| - 1] !in map_of_seqs(DropLast(keys), DropLast(msgs))
  {
    if keys[|keys| - 1] in map_of_seqs(DropLast(keys), DropLast(msgs)) {
      var i := GetIndex(DropLast(keys), DropLast(msgs), keys[|keys| - 1]);
      reveal_IsStrictlySorted();
    }
  }

  lemma SeqsEqOfMapsEq(
      keys: seq<Key>, msgs: seq<Message>,
      keys': seq<Key>, msgs': seq<Message>)
  requires IsStrictlySorted(keys)
  requires IsStrictlySorted(keys')
  requires |keys| == |msgs|
  requires |keys'| == |msgs'|
  requires map_of_seqs(keys, msgs) == map_of_seqs(keys', msgs')
  ensures keys == keys'
  ensures msgs == msgs'
  {
    if |keys| == 0 {
      assert map_of_seqs(keys', msgs')
          == map_of_seqs(keys, msgs)
          == map[];
      if 0 < |keys'| {
        MapMapsIndex(keys', msgs', 0);
        assert false;
      }
    } else {
      var maxkey := Last(keys);
      var maxval := Last(msgs);

      MapMapsIndex(keys, msgs, |keys| - 1);
      var i := GetIndex(keys', msgs', maxkey);

      assert i == |keys'| - 1 by {
        if i < |keys'| - 1 {
          var maxkey' := Last(keys');
          MapMapsIndex(keys', msgs', |keys'| - 1);
          var j := GetIndex(keys, msgs, maxkey');
          reveal_IsStrictlySorted();
        }
      }

      assert Last(keys) == Last(keys');

      assert IsStrictlySorted(DropLast(keys)) by { reveal_IsStrictlySorted(); }
      assert IsStrictlySorted(DropLast(keys')) by { reveal_IsStrictlySorted(); }

      calc {
        map_of_seqs(DropLast(keys), DropLast(msgs));
        {
          lemma_maxkey_not_in_map_of_seqs_drop_last(keys, msgs);
        }
        MapRemove1(map_of_seqs(keys, msgs), maxkey);
        MapRemove1(map_of_seqs(keys', msgs'), maxkey);
        {
          lemma_maxkey_not_in_map_of_seqs_drop_last(keys', msgs');
        }
        map_of_seqs(DropLast(keys'), DropLast(msgs'));
      }

      SeqsEqOfMapsEq(
          DropLast(keys), DropLast(msgs),
          DropLast(keys'), DropLast(msgs'));

      calc {
        keys;
        DropLast(keys) + [Last(keys)];
        DropLast(keys') + [Last(keys')];
        keys';
      }

      calc {
        msgs;
        DropLast(msgs) + [Last(msgs)];
        DropLast(msgs') + [Last(msgs')];
        msgs';
      }
    }
  }

  lemma MapOfEmptySeq()
  ensures map_of_seqs([], []) == map[]
  ensures IsStrictlySorted([])
  {
    reveal_IsStrictlySorted();
  }

  lemma map_of_seqs_push_back(
      keys: seq<Key>, msgs: seq<Message>, key: Key, msg: Message)
  requires |keys| == |msgs|
  requires IsStrictlySorted(keys)
  requires forall k | k in keys :: lt(k, key)
  ensures map_of_seqs(keys + [key], msgs + [msg])
       == map_of_seqs(keys, msgs)[key := msg]
  ensures key !in map_of_seqs(keys, msgs)
  {
    //reveal_BucketMapOfSeq();
    if key in map_of_seqs(keys, msgs) {
      var i := GetIndex(keys, msgs, key);
      assert lt(keys[i], key);
    }
  }

  lemma map_of_seqs_pop_front(
      keys: seq<Key>, msgs: seq<Message>, i: int)
  requires |keys| == |msgs|
  requires 0 <= i < |keys|
  requires IsStrictlySorted(keys)
  ensures map_of_seqs(keys[i+1..], msgs[i+1..])[keys[i] := msgs[i]]
       == map_of_seqs(keys[i..], msgs[i..])
  ensures keys[i] !in map_of_seqs(keys[i+1..], msgs[i+1..])
  {
    var a := map_of_seqs(keys[i+1..], msgs[i+1..])[keys[i] := msgs[i]];
    var b := map_of_seqs(keys[i..], msgs[i..]);
    forall k | k in a
    ensures k in b
    ensures a[k] == b[k]
    {
      reveal_IsStrictlySorted();
      if k == keys[i] {
        MapMapsIndex(keys[i..], msgs[i..], 0);
        assert a[k] == b[k];
      } else {
        var j := GetIndex(keys[i+1..], msgs[i+1..], k);
        MapMapsIndex(keys[i..], msgs[i..], j+1);
        assert a[k] == b[k];
      }
    }
    forall k | k in b
    ensures k in a
    {
      reveal_IsStrictlySorted();
      var j := GetIndex(keys[i..], msgs[i..], k);
      if j > 0 {
        MapMapsIndex(keys[i+1..], msgs[i+1..], j-1);
      } else {
      }
    }
    if keys[i] in map_of_seqs(keys[i+1..], msgs[i+1..]) {
      var j := GetIndex(keys[i+1..], msgs[i+1..], keys[i]);
      reveal_IsStrictlySorted();
      assert false;
    }
  }

  lemma map_union_of_seq_concat(
      keys1: seq<Key>, msgs1: seq<Message>,
      keys2: seq<Key>, msgs2: seq<Message>)
  requires |keys1| == |msgs1|
  requires |keys2| == |msgs2|
  requires IsStrictlySorted(keys1 + keys2)
  ensures IsStrictlySorted(keys1)
  ensures IsStrictlySorted(keys2)
  ensures map_of_seqs(keys1, msgs1).Keys !! map_of_seqs(keys2, msgs2).Keys
  ensures MapDisjointUnion(map_of_seqs(keys1, msgs1), map_of_seqs(keys2, msgs2))
      == map_of_seqs(keys1 + keys2, msgs1 + msgs2)
  {
    assume false; // TODO
  }

  lemma eq_map_of_seqs(keys: seq<Key>, msgs: seq<Message>, bmap: map<Key, Message>)
  requires IsStrictlySorted(keys)
  requires Set(keys) == bmap.Keys
  requires |keys| == |msgs|
  requires forall i | 0 <= i < |keys| :: bmap[keys[i]] == msgs[i]
  ensures bmap == map_of_seqs(keys, msgs)
  {
    assume false; // TODO
  }

  lemma key_sets_eq(keys: seq<Key>, msgs: seq<Message>)
  requires |keys| == |msgs|
  ensures Set(keys) == map_of_seqs(keys, msgs).Keys
  {
  }
}
