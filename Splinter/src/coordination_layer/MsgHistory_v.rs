#![allow(unused_imports)]

use builtin_macros::*;
use builtin::*;
use crate::pervasive::{*,map::*,set::*};

use crate::spec::Messages_t::*;
use crate::spec::TotalKMMap_t::*;
use crate::coordination_layer::StampedMap_v::*;

verus! {

pub struct KeyedMessage { 
  pub key: Key, 
  pub message: Message 
}

pub struct MsgHistory { 
  pub msgs: Map<LSN, KeyedMessage>, 
  pub seq_start: LSN, 
  pub seq_end: LSN 
}

impl MsgHistory {
  pub open spec fn wf(self) -> bool {
    &&& self.seq_start <= self.seq_end
    &&& self.contains_exactly(self.msgs.dom())
  }

  pub open spec fn contains(self, lsn: LSN) -> bool {
    self.seq_start <= lsn < self.seq_end
  }

  pub open spec fn contains_key(self, key: Key) -> bool {
    exists |lsn| #![auto] self.msgs[lsn].key == key
  }

  pub open spec fn contains_exactly(self, lsns: Set<LSN>) -> bool {
    forall |lsn| lsns.contains(lsn) <==> self.contains(lsn)
  }

  pub open spec fn is_empty(self) -> bool {
    self.seq_start == self.seq_end
  }

  pub open spec fn len(self) -> int {
    self.seq_end - self.seq_start
  }

  pub open spec fn can_follow(self, lsn: LSN) -> bool {
    self.seq_start == lsn
  }

  pub open spec fn can_concat(self, other: MsgHistory) -> bool {
    other.can_follow(self.seq_end)
  }

  pub open spec fn concat(self, other: MsgHistory) -> MsgHistory 
    recommends self.can_concat(other)
  {
    MsgHistory{ 
      msgs: self.msgs.union_prefer_right(other.msgs), 
      seq_start: self.seq_start, 
      seq_end: other.seq_end 
    }
  }

  // TODO(verus): in dafny this was three lines of ensures tacked onto concat, and the proof was free
  // because we didn't need explicit extensionality.
  pub proof fn concat_lemma(self, other: MsgHistory)
  requires
    self.wf(),
    other.wf(),
    self.can_concat(other),
  ensures ({
    let result = self.concat(other);
    &&& result.wf()
    &&& forall(|x| result.contains(x) <==> (self.contains(x) || other.contains(x)))
    &&& (other.is_empty() ==> result == self)
  }),
  {
    let result = self.concat(other);
    if other.is_empty() {
      assert_maps_equal!(result.msgs, self.msgs);
    }
  }

  // TODO(tenzinhl): Delete this. This lemma was used to figure out that
  // we were missing an extensionality argument that Dafny was automatically
  // getting.
  pub proof fn concat_property_1(x: MsgHistory, y: MsgHistory, lsn: LSN)
  requires
    x.wf(),
    y.wf(),
    y.can_discard_to(lsn),
    x.can_concat(y),
  ensures
    x.concat(y.discard_recent(lsn)) == x.concat(y).discard_recent(lsn)
  {
    assert_maps_equal!(
      x.concat(y.discard_recent(lsn)).msgs,
      x.concat(y).discard_recent(lsn).msgs
    );
  }

  pub proof fn concat_forall_lemma()
  ensures
    forall |_self: MsgHistory, other: MsgHistory|
    {
      &&& _self.wf()
      &&& other.wf()
      &&& _self.can_concat(other)
    } ==> {
      let result = #[trigger] _self.concat(other);
      &&& result.wf()
      &&& forall(|x| result.contains(x) <==> (_self.contains(x) || other.contains(x)))
      &&& (other.is_empty() ==> result == _self)
    }
  {
    assert forall |_self: MsgHistory, other: MsgHistory|
    {
      &&& _self.wf()
      &&& other.wf()
      &&& _self.can_concat(other)
    } implies {
      let result = #[trigger] _self.concat(other);
      &&& result.wf()
      &&& forall(|x| result.contains(x) <==> (_self.contains(x) || other.contains(x)))
      &&& (other.is_empty() ==> result == _self)
    }
    by
    {
      _self.concat_lemma(other);
    }
  }

  pub open spec fn can_discard_to(self, lsn: LSN) -> bool {
    self.seq_start <= lsn <= self.seq_end
  }

  pub open spec fn discard_recent(self, lsn: LSN) -> MsgHistory 
    recommends self.can_discard_to(lsn)
  {
    let keepMap = Map::new(
      |k: nat| self.seq_start <= k < lsn,
      |k: nat| self.msgs[k],
    );
    MsgHistory{ msgs: keepMap, seq_start: self.seq_start, seq_end: lsn }
  }

  pub open spec fn apply_to_stamped_map(self, orig: StampedMap) -> StampedMap 
    recommends 
      self.wf(),  // TODO(verus): check if decreases_when implies recommends
      self.can_follow(orig.seq_end),
    decreases
      self.len(),
  {
    decreases_when(self.wf());
    if self.is_empty() {
      orig
    } else {
      let last_lsn = (self.seq_end - 1) as nat;
      let sub_map = self.discard_recent(last_lsn).apply_to_stamped_map(orig);
      let key = self.msgs[last_lsn].key;
      let new_message = self.msgs[last_lsn].message;
      let old_message = sub_map.value[key];
      let new_value = sub_map.value.insert(key, old_message.merge(new_message));
      Stamped{ value: new_value, seq_end: sub_map.seq_end + 1 }
    }
  }

  // Originally was going to write proof to show that applying to stamped map
  // doesn't change domains, but it look like intended method to prove was through
  // the fact that TotalKMMaps should all have same domain, so working on that
  // instead.
  pub proof fn apply_to_stamped_map_wf_lemma(self, orig: StampedMap)
    requires
      orig.value.wf(),
      self.wf(),
      self.can_follow(orig.seq_end),
    ensures
      self.apply_to_stamped_map(orig).value.wf(),
    decreases self.len()
  {
    if !self.is_empty() {
      let last_lsn = (self.seq_end - 1) as nat;
      let sub_map = self.discard_recent(last_lsn).apply_to_stamped_map(orig);
      self.discard_recent(last_lsn).apply_to_stamped_map_wf_lemma(orig);
      sub_map.value.insert_lemma();
    }
  }

  // TODO(verus): This 14 lines of proof is all basically free with the
  // 'ensures' line in the spec definition in Dafny. Perhaps we should have an
  // "invariant" clause in spec proofs that creates this lemma on the side?
  // And then there's the question of how to invoke the lemma; we'd like it to
  // get triggered automatically with mentions of the definition.
  //
  // Could be side-stepped by just changing the substitution in `apply_to_stamped_map`
  // when creating the final Stamped{} to be `self.seq_end + 1`
  pub proof fn apply_to_stamped_map_length_lemma(self, orig: StampedMap)
    requires
      self.wf(),
      self.can_follow(orig.seq_end)
    ensures
      self.apply_to_stamped_map(orig).seq_end == orig.seq_end + self.len()
    decreases
      self.len()
  {
    if !self.is_empty() {
      let last_lsn = (self.seq_end - 1) as nat;
      self.discard_recent(last_lsn).apply_to_stamped_map_length_lemma(orig);
    }
  }

  pub open spec fn discard_old(self, lsn: LSN) -> MsgHistory
    recommends self.can_discard_to(lsn)
  {
    let keepMap = Map::new(
      |k: nat| lsn <= k < self.seq_end,
      |k: nat| self.msgs[k],
    );
    MsgHistory{ msgs: keepMap, seq_start: lsn, seq_end: self.seq_end }
  }

  pub open spec fn maybe_discard_old(self, lsn: LSN) -> MsgHistory
    recommends lsn <= self.seq_end
  {
    if self.seq_start <= lsn {
      self.discard_old(lsn)
    } else {
      self
    }
  }

  pub open spec fn includes_subseq(self, subseq: MsgHistory) -> bool {
    &&& self.seq_start <= subseq.seq_start
    &&& subseq.seq_end <= self.seq_end
    &&& forall |lsn| #![auto] subseq.contains(lsn) ==> self.contains(lsn) && self.msgs[lsn] === subseq.msgs[lsn]
  }

  pub open spec fn empty_history_at(lsn: LSN) -> MsgHistory {
    MsgHistory{ msgs: Map::empty(), seq_start: lsn, seq_end: lsn }
  }
  
  pub open spec fn singleton_at(lsn: LSN, msg: KeyedMessage) -> MsgHistory {
    MsgHistory{ msgs: Map::empty(), seq_start: lsn, seq_end: lsn }
  }
  
  pub open spec fn map_plus_history(stamped_map: StampedMap, history: MsgHistory) -> StampedMap
    recommends
      stamped_map.value.wf(),
      history.wf(),
      history.can_follow(stamped_map.seq_end),
  {
    history.apply_to_stamped_map(stamped_map)
  }

  pub proof fn map_plus_history_lemma(stamped_map: StampedMap, history: MsgHistory)
    requires
      stamped_map.value.wf(),
      history.wf(),
      history.can_follow(stamped_map.seq_end),
    ensures
      Self::map_plus_history(stamped_map, history).value.wf(),
  {
    history.apply_to_stamped_map_wf_lemma(stamped_map);
  }

  pub proof fn map_plus_history_forall_lemma()
    ensures
      forall |stamped_map: StampedMap, history: MsgHistory|
      (
        stamped_map.value.wf()
        && history.wf()
        && history.can_follow(stamped_map.seq_end)
      ) ==>
      (#[trigger] Self::map_plus_history(stamped_map, history)).value.wf()
  {
    assert forall |stamped_map: StampedMap, history: MsgHistory|
      (
        stamped_map.value.wf()
        && history.wf()
        && history.can_follow(stamped_map.seq_end)
      ) implies #[trigger]
        Self::map_plus_history(stamped_map, history).value.wf()
    by
    {
      Self::map_plus_history_lemma(stamped_map, history);
    }
  }

  // TODO(tenzinhl): include this in the map_plus_history_forall lemma
  pub proof fn map_plus_history_seq_end_lemma(stamped_map: StampedMap, history: MsgHistory)
    requires
      stamped_map.value.wf(),
      history.wf(),
      history.can_follow(stamped_map.seq_end),
    ensures
      history.apply_to_stamped_map(stamped_map).seq_end == stamped_map.seq_end + history.len(),
  {
    history.apply_to_stamped_map_length_lemma(stamped_map);
  }
}
}
