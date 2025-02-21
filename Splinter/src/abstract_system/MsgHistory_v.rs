// Copyright 2018-2024 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, University of Washington
// SPDX-License-Identifier: BSD-2-Clause
use builtin_macros::*;
use builtin::*;
use vstd::{map::*,set::*};

use crate::spec::KeyType_t::*;
use crate::spec::Messages_t::*;
use crate::abstract_system::StampedMap_v::*;

verus! {

/// A KeyedMessage stores a "key" to perform the operation in the stored
/// "message" on.
pub struct KeyedMessage { 
  pub key: Key, 
  pub message: Message 
}

// (Tenzin): It seems that given MsgHistory is required to be contiguous,
// reusing a FloatingSeq of the appropriate type would provide better
// type reusage.

/// A contiguous log of kv-store command messages (keyed by LSN).
/// Stores requests from seq_start <= LSN < seq_end.
#[verifier::ext_equal]
pub struct MsgHistory { 
  /// The messages stored in this history. Stored as key-value pairs,
  /// where key is the LSN of the operation, and KeyedMessage stores
  /// the operation to perform.
  pub msgs: Map<LSN, KeyedMessage>,
  /// The first LSN in this MsgHistory.
  pub seq_start: LSN, 
  /// The first LSN *past the end* of this MsgHistory.
  pub seq_end: LSN 
}

impl MsgHistory {
  pub open spec(checked) fn wf(self) -> bool {
    &&& self.seq_start <= self.seq_end
    &&& self.contains_exactly(self.msgs.dom())
  }

  // Call this instead of using `==` when checking/asserting that
  pub open spec(checked) fn ext_equal(self, other: MsgHistory) -> bool {
    &&& self.msgs =~= other.msgs
    &&& self.seq_start == other.seq_start
    &&& self.seq_end == other.seq_end
  }

  pub proof fn ext_equal_is_equality()
    ensures forall |a: MsgHistory, b: MsgHistory|
      a.ext_equal(b) == (a == b)
  {
  }

  pub open spec(checked) fn contains(self, lsn: LSN) -> bool {
    self.seq_start <= lsn < self.seq_end
  }

  pub open spec fn contains_key(self, key: Key) -> bool
  recommends
    self.wf(),
  {
    exists |lsn| #![auto] self.msgs[lsn].key == key
  }

  pub open spec(checked) fn contains_exactly(self, lsns: Set<LSN>) -> bool {
    forall |lsn| lsns.contains(lsn) <==> self.contains(lsn)
  }

  pub open spec(checked) fn is_empty(self) -> bool {
    self.seq_start == self.seq_end
  }

  pub open spec(checked) fn len(self) -> nat
  recommends
    self.wf()
  {
    (self.seq_end - self.seq_start) as nat
  }

  pub open spec(checked) fn can_follow(self, lsn: LSN) -> bool {
    self.seq_start == lsn
  }

  pub open spec(checked) fn can_concat(self, other: MsgHistory) -> bool {
    other.can_follow(self.seq_end)
  }

  pub open spec(checked) fn concat(self, other: MsgHistory) -> MsgHistory 
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
    &&& (forall |x| result.contains(x) <==> (self.contains(x) || other.contains(x)))
    &&& (other.is_empty() ==> result == self)
  }),
  {
    let result = self.concat(other);
    if other.is_empty() {
      assert_maps_equal!(result.msgs, self.msgs);
    }
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
      &&& (forall |x| result.contains(x) <==> (_self.contains(x) || other.contains(x)))
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
      &&& (forall |x| result.contains(x) <==> (_self.contains(x) || other.contains(x)))
      &&& (other.is_empty() ==> result == _self)
    }
    by
    {
      _self.concat_lemma(other);
    }
  }

  pub open spec(checked) fn can_discard_to(self, lsn: LSN) -> bool {
    self.seq_start <= lsn <= self.seq_end
  }

  /// Returns this[start, lsn). (Slice off right side).
  pub open spec(checked) fn discard_recent(self, lsn: LSN) -> MsgHistory 
    recommends self.can_discard_to(lsn)
  {
    let keepMap = Map::new(
      |k: nat| self.seq_start <= k < lsn,
      |k: nat| self.msgs[k],
    );
    MsgHistory{ msgs: keepMap, seq_start: self.seq_start, seq_end: lsn }
  }

  // Tenzin: I type these so much it's much easier to write and read shorthand
  pub open spec(checked) fn _dr(self, lsn: LSN) -> MsgHistory
    recommends self.can_discard_to(lsn)
  {
    self.discard_recent(lsn)
  }

  /// Returns a StampedMap formed by applying the operations in self (MsgHistory)
  /// to the StampedMap "orig".
  pub open spec fn apply_to_stamped_map(self, orig: StampedMap) -> StampedMap 
    recommends
        self.can_follow(orig.seq_end),
    decreases self.len() when self.wf()
  {
    if self.is_empty() {
      orig
    } else {
      // We define the application of a MsgHistory to a StampedMap recursively.

      // First we pop off the last log entry and apply the prefix log to the
      // stamped map.
      let last_lsn = (self.seq_end - 1) as nat;
      let sub_map = self.discard_recent(last_lsn).apply_to_stamped_map(orig);

      // Then we apply the last entry in the log to the StampedMap.
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
  // 'ensures' line in the spec(checked) definition in Dafny. Perhaps we should have an
  // "invariant" clause in spec(checked) proofs that creates this lemma on the side?
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

  pub open spec(checked) fn discard_old(self, lsn: LSN) -> MsgHistory
    recommends self.can_discard_to(lsn)
  {
    let keepMap = Map::new(
      |k: nat| lsn <= k < self.seq_end,
      |k: nat| self.msgs[k],
    );
    MsgHistory{ msgs: keepMap, seq_start: lsn, seq_end: self.seq_end }
  }

  pub open spec(checked) fn _do(self, lsn: LSN) -> MsgHistory
    recommends self.can_discard_to(lsn)
  {
    self.discard_old(lsn)
  }

  pub open spec(checked) fn maybe_discard_old(self, lsn: LSN) -> MsgHistory
  recommends
    self.wf(),
    lsn <= self.seq_end,
  {
    if self.seq_start <= lsn {
      self.discard_old(lsn)
    } else {
      self
    }
  }

  // TODO(tenzin): this isn't really needed
  pub proof fn discard_order_is_commutative(self, start: LSN, end: LSN)
    requires
      start <= end,
      self.can_discard_to(start),
      self.can_discard_to(end),
    ensures
      self.discard_old(start).discard_recent(end) 
        == self.discard_recent(end).discard_old(start)
  {
    let left = self.discard_old(start).discard_recent(end);
    let right = self.discard_recent(end).discard_old(start);
    assert(left.ext_equal(right));
  }

  pub proof fn added_slices_union(self, middle: LSN)
    requires
      self.wf(),
      self.can_discard_to(middle),
    ensures
      // history[:middle] + history[middle:] = history
      self.discard_recent(middle).concat(self.discard_old(middle))
        == self,
    {
      let other = self.discard_recent(middle).concat(self.discard_old(middle));
      assert(self.ext_equal(other));
    }

  // Returns `true` iff the given MsgHistory is an exact slice of MsgHistory
  // within self (values must match at each LSN).
  pub open spec(checked) fn includes_subseq(self, subseq: MsgHistory) -> bool
  recommends
      self.wf(),
      subseq.wf(),
  {
    &&& self.seq_start <= subseq.seq_start
    &&& subseq.seq_end <= self.seq_end
    &&& forall |lsn| #![auto] subseq.contains(lsn) ==> self.contains(lsn) && self.msgs[lsn] === subseq.msgs[lsn]
  }

  pub open spec(checked) fn empty_history_at(lsn: LSN) -> MsgHistory {
    MsgHistory{ msgs: map![], seq_start: lsn, seq_end: lsn }
  }

  pub open spec(checked) fn singleton_at(lsn: LSN, msg: KeyedMessage) -> MsgHistory {
    MsgHistory{ msgs: map![lsn => msg], seq_start: lsn, seq_end: lsn + 1 }
  }
  
  pub open spec(checked) fn map_plus_history(stamped_map: StampedMap, history: MsgHistory) -> StampedMap
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
      Self::map_plus_history(stamped_map, history).seq_end 
        == stamped_map.seq_end + history.len(),
  {
    history.apply_to_stamped_map_wf_lemma(stamped_map);
    Self::map_plus_history_seq_end_lemma(stamped_map, history);
  }

  pub proof fn map_plus_history_forall_lemma()
    ensures
      forall |stamped_map: StampedMap, history: MsgHistory|
      (
        stamped_map.value.wf()
        && history.wf()
        && history.can_follow(stamped_map.seq_end)
      ) ==>
      {
        &&& (#[trigger] Self::map_plus_history(stamped_map, history)).value.wf()
        &&& Self::map_plus_history(stamped_map, history).seq_end == stamped_map.seq_end + history.len()
      }
  {
    assert forall |stamped_map: StampedMap, history: MsgHistory|
      (
        stamped_map.value.wf()
        && history.wf()
        && history.can_follow(stamped_map.seq_end)
      ) implies
       ((#[trigger] Self::map_plus_history(stamped_map, history)).value.wf()
       && Self::map_plus_history(stamped_map, history).seq_end == stamped_map.seq_end + history.len())
    by
    {
      // When this assert is commented out, it complains that precondition to 295 isn't met, but
      // when left in it seems to trigger something and then it says 295 is fine.
      // assert(history.can_follow(stamped_map.seq_end));
      Self::map_plus_history_lemma(stamped_map, history);
      Self::map_plus_history_seq_end_lemma(stamped_map, history);
//      assert(Self::map_plus_history(stamped_map, history).seq_end == stamped_map.seq_end + history.len());
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
