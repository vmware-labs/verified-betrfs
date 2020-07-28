  method FixedSizeInsert<V>(linear inout self: FixedSizeLinearHashMap, key: uint64, value: V)
  returns (replaced: Option<V>)

    requires FixedSizeInv(self)
    requires self.count as nat < |self.storage| - 1
    ensures (
      && FixedSizeInv(self)
      && self.contents == old(self).contents[key := Some(value)]
      && (key in old(self).contents ==> replaced == old(self).contents[key])
      && (replaced.Some? ==> key in old(self).contents)
      && (key !in old(self).contents ==> replaced.None?)
      && |self.storage| == |old(self).storage|)
  {
    var slotIdx := Probe(self, key);
    var probeRes := LemmaProbeResult(self, key);

    assert slotIdx == probeRes.slotIdx;
    ghost var probeStartSlotIdx := probeRes.startSlotIdx;
    ghost var probeSkips := probeRes.ghostSkips;

    var replacedItem := seq_get(self.storage, slotIdx);
    seq_set(linear inout self.storage, slotIdx, Entry(key, value));

    replaced := None;
    if replacedItem.Empty? {
      var newCount := self.count + 1;
      Assign(inout self.count, newCount);
    } else if replacedItem.Value? {
      replaced := Some(replacedItem.value);
    }

    forall explainedKey | explainedKey in self.contents
    ensures exists skips :: SlotExplainsKey(self.storage, skips, explainedKey)
    {
      if key == explainedKey {
        assert SlotExplainsKey(self.storage, probeSkips as nat, key); // observe
      } else {
        var oldSkips :| SlotExplainsKey(old(self).storage, oldSkips, explainedKey);
        assert SlotExplainsKey(self.storage, oldSkips, explainedKey); // observe
      }
    }

    forall slot | ValidSlot(|self.storage|, slot) && self.storage[slot.slot].Entry?
    ensures && var item := self.storage[slot.slot];
            && self.contents[item.key] == Some(item.value)
    {
      var item := self.storage[slot.slot];
      if slot != Slot(slotIdx as nat) {
        if item.key == key {
          assert TwoNonEmptyValidSlotsWithSameKey(self.storage, slot, Slot(slotIdx as nat)); // observe
          assert SameSlot(|self.storage|, slot, Slot(slotIdx as nat)); // observe
          assert false;
        }
      }
    }
    forall slot | ValidSlot(|self.storage|, slot) && self.storage[slot.slot].Tombstone?
    ensures && var item := self.storage[slot.slot];
            && self.contents[item.key].None?
    {
      var item := self.storage[slot.slot];
      if slot != Slot(slotIdx as nat) {
        if item.key == key {
          assert TwoNonEmptyValidSlotsWithSameKey(self.storage, slot, Slot(slotIdx as nat)); // observe
          assert SameSlot(|self.storage|, slot, Slot(slotIdx as nat)); // observe
          assert false;
        }
      }
    }
  }

