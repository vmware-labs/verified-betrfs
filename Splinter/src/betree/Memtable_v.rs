#![allow(unused_imports)]
use builtin::*;

use builtin_macros::*;

use vstd::prelude::*;
use vstd::map::*;

use crate::betree::Buffer_v::*;
use crate::spec::Messages_t::*;
use crate::spec::KeyType_t::*;
use crate::abstract_system::StampedMap_v::*;
use crate::abstract_system::MsgHistory_v::*;

verus! {
pub struct Memtable {
    pub buffer: Buffer,
    pub seq_end: LSN
}

impl Memtable {
    pub open spec(checked) fn query(self, key: Key) -> Message {
        self.buffer.query(key)
    }

    pub open spec(checked) fn apply_put(self, km: KeyedMessage) -> Memtable {
        Memtable{ 
            buffer: Buffer{
                map: self.buffer.map.insert(km.key, self.query(km.key).merge(km.message))
            },
            seq_end: self.seq_end + 1
        }
    }

    pub open spec(checked) fn apply_puts(self, puts: MsgHistory) -> Memtable
        recommends puts.wf(), puts.can_follow(self.seq_end)
        decreases puts.seq_end when puts.wf()
    {
        if puts.is_empty() {
            self
        } else {
            let last_lsn = (puts.seq_end - 1) as nat;
            self.apply_puts(puts.discard_recent(last_lsn)).apply_put(puts.msgs[last_lsn])
        }
    }

    pub proof fn apply_puts_end(self, puts: MsgHistory)
        requires puts.wf(), puts.can_follow(self.seq_end)
        ensures self.apply_puts(puts).seq_end == puts.seq_end
        decreases puts.len()
    {
        if 0 < puts.len() {
            let last_lsn = (puts.seq_end - 1) as nat;
            self.apply_puts_end(puts.discard_recent(last_lsn));
        }
    }

    pub proof fn apply_puts_additive(self, puts1: MsgHistory, puts2: MsgHistory)
        requires puts1.wf(), puts2.wf(),
            puts1.can_follow(self.seq_end),
            puts2.can_follow(puts1.seq_end)
        ensures self.apply_puts(puts1).apply_puts(puts2) == self.apply_puts(puts1.concat(puts2))
        decreases puts1.len() + puts2.len()
    {
        MsgHistory::concat_forall_lemma();
        if puts2.len() > 0 {
            let last_lsn = (puts2.seq_end - 1) as nat;
            self.apply_puts_additive(puts1, puts2.discard_recent(last_lsn));
            assert_maps_equal!(
                puts1.concat(puts2).discard_recent(last_lsn).msgs,
                puts1.concat(puts2.discard_recent(last_lsn)).msgs
            );
        }
    }

    pub open spec(checked) fn empty_memtable(lsn: LSN) -> Memtable {
        Memtable{ 
            buffer: Buffer::empty(),
            seq_end: lsn
        }
    }

    pub open spec(checked) fn drain(self) -> Memtable {
        Self::empty_memtable(self.seq_end)
    }

    pub open spec(checked) fn is_empty(self) -> bool {
        self.buffer == Buffer::empty()
        // Note(Jialin): not suited here bc if map is not finite len has no meaning
        // we can write it as the following
        // &&& self.buffer.map.dom().finite()
        // &&& self.buffer.map.dom().len() == 0 
    }

} // end impl Memtable

} // end verus!