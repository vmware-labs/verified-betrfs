#![allow(unused_imports)]
use builtin::*;

use builtin_macros::*;

use vstd::prelude::*;
use crate::betree::Buffer_v::*;
use crate::spec::Messages_t::*;
use crate::spec::KeyType_t::*;
use crate::coordination_layer::StampedMap_v::*;
use crate::coordination_layer::MsgHistory_v::*;

verus! {
pub struct Memtable {
    pub buffer: Buffer,
    pub seq_end: LSN
}

impl Memtable {
    pub open spec fn query(self, key: Key) -> Message {
        self.buffer.query(key)
    }

    pub open spec fn apply_put(self, km: KeyedMessage) -> Memtable {
        Memtable{ 
            buffer: Buffer{
                map: self.buffer.map.insert(km.key, km.message.merge(self.query(km.key)))
            },
            seq_end: self.seq_end + 1
        }
    }

    pub open spec fn apply_puts(self, puts: MsgHistory) -> Memtable
        recommends puts.wf(), puts.seq_start == self.seq_end
        decreases puts.seq_end, 1nat
    {
        decreases_when(puts.wf());
        if puts.is_empty() {
            self
        } else {
            let last_lsn = (puts.seq_end - 1) as nat;
            self.apply_puts(puts.discard_recent(last_lsn)).apply_put(puts.msgs[last_lsn])
        }
    }

    pub open spec fn empty_memtable(lsn: LSN) -> Memtable {
        Memtable{ 
            buffer: Buffer::empty_buffer(),
            seq_end: lsn
        }
    }

    pub open spec fn drain(self) -> Memtable {
        Self::empty_memtable(self.seq_end)
    }

    pub open spec fn is_empty(self) -> bool {
        self.buffer.map.dom().len() == 0
    }

} // end impl Memtable

} // end verus!