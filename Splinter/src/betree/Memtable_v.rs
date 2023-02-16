#![allow(unused_imports)]
use builtin::*;

use builtin_macros::*;

use crate::pervasive::prelude::*;
use crate::betree::Buffers_v::*;
use crate::spec::Messages_t::*;
use crate::spec::TotalKMMap_t::*;
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

    pub open spec fn apply_puts(self, km: KeyedMessage) -> Memtable {
        Memtable{ 
            buffer: Buffer{
                map: self.buffer.map.insert(km.key, km.message.merge(self.query(km.key)))
            },
            seq_end: self.seq_end + 1
        }
    }

    pub open spec fn empty_memtable(self, lsn: LSN) -> Memtable {
        Memtable{ 
            buffer: Buffer{
                map: Map::empty()
            },
            seq_end: lsn
        }
    }

    pub open spec fn drain(self) -> Memtable {
        self.empty_memtable(self.seq_end)
    }

    pub open spec fn is_empty(self) -> bool {
        self.buffer.map.dom().len() == 0
    }

} // end impl Memtable

} // end verus!