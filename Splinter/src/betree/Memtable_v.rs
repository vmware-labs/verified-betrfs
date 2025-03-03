// Copyright 2018-2024 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, University of Washington
// SPDX-License-Identifier: BSD-2-Clause
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

#[verifier::ext_equal]
pub struct Memtable {
    pub buffer: SimpleBuffer,
    pub seq_end: LSN
}

impl Memtable {
    pub open spec(checked) fn empty_memtable(lsn: LSN) -> Self {
        Memtable{
            buffer: SimpleBuffer::empty(),
            seq_end: lsn
        }
    }

    pub open spec(checked) fn drain(self) -> Self {
        Self::empty_memtable(self.seq_end)
    }

    pub open spec(checked) fn query(self, key: Key) -> Message
    {
        self.buffer.query(key)
    }

    pub open spec(checked) fn contains(self, key: Key) -> bool
    {
        self.buffer.contains(key)
    }

    pub open spec(checked) fn is_empty(self) -> bool
    {
        self.buffer.is_empty()
    }

    pub open spec(checked) fn apply_put(self, km: KeyedMessage) -> Memtable {
        let msg = self.query(km.key).merge(km.message);
        Memtable{
            buffer: self.buffer.insert(km.key, msg),
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

    // pub proof fn apply_puts_refines(self, puts: MsgHistory)
    //     requires puts.wf(), puts.can_follow(self.seq_end)
    //     ensures self.apply_puts(puts).i == self.i().apply_puts(puts)
    //     decreases puts.len()
    // {
    //     broadcast use Buffer::insert_refines, Buffer::query_refines;
    //     if 0 < puts.len() {
    //         let last_lsn = (puts.seq_end - 1) as nat;
    //         self.apply_puts_refines(puts.discard_recent(last_lsn));
    //     }
    // }
}

} // end verus!