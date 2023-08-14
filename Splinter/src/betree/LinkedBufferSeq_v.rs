use builtin::*;

use builtin_macros::*;

use vstd::{map::*,seq::*,set::*};
use crate::spec::KeyType_t::*;
use crate::spec::Messages_t::*;
use crate::betree::Buffer_v::*;
use crate::betree::BufferSeq_v;
use crate::betree::OffsetMap_v::*;
use crate::disk::GenericDisk_v::*;

verus! {
#[verifier::ext_equal]
pub struct DiskView {
    pub entries: Map<Address, Buffer>
}

impl DiskView {
    pub open spec(checked) fn wf(self) -> bool
    {
        self.entries.dom().finite()
    }

    pub open spec(checked) fn repr(self) -> Set<Address>
    {
        self.entries.dom()
    }

    pub open spec(checked) fn get(self, addr: Address) -> Buffer
        recommends self.entries.contains_key(addr)
    {
        self.entries[addr]
    }

    pub open spec(checked) fn modify_disk(self, addr: Address, buffer: Buffer) -> DiskView
    {
        DiskView{ entries: self.entries.insert(addr, buffer) }
    }

    pub open spec(checked) fn is_fresh(self, addrs: Set<Address>) -> bool 
    {
        self.entries.dom().disjoint(addrs)
    }

    pub open spec(checked) fn is_subdisk(self, bigger: DiskView) -> bool
    {
        self.entries.le(bigger.entries)  
    }

    pub open spec(checked) fn merge_disk(self, other: DiskView) -> DiskView
    {
        DiskView{ entries: self.entries.union_prefer_right(other.entries) }
    }
} // end of DiskView impl

pub open spec(checked) fn empty_disk() -> DiskView
{
    DiskView{ entries: Map::empty() }
}

#[verifier::ext_equal]
pub struct BufferSeq {
    pub buffers: Seq<Address>
}

impl BufferSeq {
    pub open spec(checked) fn empty() -> BufferSeq
    {
        BufferSeq{ buffers: seq![] }
    }

    pub open spec(checked) fn len(self) -> nat {
        self.buffers.len()
    }

    #[verifier(inline)]
    pub open spec(checked) fn spec_index(self, i: int) -> Address
        recommends 0 <= i < self.len()
    {
        self.buffers[i]
    }

    pub open spec(checked) fn valid(self, dv: DiskView) -> bool
    {
        forall |i| #![auto] 0 <= i < self.len() ==> dv.repr().contains(self.buffers[i])
    }

    pub open spec(checked) fn repr(self) -> Set<Address>
    {
        self.buffers.to_set()
    }

    pub open spec(checked) fn slice(self, start: int, end: int) -> BufferSeq 
        recommends 0 <= start <= end <= self.len()
    {
        BufferSeq{ buffers: self.buffers.subrange(start, end) }
    }

    pub open spec(checked) fn extend(self, new_buffers: BufferSeq) -> BufferSeq 
    {
        BufferSeq{ buffers: self.buffers + new_buffers.buffers }
    }

    pub open spec(checked) fn query_from(self, dv: DiskView, k: Key, start: int) -> Message 
        recommends 0 <= start <= self.len()
        decreases self.len() - start when start <= self.len()
    {
        if start == self.len() {
            Message::Update{delta: nop_delta()}
        } else {
            if dv.entries.contains_key(self[start]) {
                dv.get(self[start]).query(k).merge(self.query_from(dv, k, start+1))
            } else {
                self.query_from(dv, k, start+1)
            }
        }
    }

    pub open spec(checked) fn update_subrange(self, start: int, end: int, new_buffer_addr: Address) -> BufferSeq 
        recommends 0 <= start < end <= self.len()
    {
        let s = seq![new_buffer_addr];
        BufferSeq{ buffers: self.buffers.subrange(0, start) + s + self.buffers.subrange(end, self.len() as int) }
    }

    pub open spec(checked) fn i(self, dv: DiskView) -> BufferSeq_v::BufferSeq
        recommends self.valid(dv)
    {
        let buffers = Seq::new(self.len(), |i| dv.get(self[i]));
        BufferSeq_v::BufferSeq{ buffers: buffers }
    }

    pub proof fn subdisk_implies_same_i(self, small: DiskView, big: DiskView)
        requires self.valid(small), small.is_subdisk(big)
        ensures self.valid(big), self.i(small) == self.i(big)
    {
        assert forall |i| 0 <= i < self.len()
        implies self.i(small)[i] == self.i(big)[i]
        by {
            assert(big.entries.dom().contains(self[i])); // trigger
        }
        assert(self.i(small) =~= self.i(big));
    }

    pub open spec fn key_in_buffer(self, dv: DiskView, from_idx: int, k: Key, buffer_idx: int) -> bool
    {
        &&& from_idx <= buffer_idx < self.len()
        &&& dv.entries.contains_key(self[buffer_idx])
        &&& dv.get(self[buffer_idx]).map.contains_key(k)
    }

    pub open spec(checked) fn key_in_buffer_filtered(self, dv: DiskView, offset_map: OffsetMap, from_idx: int, k: Key, buffer_idx: int) -> bool
        recommends 0 <= from_idx, offset_map.is_total()
    {
        &&& self.key_in_buffer(dv, from_idx, k, buffer_idx)
        &&& offset_map.offsets[k] <= buffer_idx
    }

    pub proof fn query_from_commutes_with_i(self, dv: DiskView, k: Key, start: int)
        requires 0 <= start <= self.len(), self.valid(dv)
        ensures self.query_from(dv, k, start) == self.i(dv).query_from(k, start)
        decreases self.len() - start
    {
        if start < self.len() {
            self.query_from_commutes_with_i(dv, k, start+1);
        }    
    }
} // end impl BufferSeq
}  // end verus!
