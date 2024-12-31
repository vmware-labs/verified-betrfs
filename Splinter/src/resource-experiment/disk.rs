// use builtin::*;

// use std::marker::PhantomData;

use vstd::prelude::*;
// use vstd::rwlock::*;
// use std::collections::hash_map::*;
// use vstd::std_specs::hash::*;
// use vstd::modes::*;
// use vstd::invariant::*;
// use std::sync::Arc;
// use vstd::thread::*;
use crate::frac::*;

// Open questions:
// - How do we represent the disk resources being reset after a crash?
//   Who do they go back to?
// - How should I represent physical asynchrony, like disk I/O?
// - Uses of Vec<u8> should probably be [u8; 512], except we can't construct
//   those in a tracked context.
// - Disk has implementations, which is dumb. What's the proof equivalent of
//   arbitrary!() ?

verus!{

//////////////////////////////////////////////////////////////////////////////

struct Disk {
    block_count: usize,
}

trait DiskReadCallback: Sized {
    type CBResult;

    spec fn inv(&self) -> bool
        ;

    spec fn id(&self) -> int
        ;

    spec fn inv_namespace(&self) -> int
        ;

    spec fn post(&self, return_val: Seq<u8>, result: Self::CBResult) -> bool
        ;

    proof fn read_cb(tracked self, tracked rsrc: &FractionalResource<Seq<u8>, 2>, return_val: Seq<u8>) 
        -> (tracked out: Self::CBResult)
    requires
        self.inv(),
        rsrc.valid(self.id(), 1),
        return_val == rsrc.val(),
    ensures
        self.post(return_val, out),
    opens_invariants [ self.inv_namespace() ]
    ;
}

trait DiskWriteCallback: Sized {
    type CBResult;

    spec fn inv(&self) -> bool
        ;

    spec fn id(&self) -> int
        ;

    spec fn inv_namespace(&self) -> int
        ;

    spec fn post(&self, return_val: Seq<u8>, result: Self::CBResult) -> bool
        ;

    proof fn write_cb(tracked self, tracked rsrc: &FractionalResource<Seq<u8>, 2>, lba: usize, set_val: Seq<u8>) 
        -> (tracked out: (FractionalResource<Seq<u8>, 2>, Self::CBResult))
    requires
        self.inv(),
        rsrc.valid(self.id(), 1),
    ensures
        out.0.valid(self.id(), 1),
        out.0.val() == set_val,
        self.post(set_val, out.1),
    opens_invariants [ self.inv_namespace() ]
    ;
}

impl Disk {
    spec fn valid_lba(self, lba: usize) -> bool
    {
        lba < self.block_count
    }

    spec fn ids(self) -> Map<usize, int>
    {
        arbitrary()
    }

    fn read<CB: DiskReadCallback>(&self, lba: usize, cb: Tracked<CB>)
        -> (out: (Vec<u8>, Tracked<CB::CBResult>))
    requires
        self.valid_lba(lba),
        cb@.inv(),
        cb@.id() == self.ids()[lba],
    ensures
        cb@.post(out.0@, out.1@),
    {
        assume(false);
        (unreached(), Tracked(proof_from_false()))
//         let phy_result = vec![0; 512];
// 
//         let tracked empty_block = vec![0; 512];
// 
//         let tracked(placeholder_frac, lost_frac) = FractionalResource::new(empty_block@).split(1);
//         let tracked callee_frac = placeholder_frac;
//         let cbresult = Tracked({ cb.get().read_cb(&callee_frac, phy_result@) });
//         (phy_result, cbresult)
    }

    fn write<CB: DiskWriteCallback>(&self, lba: usize, value: Vec<u8>, cb: Tracked<CB>)
        -> (out: Tracked<CB::CBResult>)
    requires
        self.valid_lba(lba),
        cb@.inv(),
        cb@.id() == self.ids()[lba],
    ensures
        cb@.post(value@, out@),
    {
        assume(false);
        Tracked(proof_from_false())
    }
}


}//verus!
