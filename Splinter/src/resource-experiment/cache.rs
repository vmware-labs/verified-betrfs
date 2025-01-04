// use builtin::*;
use vstd::prelude::*;
use vstd::rwlock::*;

use crate::frac::*;
use crate::disk::*;

verus!{

struct EntryState {
    phy: Option<Vec<u8>>,
    clean: bool,
    disk_rsrc: Tracked<FractionalResource<Seq<u8>, 2>>,
    cache_rsrc: Tracked<FractionalResource<Seq<u8>, 2>>,
}

struct EntryPred {
    disk_id: int,
    cache_id: int,
}

impl RwLockPredicate<EntryState> for EntryPred {
    closed spec fn inv(self, v: EntryState) -> bool {
        &&& v.disk_rsrc@.valid(self.disk_id, 1) 
        &&& v.cache_rsrc@.valid(self.cache_id, 1) 

        &&& v.phy is Some ==> {
            // The physical state always agrees with the cache (when the lock is released)
            &&& v.phy.unwrap() == v.cache_rsrc@.val()

            // The disk state only agrees if the record is clean
            &&& v.clean ==> v.disk_rsrc@.val() == v.phy.unwrap()@
        }
    }
}

struct Cache {
    disk: Disk,
    // Every single lba gets an interior-mutable RwLock-protected Entry.
    entries: Map<usize, RwLock<EntryState, EntryPred>>,
}

impl Cache {
    // The cache owns the entire disk, which is how it can promise to lock resources.
    exec fn new(&self, block_count: usize) -> (cache: Self)
    {
        let (disk, disk_rsrcs) = Disk::new(block_count);
        // how are we gonna get the caller_parts out of this comprehension?
        let entries = Map::new(
            |lba: usize| disk.valid_lba(lba),
            |lba: usize| {
                let tracked(my_part, caller_part) = FractionalResource::new(Seq::empty()).split(1);
                let state = EntryState {
                    phy: None,
                    clean: true,
                    disk_rsrc: disk_rsrcs.tracked_remove(lba),
                    cache_rsrc: Tracked(my_part),
                };
                let ghost pred = EntryPred{
                    disk_id: disk_rsrcs[lba]@.id,
                    cache_id: my_part@.id,
                };
                let locked_state = RwLock::new(state, Ghost(pred));
                locked_state
            }
        );
        Self{ disk, entries }
    }

    // Okay, there's unlocked physical state we need to think about.
    // The entries Map
    // the cell enum inside the map records needs to be replaced.
    // A simple strategy: have a map of rwlocks, one per page.
    // A fancier strategy is the Splinter cache.
    // So maybe we should do the simple thing now to avoid getting overwhelmed.

    exec fn fault_in(&self, lba: usize)
    requires
        self.disk.valid_lba(lba),
    {
//         let (phy, tracked_rsrc) = self.disk.read(lba, fault_in_cb);
    }

    spec fn id_map(&self) -> Map<usize, int>
    {
        Map::new(
            |lba: usize| self.disk.valid_lba(lba),
            |lba: usize| self.entries[lba].cache_rsrc@.id()
        )
    }

    fn write_lock(&self, lba: usize) -> (rsrc: FractionalResource<Seq<u8>, 2>)
    requires
       !(self.entries[lba].state is Absent),
    {
//         if self.entries[lba].state.get_lock_state().Unlocked
    }

    fn read(&self, lba: usize, rsrc: &FractionalResource<Seq<u8>, 2>)
        -> Vec<u8>
    {
    }

    fn write(&self, lba: usize, FractionalResource<Seq<u8>, 2>)
        -> (Vec<u8>, FractionalResource<Seq<u8>, 2>)
    {
    }

    fn unlock(&self, lba: usize, FractionalResource<Seq<u8>, 2>)
    {
    }

//     fn read<CB: DiskReadCallback>(&self, lba: usize, cb: Tracked<CB>)
//         -> (out: (Vec<u8>, Tracked<CB::CBResult>))
}

}//verus!
