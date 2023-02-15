#![allow(unused_imports)]
use builtin::*;

use builtin_macros::*;
use state_machines_macros::state_machine;
use crate::pervasive::prelude::*;

use crate::spec::Messages_t::*;
use crate::spec::MapSpec_t;
use crate::spec::MapSpec_t::*;
use crate::spec::FloatingSeq_t::*;

use crate::coordination_layer::CoordinationSystem_v::*;
use crate::coordination_layer::CrashTolerantJournal_v::*;
use crate::coordination_layer::CrashTolerantMap_v::*;
use crate::coordination_layer::CrashTolerantMap_v;
use crate::coordination_layer::StampedMap_v::*;
use crate::coordination_layer::MsgHistory_v::{MsgHistory, KeyedMessage};

verus! {

  impl CrashTolerantJournal::State
  {
    pub open spec fn i(self) -> MsgHistory
      recommends
        self.ephemeral.is_Known()
    {
      self.ephemeral.get_Known_v().journal
    }
  }

  impl CrashTolerantMap::State
  {
    pub open spec fn i(self) -> StampedMap
      recommends
        self.ephemeral.is_Known()
    {
      self.ephemeral.get_Known_v().stamped_map
    }
  }

  type Journal = MsgHistory;

  impl CoordinationSystem::State
  {
    pub open spec fn ephemeral_seq_end(self) -> LSN
      recommends
        self.ephemeral.is_Some()
    {
      self.journal.i().seq_end
    }
  }

  impl StampedMap
  {
    pub open spec fn to_version(self) -> Version
    {
      PersistentState{ appv: MapSpec::State{ kmmap: self.value } }
    }
  }

  pub open spec fn floating_versions(base: StampedMap, msg_history: MsgHistory, stable_lsn: LSN)
    -> (versions: FloatingSeq<Version>)
    recommends
      msg_history.can_follow(base.seq_end),
      msg_history.can_discard_to(stable_lsn),
  {
    FloatingSeq::new(stable_lsn, msg_history.seq_end + 1,
      |lsn: int| MsgHistory::map_plus_history(base, msg_history.discard_recent(lsn as LSN)).to_version()
    )
  }

  // Ic can be skipped as Dafny's CrashTolerantMapSpecMod had empty constants

  impl CoordinationSystem::State
  {
    pub open spec fn i(self) -> CrashTolerantAsyncMap::State
    {
      let stable_lsn = self.journal.persistent.seq_end;
      match self.ephemeral {
        Some(Known{ progress, sync_reqs, .. }) => CrashTolerantAsyncMap::State{
          versions: floating_versions(self.mapadt.persistent, self.journal.i(), stable_lsn),
          async_ephemeral: progress,
          sync_requests: sync_reqs,
        },
        None => CrashTolerantAsyncMap::State{
          versions: floating_versions(self.mapadt.persistent, self.journal.persistent, stable_lsn),
          async_ephemeral: AsyncMap::State::init_ephemeral_state(),
          sync_requests: Map::empty(),
        }
      }
    }
  }

  pub closed spec fn journal_overlaps_agree(j0: Journal, j1: Journal) -> bool
  {
    forall |lsn| #![auto] j0.contains(lsn) && j1.contains(lsn) ==> j0.msgs[lsn] == j1.msgs[lsn]
  }

  pub open spec fn journal_extends_journal(jlong: Journal, jshort: Journal, start_lsn: LSN) -> bool
    recommends
      jlong.can_follow(start_lsn),
      jshort.can_follow(start_lsn),
  {
    &&& jlong.can_discard_to(jshort.seq_end)            // jlong is longer
    &&& jlong.discard_recent(jshort.seq_end) == jshort  // they agree on contents in overlap
  }

  impl CoordinationSystem::State
  {
    // Geometry refers to the boundaries between the journal and
    // the mapadt line up correctly
    pub open spec fn inv_persistent_journal_geometry(self) -> bool
    {
      self.journal.persistent.can_follow(self.mapadt.persistent.seq_end)
    }

    pub open spec fn inv_ephemeral_geometry(self) -> bool
      recommends
        self.ephemeral.is_Some(),
    {
      // Ephemeral journal begins at persistent map
      &&& self.journal.i().can_follow(self.mapadt.persistent.seq_end)
      // Ephemeral map ends no earlier than persistent map
      &&& self.mapadt.persistent.seq_end <= self.mapadt.i().seq_end
      // Ephemeral journal ends no earlier than ephmeral map
      // (With the first conjunct, this conjunct happens to subsume the second conjunct,
      // but this was the nicest way to write it.)
      &&& self.journal.i().can_discard_to(self.mapadt.i().seq_end)
      // Ephemeral journal is no shorter than persistent state
      &&& self.journal.persistent.seq_end <= self.ephemeral_seq_end()
      // Local snapshot of mapLsn matched actual map state machine
      &&& self.ephemeral.get_Some_0().map_lsn == self.mapadt.ephemeral.get_Known_v().stamped_map.seq_end
    }

    pub open spec fn inv_ephemeral_value_agreement(self) -> bool
      recommends
        self.ephemeral.is_Some(),
        self.inv_ephemeral_geometry()
    {
      // Ephemeral journal agrees with persistent journal
      &&& journal_overlaps_agree(self.journal.persistent, self.journal.i())
      // Ephemeral map state agrees with ephemeral journal (tacked onto persistent map)
      &&& self.mapadt.i() == MsgHistory::map_plus_history(
            self.mapadt.persistent,
            self.journal.i().discard_recent(self.mapadt.i().seq_end))
    }

    pub open spec fn map_is_frozen(self) -> bool
    {
      self.mapadt.in_flight.is_Some()
    }

    pub open spec fn commit_started(self) -> bool
    {
      self.journal.in_flight.is_Some()
    }

    pub open spec fn inv_frozen_map_geometry(self) -> bool
      recommends
        self.ephemeral.is_Some(),
        self.map_is_frozen()
    {
      // frozen map hasn't passed ephemeral journal
      &&& self.mapadt.in_flight.get_Some_0().seq_end <= self.ephemeral_seq_end()
      // Frozen map doesn't regress before persistent map
      &&& self.mapadt.persistent.seq_end <= self.mapadt.in_flight.get_Some_0().seq_end
    }
  }
}
