#![allow(unused_imports)]
use builtin::*;

use builtin_macros::*;
use state_machines_macros::state_machine;
use crate::pervasive::prelude::*;
use crate::pervasive::seq_lib::*;

use crate::spec::Messages_t::*;
use crate::spec::MapSpec_t;
use crate::spec::MapSpec_t::*;
use crate::spec::FloatingSeq_t::*;
use crate::spec::TotalKMMap_t;

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

    pub open spec fn inv_frozen_map_value_agreement(self) -> bool
      recommends
        self.ephemeral.is_Some(),
        self.inv_ephemeral_geometry(),
        self.map_is_frozen(),
        self.inv_frozen_map_geometry(),
    {
      self.mapadt.in_flight.get_Some_0() == 
        MsgHistory::map_plus_history(
          self.mapadt.persistent,
          self.journal.i().discard_recent(self.mapadt.in_flight.get_Some_0().seq_end)
        )
      // NB: Frozen Journal agreement comes "for free" because the frozen
      // journal is just defined as the frozenJournalLSN prefix of the
      // ephemeral journal.
    }

    pub open spec fn inv_commit_started_geometry(self) -> bool
      recommends self.commit_started()
    {
      let if_map = self.mapadt.in_flight.get_Some_0();
      let if_journal = self.journal.in_flight.get_Some_0();

      // We need a well-behaved journal to relate in-flight state to.
      &&& self.ephemeral.is_Some()
      &&& self.inv_ephemeral_geometry()

      // Geometry properties
      // In-flight map + journal stitch.
      &&& if_journal.can_follow(if_map.seq_end)
      // Commiting in-flight state won't shrink persistent state
      &&& self.journal.persistent.seq_end <= if_journal.seq_end
      // In-flight map doesn't precede persistent map -- that would cause
      // forgotten lsns to pop back into existence, and we don't have those lsns
      // in the ephemeral journal to compare to.
      &&& self.mapadt.persistent.seq_end <= if_map.seq_end
      // in-flight view hsan't passed ephemeral journal
      &&& if_journal.seq_end <= self.ephemeral_seq_end()
    }

    pub open spec fn inv_commit_started_value_agreement(self) -> bool
      recommends
        self.commit_started(),
        self.inv_commit_started_geometry(),
    {
      let if_map = self.mapadt.in_flight.get_Some_0();
      let if_journal = self.journal.in_flight.get_Some_0();

      // in-flight journal is consistent with the persistent journal
      &&& journal_overlaps_agree(if_journal, self.journal.persistent)
      // in-flight journal is consistent with the ephemeral journal
      &&& journal_overlaps_agree(if_journal, self.journal.i())
      // in-flight map matches corresponding state in ephemeral world
      // TODO: map_plus_history should probably be moved out of MsgHistory
      &&& if_map == MsgHistory::map_plus_history(
            self.mapadt.persistent,
            self.journal.i().discard_recent(if_map.seq_end)
          )
    }

    // TODO: (tenzin) Should this be made an inv of the state machine?
    // TODO: (Tenzin) have curly braces guarding implications double checked
    pub open spec fn inv(self) -> bool
    {
      &&& self.inv_persistent_journal_geometry()
      &&& self.ephemeral.is_None() ==> {!self.map_is_frozen() && !self.commit_started()}
      &&& self.ephemeral.is_Some() ==>
      {
        &&& self.inv_ephemeral_geometry()
        &&& self.inv_ephemeral_value_agreement()
        &&& self.map_is_frozen() ==>
        {
          &&& self.inv_frozen_map_geometry()
          &&& self.inv_frozen_map_value_agreement()
        }
      }
      &&& self.commit_started() ==>
      {
        &&& self.inv_commit_started_geometry()
        &&& self.inv_commit_started_value_agreement()
      }
    }
  }

  pub proof fn lemma_init_refines(v: CoordinationSystem::State)
    requires
      CoordinationSystem::State::init(v),
    ensures
      v.inv(),
      // TODO (tenzin): Get this initialization translation double checked
      CrashTolerantAsyncMap::State::init(v.i()),
  {
    // Was going to attempt this, but then you need to init a config with your own
    // thing but that just feels silly.
    // assert(CoordinationSystem::State::init_by(v, CoordinationSystem::Config::initialize()));
    
    // https://verus-lang.github.io/verus/guide/exists.html#choose
    // verus docs suggest that when a precondition contains an exists using
    // a choose statement is the canonical way to get it
    // let a = choose(|config: CoordinationSystem::Config| A::State::init_by(v, config))
    // assert(CoordinationSystem::State::initialize(v, v));
    
    // Despite requiring that this is true in the `initialize` of CoordinationSystem
    // this still isn't properly detected. My guess is that it's because `init`
    // actually uses an `exists` clause to determine which initialization function
    // to actually use, so verus isn't actually sure here which one we're using (even
    // though there's only one definition for `init`, the dummy is possible and
    // doesn't provide any guarantees)
    // Also I've noticed that these spec functions which we are calling are all
    // opaque, which might be cause for concern...
    // assert(CrashTolerantJournal::State::init(v.journal));

    // Found this in Slack history:
    // https://github.com/verus-lang/verus/blob/b990f436ef3ffa3a4078bdb6ee0aa7b05c46c5a7/source/rust_verify/example/state_machines/refinement.rs#L112
    // Seems like there are macros to help with refinement, but also it provides
    // a guide on how to do refinement
    // Here's my attempt following that:


    reveal(CoordinationSystem::State::init);
    reveal(CoordinationSystem::State::init_by);
    reveal(CrashTolerantJournal::State::init);
    reveal(CrashTolerantJournal::State::init_by);
    reveal(CrashTolerantMap::State::init);
    reveal(CrashTolerantMap::State::init_by);

    match choose(|config: CoordinationSystem::Config|
      CoordinationSystem::State::init_by(v, config))
    {
      CoordinationSystem::Config::initialize(state) => {
        v.i().versions.extensionality(FloatingSeq::new(0, 1, |i| AsyncMap::State::init_persistent_state()));
        
        assert(CrashTolerantAsyncMap::State::initialize(v.i()));

        CrashTolerantAsyncMap::show::initialize(v.i());
      },
      CoordinationSystem::Config::dummy_to_use_type_params(_) => {
        // Annoying case
        assume(false);
      }
    }
  }
}
