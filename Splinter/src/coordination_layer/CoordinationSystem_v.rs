#![allow(unused_imports)]
use builtin::*;

use builtin_macros::*;
use state_machines_macros::state_machine;
use crate::pervasive::prelude::*;

use crate::spec::MapSpec_t;
use crate::spec::MapSpec_t::*;

use crate::coordination_layer::CrashTolerantJournal_v::*;
use crate::coordination_layer::CrashTolerantMap_v::*;
use crate::coordination_layer::CrashTolerantMap_v;
use crate::coordination_layer::StampedMap_v::*;
use crate::coordination_layer::MessageHistory_v::MsgHistory;

// TODO (jonh): Rename all of the labels in all files to exclude "Op" or "Label" since it's redundant
// as enums are already namespaced under "Label", so it's like saying "Label Label"

verus! {

type SyncReqId = nat;
type SyncReqs = Map<SyncReqId, LSN>;

// Does magic I guess
// #[is_variant]
// pub enum Ephemeral {
//   Unknown,
//   Known {
//     // TODO: is this right? I think this should actually be the MapSpec_t ephemeral state
//     progress: MapSpec_t::EphemeralState,
//     sync_reqs: SyncReqs,
//     map_lsn: LSN  // invariant: agrees with mapadt.stampedMap.seqEnd
//   },
// }

pub struct Known {
  progress: MapSpec_t::EphemeralState,
  sync_reqs: SyncReqs,
  map_lsn: LSN  // invariant: agrees with mapadt.stampedMap.seqEnd
}

type Ephemeral = Option<Known>;

state_machine!{ CoordinationSystem {
  fields {
    pub journal: CrashTolerantJournal::State,
    pub mapadt: CrashTolerantMap::State,
    pub ephemeral: Ephemeral,
  }

  // Labels of coordinationsystem should directly be the labels of the
  // CrashTolerantAsyncMap labels. Ideal would be to just copy it somehow,
  // but for now we're just wrapping the CTAM ones.
  #[is_variant]
  pub enum Label{
    Label{ ctam_label: CrashTolerantAsyncMap::Label }
  }

  init! {
    // Raise the non-determinism to the caller level (functional style)
    // initialize(j: CrashTolerantJournal::State, m: CrashTolerantMap::State) {
    //   require CrashTolerantJournal::State::initialize(j);
    //   require CrashTolerantMap::State::initialize(m)
    //   init journal = j;
    //   init mapadt = m;
    //   init ephemeral = Ephemeral::Unknown;
    // }

    // "Predicate-style" (give me the state and I verify it's good for initial state)
    initialize(state: CoordinationSystem::State) {
      // "Looks good to me" - Jon
      init journal = state.journal;
      init mapadt = state.mapadt;
      init ephemeral = None;
    }
  }

  transition! {
    load_ephemeral_from_persistent(
      label: Label,
      new_journal: CrashTolerantJournal::State,
      new_mapadt: CrashTolerantMap::State,
      map_lsn: LSN,
    ) {
      require let Label::Label{ ctam_label: CrashTolerantAsyncMap::Label::Noop } = label;
      
      require CrashTolerantJournal::State::next(
        pre.journal,
        new_journal,
        CrashTolerantJournal::Label::LoadEphemeralFromPersistentLabel
      );

      require CrashTolerantMap::State::next(
        pre.mapadt,
        new_mapadt,
        CrashTolerantMap::Label::LoadEphemeralFromPersistentLabel{ end_lsn: map_lsn }
      );

      // Solving the "initial" state problem is weird. Inherently we want a function
      // that returns a non-deterministic value, but as we've noted: not really possible
      // What would that primitive even be? An amorphous blob?

      update ephemeral = Some(
        Known {
          progress: AsyncMap::State::init_ephemeral_state(),
          sync_reqs: Map::empty(),
          map_lsn: map_lsn,
        }
      );

      update journal = new_journal;
      update mapadt = new_mapadt;
    }
  }

  transition! {
    Recover(
      label: Label,
      new_journal: CrashTolerantJournal::State,
      new_mapadt: CrashTolerantMap::State,
      records: MsgHistory,
    ) {
      require let Label::Label{ ctam_label: CrashTolerantAsyncMap::Label::Noop } = label;

      require pre.ephemeral.is_Some();

      require CrashTolerantJournal::State::next(
        pre.journal,
        new_journal,
        CrashTolerantJournal::Label::ReadForRecoveryLabel{ records }
      );

      require CrashTolerantMap::State::next(
        pre.mapadt,
        new_mapadt,
        CrashTolerantMap::Label::PutRecordsLabel{ records }
      );

      update ephemeral = Some(
        Known {
          map_lsn: records.seq_end,
          ..pre.ephemeral.unwrap()
        }
      );

      update journal = new_journal;
      update mapadt = new_mapadt; 
    }
  }

  transition! {
    crash(
      label: Label,
      new_journal: CrashTolerantJournal::State,
      new_map: CrashTolerantMap::State,
    ) {
      // TODO (travis/jonh): Figure out a way to gracefully handle state machines
      // that only have one possible label (or a way to suppress the warning about
      // unreachable branch in `match` statement that these `let` statements expand
      // to)
      // example that triggers the warning:
      // require let Label::Label{ ctam_label } = label;

      require let Label::Label{ ctam_label: CrashTolerantAsyncMap::Label::CrashOp } = label;

      require CrashTolerantJournal::State::next(
        pre.journal,
        new_journal,
        CrashTolerantJournal::Label::CrashLabel
      );

      require CrashTolerantMap::State::next(
        pre.mapadt,
        new_map,
        CrashTolerantMap::Label::CrashLabel
      );

      update journal = new_journal;
      update mapadt = new_map;
      update ephemeral = None;
    }
  }
}

}
}
