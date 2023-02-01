#![allow(unused_imports)]
use builtin::*;

use builtin_macros::*;
use state_machines_macros::state_machine;
use crate::pervasive::{*, map::*};

use crate::spec::MapSpec_t::*;

use crate::coordination_layer::CrashTolerantJournal_v::*;
use crate::coordination_layer::CrashTolerantMap_v::*;
use crate::coordination_layer::CrashTolerantMap_v;
use crate::coordination_layer::StampedMap_v::*;

verus! {

type SyncReqId = nat;
type SyncReqs = Map<SyncReqId, LSN>;

// Does magic I guess
#[is_variant]
pub enum Ephemeral {
  Unknown,
  Known {
    progress: CrashTolerantMap_v::Ephemeral,
    syncReqs: SyncReqs,
    mapLsn: LSN  // invariant: agrees with mapadt.stampedMap.seqEnd
  },
}

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
      init ephemeral = Ephemeral::Unknown;
    }
  }

  // TODO (jonh): Rename all of the labels to exclude "Op" or "Label" since it's redundant
  // as enums are already namespaced under "Label", so it's like saying "Label Label"

  transition! {
    crash(
      label: Label,
      new_journal: CrashTolerantJournal::State,
      new_map: CrashTolerantMap::State
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
      update ephemeral = Ephemeral::Unknown;
    }
  }

  // transition! {
  //   load_ephemeral_from_persistent(
  //     label: Label,
  //     new_journal: CrashTolerantJournal::State,
  //     journal_step: CrashTolerantJournal::Step,
  //     new_map: CrashTolerantMap::State,
  //     map_step: CrashTolerantMap::Step
  //   ) {
  //     require label.is_NoOp
  //   }
  // }
}

}
}
