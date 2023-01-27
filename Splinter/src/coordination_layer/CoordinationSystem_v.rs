#![allow(unused_imports)]
use builtin::*;

use builtin_macros::*;
use state_machines_macros::state_machine;
use crate::pervasive::{*, map::*};

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

  // TODO: add the async labels to the CrashTolerantMap
  // So there's a tree of labels. In Dafny there was templating
  // that was occuring by composing labels.
  // You could reuse higher level labels by passing the them a type
  // to wrap.
  // Example:
  // - Asynchrony is a type of interface. You can operate, you can crash
  //  you can sync etc. But depending on what thing is actually asynchronous
  //  the parameters of OperateOp are dependent on what it is (like a
  //  map or a journal)
  // - Kind of like a form of inheritance (really like templating).
  // - So you'd have a general

  // So there shouldn't actually be labels defined here, the labels
  // of the coordination system should just be the labels of the top
  // level pure, awesome, trusted, abstract, theoretical map.
  #[is_variant]
  pub enum Label{
    // TODO: 
    // OperateOp(baseOp: async.UIOp),
    CrashOp,
    SyncOp,
    ReqSyncOp{ syncReqId: SyncReqId },
    ReplySyncOp{ syncReqId: SyncReqId },
    NoopOp,
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

  transition! {
    crash(
      label: Label,
      new_journal: CrashTolerantJournal::State,
      journal_step: CrashTolerantJournal::Step,
      new_map: CrashTolerantMap::State,
      map_step: CrashTolerantMap::Step,
    ) {
      // Well-formed() predicates no longer necessary in spec mode
      require label.is_CrashOp();

      // `pre` is a keyword to access previous state (the v for the v')
      // `post` is a keyword for the `v'` state. However, in this context
      // `self` is equivalent to `post` it seems.
      require CrashTolerantJournal::State::next_by(
        pre.journal,
        new_journal,
        CrashTolerantJournal::Label::CrashLabel,
        journal_step
      );

      require CrashTolerantMap::State::next_by(
        pre.mapadt,
        new_map,
        CrashTolerantMap::Label::CrashLabel,
        map_step
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
