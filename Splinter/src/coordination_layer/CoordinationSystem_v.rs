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

type Label = CrashTolerantMap::Label;

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

  init! {
    initialize(j: CrashTolerantJournal::State) {
      require CrashTolerantJournal::State::initialize(j);
      init journal = j;
      let m = choose (|m| CrashTolerantMap::State::initialize(m)); 
      init mapadt = m;
      init ephemeral = Ephemeral::Unknown;
    }
  }

  // transition!{
  //   crash(lbl: Label) {
  //     require lbl.is_CrashLabel();

  //     require CrashTolerantJournal::State::next_by(
  //       pre.ephemeral.get_Known_v(), 
  //       new_journal, 
  //       AbstractJournal::Label::ReadForRecoveryLabel{ messages: lbl.get_ReadForRecoveryLabel_records() },
  //       journal_step
  //     );
  //   }
  // }
}

}
}
