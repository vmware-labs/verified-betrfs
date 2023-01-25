#![allow(unused_imports)]
use builtin::*;

use builtin_macros::*;
use state_machines_macros::state_machine;
use crate::pervasive::{map::*};

use crate::coordination_layer::CrashTolerantJournal_v::*;
use crate::coordination_layer::CrashTolerantMap_v::*;
use crate::coordination_layer::CrashTolerantMap_v;

verus! {

// Does magic I guess
#[is_variant]
pub enum Ephemeral {
  Unknown,
  Known {
    progress: CrashTolerantMap_v::Ephemeral,
    // syncReqs: SyncReqs,
    mapLsn: LSN  // invariant: agrees with mapadt.stampedMap.seqEnd
  },
}

state_machine!{ CoordinationSystem {
  fields {
    pub journal: CrashTolerantJournal::State,
    pub mapadt: CrashTolerantMap::State,
    pub ephemeral: Ephemeral,
  }
}
}

}
