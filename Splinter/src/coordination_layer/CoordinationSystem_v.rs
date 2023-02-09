#![allow(unused_imports)]
use builtin::*;

use builtin_macros::*;
use state_machines_macros::state_machine;
use crate::pervasive::prelude::*;

use crate::spec::Messages_t::*;
use crate::spec::MapSpec_t;
use crate::spec::MapSpec_t::*;

use crate::coordination_layer::CrashTolerantJournal_v::*;
use crate::coordination_layer::CrashTolerantMap_v::*;
use crate::coordination_layer::CrashTolerantMap_v;
use crate::coordination_layer::StampedMap_v::*;
use crate::coordination_layer::MessageHistory_v::{MsgHistory, KeyedMessage};

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
  pub progress: MapSpec_t::EphemeralState,
  pub sync_reqs: SyncReqs,
  pub map_lsn: LSN  // invariant: agrees with mapadt.stampedMap.seqEnd
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
    recover(
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
          ..pre.ephemeral.get_Some_0()
        }
      );

      update journal = new_journal;
      update mapadt = new_mapadt; 
    }
  }

  // TODO: get this reviewed
  transition! {
    accept_request(
      label: Label,
    ) {
      // Tenzin: Each of these destructurings requires looking
      // up in another file what the fully qualified name of the type
      // is and that's annoying. Good intellisense would save us here
      require let Label::Label{
        ctam_label: CrashTolerantAsyncMap::Label::OperateOp{
          base_op: AsyncMap::Label::RequestOp{
            req
          }
        }
      } = label;

      require !pre.ephemeral.get_Some_0().progress.requests.contains(req);

      // Wanted to do something like this but not available
      // let mut new_ephemeral = pre.ephemeral;
      // new_ephemeral.get_Some_0().progress.requests =
      //   new_ephemeral.get_Some_0().progress.requests + req;

      // This is ugly
      update ephemeral = Some(
        Known{
          progress: MapSpec_t::EphemeralState{
            requests: pre.ephemeral.get_Some_0().progress.requests.insert(req),
            ..pre.ephemeral.get_Some_0().progress
          },
          ..pre.ephemeral.get_Some_0()
        }
      );
    }
  }

  // TODO: get approval
  transition! {
    query(
      label: Label,
      new_journal: CrashTolerantJournal::State,
      new_mapadt: CrashTolerantMap::State,
    ) {
      // State must be known
      require pre.ephemeral.is_Some();
      let pre_ephemeral = pre.ephemeral.get_Some_0();

      // Dear lord my brain melted having to look up all of these
      // names
      require let Label::Label{
        ctam_label: CrashTolerantAsyncMap::Label::OperateOp{
          base_op: AsyncMap::Label::ExecuteOp{
            req,
            reply,
          }
        }
      } = label;

      require let Request{
        input: Input::QueryInput{
          key
        },
        id: request_id,
      } = req;

      require let Reply{
        output: Output::QueryOutput{
          value
        },
        id: reply_id,
      } = reply;

      require pre_ephemeral.progress.requests.contains(req);
      require req.id == reply.id;

      require !pre_ephemeral.progress.replies.contains(reply);
      // TODO(tenzin): AnyKey(key) ? How to do this

      require CrashTolerantJournal::State::next(
        pre.journal,
        new_journal,
        CrashTolerantJournal::Label::QueryEndLsnLabel{end_lsn: pre_ephemeral.map_lsn},
      );

      require CrashTolerantMap::State::next(
        pre.mapadt,
        new_mapadt,
        CrashTolerantMap::Label::QueryLabel{
          end_lsn: pre_ephemeral.map_lsn,
          key: key,
          value: value,
        },
      );

      update ephemeral = Some(
        Known{
          progress: MapSpec_t::EphemeralState{
            requests: pre_ephemeral.progress.requests.remove(req),
            replies: pre_ephemeral.progress.replies.insert(reply),
          },
          ..pre_ephemeral
        }
      );
      update journal = new_journal;
      update mapadt = new_mapadt;
    }
  }

  transition! {
    Put(
      label: Label,
      new_journal: CrashTolerantJournal::State,
      new_mapadt: CrashTolerantMap::State,
    ) {
      require pre.ephemeral.is_Some();
      let pre_ephemeral = pre.ephemeral.get_Some_0();

      // Destructuring and label checking boilerplate
      require let Label::Label{
        ctam_label: CrashTolerantAsyncMap::Label::OperateOp{
          base_op: AsyncMap::Label::ExecuteOp{
            req,
            reply,
          }
        }
      } = label;

      require let Request{
        input: Input::PutInput{
          key,
          value,
        },
        id: request_id,
      } = req;

      require let Reply{
        output: Output::PutOutput,
        id: reply_id,
      } = reply;

      require pre_ephemeral.progress.requests.contains(req);
      require req.id == reply.id;
      require !pre_ephemeral.progress.replies.contains(reply);

      // TODO: let keyed_message = 
      let keyed_message = KeyedMessage{
        key: key,
        message: Message::Define { value: value },
      };
      // TODO: let singleton: MsgHistory = <something>;
      let singleton = MsgHistory::singleton_at(pre_ephemeral.map_lsn, keyed_message);

      require CrashTolerantJournal::State::next(
        pre.journal,
        new_journal,
        CrashTolerantJournal::Label::PutLabel{ records: singleton },
      );

      require CrashTolerantMap::State::next(
        pre.mapadt,
        new_mapadt,
        CrashTolerantMap::Label::PutRecordsLabel{ records: singleton },
      );

      // TODO: update ephemeral
      update ephemeral = Some(
        Known {
          map_lsn: pre_ephemeral.map_lsn + 1,
          progress: MapSpec_t::EphemeralState{
            requests: pre_ephemeral.progress.requests.remove(req),
            replies: pre_ephemeral.progress.replies.insert(reply),
          },
          ..pre_ephemeral
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
      new_mapadt: CrashTolerantMap::State,
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
        new_mapadt,
        CrashTolerantMap::Label::CrashLabel
      );

      update journal = new_journal;
      update mapadt = new_mapadt;
      update ephemeral = None;
    }
  }
}

}
}
