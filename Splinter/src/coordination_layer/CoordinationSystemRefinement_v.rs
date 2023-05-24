#![allow(unused_imports)]
use builtin::*;

use builtin_macros::*;
use state_machines_macros::state_machine;
use vstd::prelude::*;
use vstd::seq_lib::*;
use vstd::map::*;
use vstd::set_lib::*;

use crate::spec::Messages_t::*;
use crate::spec::MapSpec_t;
use crate::spec::MapSpec_t::*;
use crate::spec::FloatingSeq_t::*;
use crate::spec::TotalKMMap_t;
use crate::spec::Option_t;

use crate::coordination_layer::AbstractJournal_v::AbstractJournal;
use crate::coordination_layer::CoordinationSystem_v::*;
use crate::coordination_layer::CrashTolerantJournal_v;
use crate::coordination_layer::CrashTolerantJournal_v::*;
use crate::coordination_layer::CrashTolerantMap_v::*;
use crate::coordination_layer::CrashTolerantMap_v;
use crate::coordination_layer::AbstractMap_v::*;
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

    pub open spec fn wf(self) -> bool
    {
      &&& self.persistent.wf()
      &&& self.ephemeral.wf()
      &&& (self.in_flight.is_Some() ==> self.in_flight.get_Some_0().wf())
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

    // CrashTolerantMap needs to carry wf/invariant that shows that contained
    // TotalKMMap is always wf (always has total domain)
    pub open spec fn wf(self) -> bool
    {
      &&& self.persistent.value.wf()
      &&& match self.ephemeral {
          CrashTolerantMap_v::Ephemeral::Known{ v } => v.stamped_map.value.wf(),
          _ => true,
        }
      &&& match self.in_flight {
          Option_t::Option::Some(v) => v.value.wf(),
          _ => true
        }
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
    pub open spec fn wf(self) -> bool
    {
      &&& self.journal.wf()
      &&& self.mapadt.wf()
      &&& self.ephemeral.is_Some() == self.journal.ephemeral.is_Known()
      &&& self.journal.ephemeral.is_Known() == self.mapadt.ephemeral.is_Known()
      &&& self.journal.in_flight.is_Some() ==> self.mapadt.in_flight.is_Some()
    }

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
      // up until ephemeral_map.seq_end (it's possible the ephemeral journal is
      // ahead of the map)
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
      // invariant: the in_flight map agrees with the persistent map,
      // plus has extra entries from the ephemeral journal.
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
      // in-flight view hasn't passed ephemeral journal
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
      // TODO: MsgHistory::map_plus_history should probably be moved out of MsgHistory
      &&& if_map == MsgHistory::map_plus_history(
            self.mapadt.persistent,
            self.journal.i().discard_recent(if_map.seq_end)
          )
    }

    // TODO: (tenzin) Should this be made an inv of the state machine?
    // TODO: (Tenzin) have curly braces guarding implications double checked
    pub open spec fn inv(self) -> bool
    {
      &&& self.wf()
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

    match choose |config: CoordinationSystem::Config|
      CoordinationSystem::State::init_by(v, config)
    {
      CoordinationSystem::Config::initialize(state) => {
        v.i().versions.extensionality(FloatingSeq::new(0, 1, |i| AsyncMap::State::init_persistent_state()));
        
        assert(CrashTolerantAsyncMap::State::initialize(v.i()));

        CrashTolerantAsyncMap::show::initialize(v.i());
      },
      CoordinationSystem::Config::dummy_to_use_type_params(_) => {
        // Dummy case that doesn't require proof. An artifact of how the
        // Config enum is created
        assume(false);
      }
    }
  }

  pub proof fn commit_step_preserves_history(
    v: CoordinationSystem::State,
    vp: CoordinationSystem::State, // v'
    label: CoordinationSystem::Label,
    step: CoordinationSystem::Step,
    lsn: LSN,
  )
    requires
      v.inv(),
      // Dafny's able to figure this out without this line, idk
      // why Verus isn't, because of opaque `next_by` etc.? (But idk how
      // to reveal those for the requires list)
      // v.ephemeral.is_Some(),
      // // Same with this,
      // v.journal.ephemeral.is_Known(),
      CoordinationSystem::State::next(v, vp, label),
      CoordinationSystem::State::next_by(v, vp, label, step),
      matches!(step, CoordinationSystem::Step::commit_complete(_, _)),
      // What we'd like to do ideally:
      // step.is_commit_complete(),
      v.mapadt.persistent.seq_end <= lsn <= v.ephemeral_seq_end(),
      v.mapadt.in_flight.get_Some_0().seq_end <= lsn,
    ensures
      v.journal.i().can_discard_to(lsn),
      MsgHistory::map_plus_history(v.mapadt.persistent, v.journal.i().discard_recent(lsn))
        == MsgHistory::map_plus_history(vp.mapadt.persistent, vp.journal.i().discard_recent(lsn))
  {
    reveal(CoordinationSystem::State::next);
    reveal(CoordinationSystem::State::next_by);
    reveal(CrashTolerantJournal::State::next);
    reveal(CrashTolerantJournal::State::next_by);
    reveal(CrashTolerantMap::State::next);
    reveal(CrashTolerantMap::State::next_by);
    reveal(AbstractJournal::State::next);
    reveal(AbstractJournal::State::next_by);

    // Passes with the reveal statements, fails without
    assert(v.ephemeral.is_Some());
    assert(v.journal.ephemeral.is_Known());

    assert(CrashTolerantJournal::State::next(v.journal, vp.journal, CrashTolerantJournal::Label::CommitCompleteLabel {
      require_end: v.ephemeral.get_Some_0().map_lsn,
    }));

    // There are six pieces in play here: the persistent and in-flight images and the ephemeral journals:
    //  _________ __________
    // | pdi.map | pdi.jrnl |
    //  --------- ----------
    //  ______________R__________
    // | idi.map      | idi.jrnl |
    //  -------------- ----------
    //            ____________________
    //           | eph.jrnl           |
    //            --------------------
    //                 _______________
    //                | eph'.jrnl     |
    //                 ---------------
    // "R" is the "reference LSN" -- that's where we're going to prune ephemeral.journal, since
    // after the commit it is going to be the LSN of the persistent map.

    let ref_lsn = v.mapadt.in_flight.get_Some_0().seq_end;
    let ej = v.journal.i();

    // Recommendation fails even though assertion passes.
    assert(ej.can_discard_to(lsn));
    let eji = ej.discard_recent(lsn);

    // Here's a calc, but in comments so we can use a shorthand algebra:
    // Let + represent both MapPlusHistory and Concat (they're associative).
    // Let [x..] represent DiscardOld(x) and [..y] represent DiscardRecent(y).
    // var im:=v.inFlightImage.value.mapadt, pm:=v.mapadt.persistent, R:=im.seqEnd
    // pm'+ej'[..lsn]
    // im+ej'[..lsn]
    // im+ej[..lsn][R..]
    //   {InvInFlightVersionAgreement}

    // (pm+ej[..R])+ej[..lsn][R..]
    journal_associativity(v.mapadt.persistent, ej.discard_recent(ref_lsn), ej.discard_recent(lsn).discard_old(ref_lsn));

    // MsgHistory::concat_forall_lemma();
    ej.discard_recent(ref_lsn).concat_lemma(ej.discard_old(ref_lsn));

    // Adding split pieces gets original ej[..lsn]+ej[lsn..] = ej
    assert_maps_equal!(ej.discard_recent(ref_lsn).concat(ej.discard_old(ref_lsn)).msgs, ej.msgs);
    // Discard commutes: ej[ref_lsn..][..lsn] = ej[..lsn][ref_lsn..]
    assert_maps_equal!(ej.discard_old(ref_lsn).discard_recent(lsn).msgs, ej.discard_recent(lsn).discard_old(ref_lsn).msgs);
    // Discard is associative with concat: ej[..ref_lsn]+(ej[ref_lsn..][..lsn]) = (ej[..ref_lsn]+ej[ref_lsn..])[..lsn]
    // Note that ej[..ref_lsn]+ej[ref_lsn..] should just be ej
    assert_maps_equal!(ej.discard_recent(ref_lsn).concat(ej.discard_old(ref_lsn).discard_recent(lsn)).msgs, ej.discard_recent(ref_lsn).concat(ej.discard_old(ref_lsn)).discard_recent(lsn).msgs);
    
    // MsgHistory::map_plus_history_forall_lemma();
    MsgHistory::map_plus_history_seq_end_lemma(v.mapadt.persistent, v.journal.i().discard_recent(lsn));
    // Proving that right's seq_end == lsn
    MsgHistory::map_plus_history_seq_end_lemma(vp.mapadt.persistent, vp.journal.i().discard_recent(lsn));
  }

  pub proof fn journal_associativity(x: StampedMap, y: MsgHistory, z: MsgHistory)
    requires
      y.wf(),
      z.wf(),
      y.can_follow(x.seq_end),
      z.can_follow(y.seq_end),
    ensures
      MsgHistory::map_plus_history(MsgHistory::map_plus_history(x, y), z) == MsgHistory::map_plus_history(x, y.concat(z))
    decreases
      z.len(),
  {
    let left = MsgHistory::map_plus_history(MsgHistory::map_plus_history(x, y), z);
    let right = MsgHistory::map_plus_history(x, y.concat(z));

    if !z.is_empty() {
      let ztrim = z.discard_recent((z.seq_end - 1) as nat);
      let yz = y.concat(z);

      journal_associativity(x, y, ztrim);
      assert(yz.discard_recent((yz.seq_end - 1) as nat) == y.concat(ztrim))
      by
      {
        assert_maps_equal!(
          yz.discard_recent((yz.seq_end - 1) as nat).msgs,
          y.concat(ztrim).msgs
        );
      }
 
      // assert_maps_equal!(left.value, right.value);
      assert(left == right);
    } else {
      let yz = y.concat(z);
      // Once again introducing extensionality arguments is necessary to prove
      // Original Dafny version does not need this else case.
      assert_maps_equal!(yz.msgs, y.msgs);
      assert(left == right);
    }
  }

  pub proof fn inv_inductive_put_step(
    v: CoordinationSystem::State,
    vp: CoordinationSystem::State,
    label: CoordinationSystem::Label,
    step: CoordinationSystem::Step,
  )
    requires
      v.inv(),
      CoordinationSystem::State::next(v, vp, label),
      CoordinationSystem::State::next_by(v, vp, label, step),
      matches!(step, CoordinationSystem::Step::put(_, _)),
    ensures
      vp.inv(),
  {
    reveal(CoordinationSystem::State::next);
    reveal(CoordinationSystem::State::next_by);
    reveal(CrashTolerantJournal::State::next);
    reveal(CrashTolerantJournal::State::next_by);
    reveal(AbstractJournal::State::next);
    reveal(AbstractJournal::State::next_by);
    reveal(CrashTolerantMap::State::next);
    reveal(CrashTolerantMap::State::next_by);
    reveal(AbstractMap::State::next);
    reveal(AbstractMap::State::next_by);

    if v.map_is_frozen() {
      let frozen_end = v.mapadt.in_flight.get_Some_0().seq_end;
      assert(v.journal.i().discard_recent(frozen_end) 
        == vp.journal.i().discard_recent(frozen_end))
      by
      {
        assert_maps_equal!(
          v.journal.i().discard_recent(frozen_end).msgs,
          vp.journal.i().discard_recent(frozen_end).msgs
        );
      }
    }

    let key = label.get_Label_ctam_label().get_OperateOp_base_op()
      .get_ExecuteOp_req().input.get_PutInput_key();
    let value = label.get_Label_ctam_label().get_OperateOp_base_op()
      .get_ExecuteOp_req().input.get_PutInput_value();

    let keyed_message = KeyedMessage{
      key: key,
      message: Message::Define { value: value },
    };

    let singleton = MsgHistory::singleton_at(v.ephemeral.get_Some_0().map_lsn, keyed_message);
    
    assert(CrashTolerantJournal::State::next(v.journal, vp.journal, CrashTolerantJournal::Label::PutLabel{ records: singleton }));

    journal_associativity(v.mapadt.persistent, v.journal.i(), singleton);

    assert(v.journal.i().discard_recent(v.mapadt.i().seq_end) == v.journal.i()) by {
      assert_maps_equal!(
        v.journal.i().discard_recent(v.mapadt.i().seq_end).msgs,
        v.journal.i().msgs
      );
    }

    // This should be true by the definition of the transition (just leaving
    // this assertion to remember that)
    assert(vp.mapadt.i() == MsgHistory::map_plus_history(v.mapadt.i(), singleton));
  
    // Because `verus` spec functions don't have ensures clauses, we need a separate lemma to
    // prove properties of certain operations.
    // MsgHistory::map_plus_history_forall_lemma();

    // Need to prove maps and sets are equal all over the place
    assert(vp.journal.i() == vp.journal.i().discard_recent(vp.mapadt.i().seq_end)) by {
      assert_maps_equal!(
        vp.journal.i().msgs,
        vp.journal.i().discard_recent(vp.mapadt.i().seq_end).msgs
      );
    }

    assert(vp.inv());
  }

  pub proof fn inv_inductive_commit_start_step(
    v: CoordinationSystem::State,
    vp: CoordinationSystem::State,
    label: CoordinationSystem::Label,
    step: CoordinationSystem::Step,
  )
    requires
      v.inv(),
      CoordinationSystem::State::next(v, vp, label),
      CoordinationSystem::State::next_by(v, vp, label, step),
      matches!(step, CoordinationSystem::Step::commit_start(_, _, _)),
    ensures
      vp.inv()
  {
    // The classic preamble for revealing all nested transitions we rely on
    reveal(CoordinationSystem::State::next);
    reveal(CoordinationSystem::State::next_by);
    reveal(CrashTolerantJournal::State::next);
    reveal(CrashTolerantJournal::State::next_by);
    reveal(AbstractJournal::State::next);
    reveal(AbstractJournal::State::next_by);
    reveal(CrashTolerantMap::State::next);
    reveal(CrashTolerantMap::State::next_by);
    // reveal(AbstractMap::State::next);
    // reveal(AbstractMap::State::next_by);
  }

  pub proof fn inv_inductive_commit_complete_step(
    v: CoordinationSystem::State,
    vp: CoordinationSystem::State,
    label: CoordinationSystem::Label,
    step: CoordinationSystem::Step,
  )
  requires
    v.inv(),
    CoordinationSystem::State::next(v, vp, label),
    CoordinationSystem::State::next_by(v, vp, label, step),
    matches!(step, CoordinationSystem::Step::commit_complete(_, _)),
  ensures
    vp.inv()
  {
    reveal(CoordinationSystem::State::next);
    reveal(CoordinationSystem::State::next_by);
    reveal(CrashTolerantJournal::State::next);
    reveal(CrashTolerantJournal::State::next_by);
    reveal(AbstractJournal::State::next);
    reveal(AbstractJournal::State::next_by);
    reveal(CrashTolerantMap::State::next);
    reveal(CrashTolerantMap::State::next_by);
    reveal(AbstractMap::State::next);
    reveal(AbstractMap::State::next_by);

    // MsgHistory::map_plus_history_forall_lemma();

    // Proof strategy:
    // Most invariant pieces go through automatically, but verus doesn't believe
    // by default that in the post state that em = pm + ej[:em_end]
    // But by invariant in the pre state that should have been true, and em
    // doesn't change, pm instead just absorbs some of ej (and then ej gets truncated).
    // So, by invariant in the pre state we have:
    //   em = pm + ej[:em_end] = pm + ej[:im_end] + ej[im_end:em_end]
    // And by invariant on in_flight in pre_state:
    //   im = pm + ej[:im_end]
    // In post state:
    //   em = pre.em
    //   pm = pre.im = pre.pm + pre.ej[:im_end]
    //   ej = pre.ej[im_end:]
    // So naturally it should follow that
    //   pm + ej = pre.pm + pre.ej[:im_end] + pre.ej[im_end:] = pre.em = em
    // QED.

    let pm = v.mapadt.persistent;
    let em_end = v.mapadt.i().seq_end;
    let ej = v.journal.i();
    let im_end = v.mapadt.in_flight.get_Some_0().seq_end;

    // Show that ej[:em_end] == ej[:im_end] + ej[im_end:em_end]
    // Needed an extensionality argument... took a while to find
    // Maybe I should make this a lemma on the concat operator...
    assert(ej.discard_recent(em_end) 
      == ej.discard_recent(im_end).concat(ej.discard_old(im_end).discard_recent(em_end)))
    by
    {
      let left = ej.discard_recent(em_end);
      let right = ej.discard_recent(im_end).concat(ej.discard_old(im_end).discard_recent(em_end));
      assert_maps_equal!(left.msgs, right.msgs);
    }

    // Argue that pre.pm + pre.ej[:im_end] + pre.ej[im_end:em_end] 
    // == pre.pm + (pre.ej[:im_end] + pre.ej[im_end:em_end]
    journal_associativity(
      v.mapadt.persistent,
      ej.discard_recent(im_end),
      ej.discard_old(im_end).discard_recent(em_end)
    );
  }

  pub proof fn inv_inductive(v: CoordinationSystem::State, vp: CoordinationSystem::State, label: CoordinationSystem::Label)
    requires
      v.inv(),
      CoordinationSystem::State::next(v, vp, label),
    ensures
      vp.inv(),
  {
    reveal(CoordinationSystem::State::next);
    reveal(CoordinationSystem::State::next_by);
    reveal(CrashTolerantJournal::State::next);
    reveal(CrashTolerantJournal::State::next_by);
    reveal(AbstractJournal::State::next);
    reveal(AbstractJournal::State::next_by);
    reveal(CrashTolerantMap::State::next);
    reveal(CrashTolerantMap::State::next_by);
    reveal(AbstractMap::State::next);
    reveal(AbstractMap::State::next_by);

    // Be careful to reveal init and init_by transitions as well!
    reveal(CrashTolerantJournal::State::init);
    reveal(CrashTolerantJournal::State::init_by);
    // No direct dependencies on init()
    // reveal(AbstractJournal::State::init);
    reveal(AbstractJournal::State::init_by);

    // Avoid common extensionality argument errors with these proofs
    // about extensional equality for the frequently used MsgHistory and
    // StampedMap
    MsgHistory::ext_equal_is_equality();
    StampedMap::ext_equal_is_equality();

    let step = choose |s| CoordinationSystem::State::next_by(v, vp, label, s);
    
    match step {
      CoordinationSystem::Step::load_ephemeral_from_persistent(_, _, _) => {
        // Verifies for free! (Well, besides all of the reveals lol)
        assert(vp.inv());
      },
      CoordinationSystem::Step::recover(new_journal, new_mapadt, records) => {
        // First let's check what vp.mapadt.ephemeral should be based on transition...
        let pre_stamped_map = v.mapadt.ephemeral.get_Known_v().stamped_map;
        let post_stamped_map = vp.mapadt.ephemeral.get_Known_v().stamped_map;

        // Believes that this is true (definition of transition)
        assert(post_stamped_map == MsgHistory::map_plus_history(pre_stamped_map, records));

        // MsgHistory::map_plus_history_forall_lemma();
        // Doesn't believe self.ephemeral.get_Some_0().map_lsn == self.mapadt.ephemeral.get_Known_v().stamped_map.seq_end
        assert(vp.ephemeral.get_Some_0().map_lsn 
          == vp.mapadt.ephemeral.get_Known_v().stamped_map.seq_end);
        // Has issues with self.mapadt.ephemeral.get_Known_v().stamped_map having total domain
        
        // Alright the above is all good, now I just need to show
        // inv_ephemeral_value_agreement()

        // So we know that this is true for the pre state
        assert(v.inv_ephemeral_value_agreement());

        // em_end (is initial map end)
        let em_end = v.mapadt.i().seq_end;
        let em_end_p = vp.mapadt.i().seq_end;
        // pre.em
        let em = v.mapadt.i();
        let ej = v.journal.i();
        let pm = v.mapadt.persistent;
        // post.em
        let em_p = vp.mapadt.i();
        let pm_p = vp.mapadt.persistent;
        let ej_p = vp.journal.i();
        // pre.em = pre.pm + pre.ej[:em_end]

        // During a recover step all we do is insert some entries from
        // the journal into the ephemeral map
        // So journal is unchanged:
        // post.ej = pre.ej
        assert(vp.journal == v.journal);
        // persistent map is unchanged too
        assert(vp.mapadt.persistent == v.mapadt.persistent);

        // These three facts should be sufficient to establish
        // the fourth, but it doesn't believe me... does now! (Extensional
        // equality yet again)
        assert(ej.includes_subseq(records));
        assert(records.seq_start == em_end);
        assert(records.seq_end == em_end_p);

        // Ah... wait, maybe it's another extensionality arguent
        // So now we need to assert that ej[em_end:em_end'] is the same
        // as records
        assert(records.ext_equal(ej.discard_old(em_end).discard_recent(em_end_p)));
        assert(records == ej.discard_old(em_end).discard_recent(em_end_p));

        // And the post state is made of original em + some entries from
        // journal 
        // post.em = pre.em + pre.ej[em_end:em_end']
        assert(em_p == em.plus_history(
          ej.discard_old(em_end).discard_recent(em_end_p)));

        // em = pm + ej[:em_end] by invariant
        assert(em.ext_equal(pm.plus_history(ej.discard_recent(em_end))));

        // Combining above two facts, we should get that:
        // em' = pm + ej[:em_end] + ej[em_end:em_end']
        assert(em_p.ext_equal(
          pm.plus_history(ej._dr(em_end)).plus_history(ej._do(em_end)._dr(em_end_p))
        ));

        // ej[:em_end'] = ej[:em_end] + ej[em_end:em_end']
        assert(ej.discard_recent(em_end_p).ext_equal(
          ej.discard_recent(em_end).concat(ej.discard_old(em_end)
          .discard_recent(em_end_p))
        ));

        journal_associativity(pm, ej._dr(em_end), ej._do(em_end)._dr(em_end_p));

        // So combining above two:
        // em' = pm + ej[:em_end']
        assert(em_p.ext_equal(pm.plus_history(ej._dr(em_end_p))));

        // Ahhh!!! ^^^Is where the breakdown occurs. This is why journal
        // associativity is necessary

        // Now we just need to show what pm' + ej'[:em_end'] is
        // We know that pm' = pm and ej' = ej, so we should have that
        // their concatenation is the same
        assert(pm_p.plus_history(ej_p._dr(em_end_p))
          == pm.plus_history(ej._dr(em_end_p)));
        
        // So now it should just follow that:
        assert(em_p.ext_equal(pm.plus_history(ej._dr(em_end_p))));

        // Target (inv_ephemeral_value_agreement()):
        // assert(vp.mapadt.i().ext_equal(MsgHistory::map_plus_history(
        //   vp.mapadt.persistent,
        //   vp.journal.i().discard_recent(vp.mapadt.i().seq_end))));

        assert(vp.inv());
      },
      _ => {
        assume(vp.inv());
      }
    }
  }
}
