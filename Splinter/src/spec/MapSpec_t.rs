// Copyright 2018-2024 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, University of Washington
// SPDX-License-Identifier: BSD-2-Clause
// TODO _t and _s enforcement in the build system? Gasp, don't know how to thing about
// approaching/modifying/enhancing crate build...?
use builtin::*;
use builtin_macros::*;
use vstd::{map::*, set::*};

use crate::spec::FloatingSeq_t::*;
use crate::spec::KeyType_t::*;
use crate::spec::Messages_t::*;
use crate::spec::TotalKMMap_t::*;

use state_machines_macros::state_machine;

// TODO (tenzin): break out everything in this file into separate files/modules
// (cleaner logical breaks)
verus! {

// Parallels a structure from Dafny (specifically from MapSpec.s.dfy)
// Where the abstract top-level map specification uses two variables to
// label its transitions. One of type `Input` and one of type `Output`.
/// An Input represents a possible action that can be taken on an abstract
/// MapSpec (i.e.: abstract key-value store), and contains the relevant
/// arguments for performing that operation.
#[derive(Debug)]
pub enum Input {
    QueryInput { key: Key },
    PutInput { key: Key, value: Value },
    NoopInput,
}

/// An Output represents the result from taking an Input action (and contains
/// any relevant return arguments from performing the corresponding action).
#[derive(Debug)]
pub enum Output {
    QueryOutput { value: Value },
    PutOutput,
    NoopOutput,
    // TODO: Error Output (e.g. disk full)
}

// TODO ugly workaround for init!{my_init()} being a predicate from outside
// TODO 2: can't declare this fn inside MapSpec state_machine!?
pub open spec(checked) fn my_init() -> MapSpec::State {
    MapSpec::State { kmmap: TotalKMMap::empty() }
}

// TODO (jonh): Make this automated. A macro of some sort
pub open spec(checked) fn getInput(label: MapSpec::Label) -> Input {
    match label {
        MapSpec::Label::Query { input, output } => input,
        MapSpec::Label::Put { input, output } => input,
        MapSpec::Label::Noop { input, output } => input,
    }
}

pub open spec(checked) fn getOutput(label: MapSpec::Label) -> Output {
    match label {
        MapSpec::Label::Query { input, output } => output,
        MapSpec::Label::Put { input, output } => output,
        MapSpec::Label::Noop { input, output } => output,
    }
}

// MapSpec is our top-level trusted spec on what a Map (key-value store)
// is.
//
// We don't refine to this directly however as it doesn't provide
// a model that allows for proper concurrent disk I/O access (since there's
// no concept of asynchronicity between requesting an operation and
// getting the result).
//
// To achieve this we wrap MapSpec within a AsyncMap state machine. Then
// to allow for a model where crashes can occur, we then wrap the AsyncMap
// state machine within a CrashTolerantAsyncMap state machine specification.
state_machine!{ MapSpec {
    fields { pub kmmap: TotalKMMap }

    pub enum Label{
        Query{input: Input, output: Output},
        Put{input: Input, output: Output},
        Noop{input: Input, output: Output},
    }

    init!{
        // TODO: examine this weird nesting predicate stuff later
        // Core issue seems to be wanting to know the concrete initial
        // state outside of this state machine
        my_init_2() {
            init kmmap = my_init().kmmap;
        }
    }

    transition!{
        query(label: Label) {
            require let Label::Query{input, output} = label;

            require let Input::QueryInput { key } = input;
            require let Output::QueryOutput { value } = output;

            require pre.kmmap[key]->value == value;
        }
    }

    transition!{
        put(label: Label) {
            require let Label::Put{input, output} = label;

            require let Input::PutInput { key, value } = input;
            require let Output::PutOutput = output;

            update kmmap = pre.kmmap.insert(key, Message::Define{value});
        }
    }

    transition!{
        noop(label: Label) {
            require let Label::Noop{input, output} = label;

            require let Input::NoopInput = input;
            require let Output::NoopOutput = output;
        }
    }

    #[invariant]
    pub open spec(checked) fn the_inv(self) -> bool {
        &&& self.kmmap.wf()
    }

    #[inductive(my_init_2)]
    fn my_init_2_inductive(post: Self) { }
   
    #[inductive(query)]
    fn query_inductive(pre: Self, post: Self, label: Label) { }
   
    #[inductive(put)]
    fn put_inductive(pre: Self, post: Self, label: Label) {
//         let key = label.arrow_Put_input().arrow_PutInput_key();
//         let value = label.arrow_Put_input().arrow_PutInput_value();
//         assert( pre.kmmap.wf() );

        pre.kmmap.insert_lemma();
        // clumsily trigger lemma we just called
//         assert( pre.kmmap.insert(key, Message::Define{value}).wf() );
//         assert( post.kmmap.wf() );
    }
   
    #[inductive(noop)]
    fn noop_inductive(pre: Self, post: Self, label: Label) { }

    pub proof fn inv_next(pre: Self, post: Self, lbl: Label)
        requires pre.the_inv(), Self::next(pre, post, lbl)
        ensures post.the_inv()
    {
        reveal(MapSpec::State::next);
        reveal(MapSpec::State::next_by);

        let step = choose |step| Self::next_by(pre, post, lbl, step);
        match step {
            MapSpec::Step::query() => {
                Self::query_inductive(pre, post, lbl);
            },
            MapSpec::Step::put() => {
                Self::put_inductive(pre, post, lbl);
            },
            MapSpec::Step::noop() => {
                Self::noop_inductive(pre, post, lbl);
            },
            _ => {
//                assert(false);
            },
        }
    }
}}  // Async things


pub type ID = u64;

// wishing for genericity
#[derive(Debug)]
pub struct Request {
    pub input: Input,
    pub id: ID,
}

#[derive(Debug)]
pub struct Reply {
    pub output: Output,
    pub id: ID,
}

// Tenzin: this structure is also brought in from Dafny (see Async.s.dfy). What is
// the use of wrapping MapSpec::State in another struct? It's unclear.
// It does make it a separate type, but there's no clear reason for
// needing/wanting that where PersistentState is used in the original Dafny.
// It's potentially a constraint from the custom "functor modules" they
// used for templating modules. I think we should just delete this type.
// It causes confusion since there's so many names for things that are
// the same thing.
/// PersistentState represents the actual state of the AsyncMap (wraps
/// the true key-value store). Whenever an operation is executed the
/// PersistentState is updated.
#[verifier::ext_equal]
pub struct PersistentState {
    pub appv: MapSpec::State,
}

impl PersistentState {
    pub open spec(checked) fn ext_equal(self, other: PersistentState) -> bool {
        &&& self.appv.kmmap.ext_equal(other.appv.kmmap)
    }

    pub proof fn ext_equal_is_equality()
        ensures
            forall|a: PersistentState, b: PersistentState| a.ext_equal(b) == (a == b),
    {
    }
}

/// EphemeralState captures the relevant async information we need to
/// track whether operations violate linearizability (and thus enforce
/// in our transitions that all operations are linearizable from the
/// perspective of the client).
///
/// We view our EphemeralState as a set of outstanding client requests
/// that haven't been executed and a set of executed replies that have
/// yet to be delivered to the client.
#[verifier::ext_equal]
pub struct EphemeralState {
    // pub history: Set<ID>,   // auditor can only 
    /// The set of received but not yet executed requests.
    pub requests: Set<Request>,
    /// The set of executed but not yet delivered replies.
    pub replies: Set<Reply>,
}

// TODO(jonh): `error: state machine field must be marked public`: why make me type 'pub', then?
// It's our syntax!
// AsyncMap wraps a MapSpec with asynchrony. It represents a spec where
// map operations are broken down into 3 stages:
// - Requesting the operation
// - Executing the operation
// - Replying (delivering confirmation to client that operation was performed).
//
// An execution is considered valid as long as there's some sequence
// of events where all requests reflect side effects from all responses
// received strictly before request is fired. (Standard Distributed
// Systems linearizability).
state_machine!{ AsyncMap {
    pub enum Label { // Was AsyncMod.UIOp
        /// Request transition is labeled with the requested operation.
        RequestOp { req: Request },
        /// Execute transition is labeled with the requested operation that
        /// was executed and the produced reply.
        ExecuteOp { req: Request, reply: Reply },
        /// Reply transition is labeled with what reply is delivered.
        ReplyOp { reply: Reply },
    }

    pub open spec(checked) fn init_persistent_state() -> PersistentState {
        PersistentState { appv: my_init() }
    }

    pub open spec(checked) fn init_ephemeral_state() -> EphemeralState {
        EphemeralState{ requests: set!{}, replies: set!{} }
    }

    fields {
        /// Persistent State is the actual state of the map (the cumulative
        /// state after applying all executions so far).
        pub persistent: PersistentState,
        /// Ephemeral state is the set of to-be-executed requests and undelivered
        /// replies.
        pub ephemeral: EphemeralState,
    }

    /// The request transition corresponds to the client requesting an operation
    /// on the async map.
    transition!{ request(label: Label) {
        require let Label::RequestOp{ req } = label;

        // req.id not in the set of requests or replies
        // set of ids that have been involved in a request (history set)

        require !pre.ephemeral.requests.contains(req); // TODO: remove
        update ephemeral = EphemeralState { requests: pre.ephemeral.requests.insert(req), ..pre.ephemeral };
    } }

    /// The execute transition corresponds to the async map executing an outstanding
    /// request.
    transition!{ execute(label: Label, map_label: MapSpec::Label, post_persistent: PersistentState) {
        require let Label::ExecuteOp{ req, reply } = label;
        require req.id == reply.id;
        require pre.ephemeral.requests.contains(req);
        // Avoid collapsing replies together
        require !pre.ephemeral.replies.contains(reply);

        // TODO(jonh): Calling into a contained state machine is painful and long
        require getInput(map_label) == req.input;
        require getOutput(map_label) == reply.output;
        require MapSpec::State::next(
            pre.persistent.appv,
            post_persistent.appv,
            map_label
        );
        update persistent = post_persistent;

        update ephemeral = EphemeralState{
            requests: pre.ephemeral.requests.remove(req),
            replies: pre.ephemeral.replies.insert(reply),
        };
    } }

    transition!{ reply(label: Label) {
        require let Label::ReplyOp{ reply } = label;
        require pre.ephemeral.replies.contains(reply);
        update ephemeral = EphemeralState { replies: pre.ephemeral.replies.remove(reply), ..pre.ephemeral };
    } }
} }

pub type SyncReqId = u64;

/// A Version is a snapshot of a map (its key-value pairs). Specifically it wraps
/// a `MapSpec::State`.
#[verifier::ext_equal]
pub type Version = PersistentState;

pub open spec fn SingletonVersions(appv: MapSpec::State) -> FloatingSeq<Version> {
    FloatingSeq::new(0, 1, |i| Version{ appv })
}

// TODO(jonh): was sad to concretize Map (because no module functors). Is there a traity alternative?
// TODO(jonh): also sad to cram Async into CrashTolerant (because Async wasn't really a real state machine).
// How do we feel about going slightly off the state machine rails and having it fall apart?
// CrashTolerantAsyncMap is a, well, crash-tolerant asynchronous map. This is the true top-level
// spec which we refine our implementation to.
//
// The CrashTolerantAsyncMap wraps a AsyncMap, but adds the notion of versioning and crashing.
// Funnily enough we still have to make the crash operation itself "async" (in that we model
// it as an operation that has to be: requested, executed, replied to).
state_machine!{ CrashTolerantAsyncMap {
    fields {
        /// `versions` is a sequence of snapshots of the map state. `versions[i]` is a
        /// snapshot of the map when `map.seq_end == i` (i.e.: when the next LSN to-be-executed
        /// was `i`).
        ///
        /// Invariant: the first active
        /// index in the floating seq is the "stable index" (i.e.: the latest index which is
        /// crash-tolerant). AKA "stable LSN".
        ///
        /// All snapshots after the first index represent the sequence
        /// of states the Map has gone through that have yet to be persisted.
        /// Thus: the last state in `versions` represents the current up-to-date view
        /// of the map (not necessarily persisted).
        pub versions: FloatingSeq<Version>,
        /// The async ephemeral state (set of outstanding client requests and replies).
        /// See comments for EphemeralState struct.
        pub async_ephemeral: EphemeralState,
        /// The set of outstanding sync requests. Stored as a map mapping from a unique
        /// sync request ID to the version number "v" the map was at at the time the
        /// sync was requested. When we deliver a reply for a given sync request we
        /// ensure that the stable index is >= "v".
        pub sync_requests: Map<SyncReqId, nat>,
    }

    pub enum Label { // Unrolled version of Dafny labels for CrashTolerantMod(MapSpecMod)
        OperateOp{ base_op: AsyncMap::Label },
        CrashOp,
        SyncOp, // TODO(refactor): ExecuteSyncOp
        ReqSyncOp{ sync_req_id: SyncReqId },
        ReplySyncOp{ sync_req_id: SyncReqId },
        Noop,
    }
    // TODO: complete this state machine

    /// Return the latest index in `self.versions` which is stable (i.e.: persistent across
    /// crashes).
    pub open spec(checked) fn stable_index(self) -> int {
        self.versions.first_active_index()
    }

    // TODO(travis): init!{} with no body produces confusing error message
    init!{ initialize() {
        init versions = FloatingSeq::new(0, 1, |i| AsyncMap::State::init_persistent_state());
        init async_ephemeral = AsyncMap::State::init_ephemeral_state();
        init sync_requests = Map::empty();
    } }

    /// Returns true iff versions_prime is one of the following:
    /// - Equal to versions.
    /// - Equal to versions with a single version appended.
    pub open spec(checked) fn optionally_append_version(versions: FloatingSeq<Version>, versions_prime: FloatingSeq<Version>) -> bool
    {
      // new versions list is either some new thing appended to the old one,
      ||| (0 < versions_prime.len() && versions_prime.drop_last() == versions)
      // or unchanged. We allow unchanged in the trusted spec(checked) so that
      // implementations don't have to account for number of read-only (query) ops.
      ||| versions_prime == versions
    }

    /// Perform an operation at the AsyncMap state machine level (this could either be
    /// requesting an operation, executing it, or returning a reply to the client).
    /// Adds a version to self.versions if the execution modifies the state of the map.
    transition!{
        operate(
            label: Label,
            new_versions: FloatingSeq<Version>,
            new_async_ephemeral: EphemeralState)
        {
            // TODO: add label checking boilerplate
            require let Label::OperateOp{ base_op } = label;

            // want to introduce nondeterminism for new_versions, then write a predicate saying
            // which values are okay
            require State::optionally_append_version(pre.versions, new_versions);
            // What's the syntax for (a) consing up an AsyncMap object and (b) calling its implicit Next
            // predicate?
            require AsyncMap::State::next(
                AsyncMap::State { persistent: pre.versions.last(), ephemeral: pre.async_ephemeral },
                AsyncMap::State { persistent: new_versions.last(), ephemeral: new_async_ephemeral },
                base_op
            );

            update versions = new_versions;
            update async_ephemeral = new_async_ephemeral;
    } }

    /// Represents the map crashing. We go back to the stable version (the persisted version)
    /// and forget all outstanding requests and replies (both for AsyncMap and for Sync
    /// requests).
    transition!{
        crash(label: Label) {
            require let Label::CrashOp = label;

            // The new versions contains only one element: the first element of pre.versions
            // (since we maintain that the first element of pre.versions is always the
            // last stable state).
            update versions = pre.versions.get_prefix(pre.stable_index() + 1);
            update async_ephemeral = AsyncMap::State::init_ephemeral_state();
            update sync_requests = Map::empty();
        }
    }

    /// Perform a sync operation (moves the stable index forward). Doesn't need
    /// to be triggered by a client request.
    transition!{
        sync(label: Label, new_stable_index: int) {
            require let Label::SyncOp = label;

            // The new stable index just needs to be some valid index within
            // pre.versions (we allow the new stable index to be the old stable
            // index, although that would correspond to not necessarily actually
            // persisting anything).
            require pre.stable_index() <= new_stable_index < pre.versions.len();
            // We truncate the front of self.versions until the first index is the new
            // stable index.
            update versions = pre.versions.get_suffix(new_stable_index);
        }
    }

    /// req_sync represents a client requesting a sync operation. Allows us to do
    /// bookkeeping to specify when the reply is delivered that we actually followed
    /// good sync semantics (a reply to a sync should mean all observable state at
    /// time of sync is persisted).
    transition!{
        req_sync(label: Label) {
            require let Label::ReqSyncOp{ sync_req_id } = label;

            // TODO (tony): add Maps::contains to Pervasives
            require !pre.sync_requests.dom().contains(sync_req_id);
            update sync_requests =
                pre.sync_requests.insert(sync_req_id, (pre.versions.len() - 1) as nat);
        }
    }

    /// reply_sync represents responding to a client that a requested sync operation
    /// completed successfully.
    ///
    /// We ensure that at the time we deliver reply that our stable index is in fact
    /// >= the version at the time of the sync request.
    transition!{
        reply_sync(label: Label) {
            require let Label::ReplySyncOp{ sync_req_id } = label;

            // TODO (tony): add Maps::contains to Pervasives
            require pre.sync_requests.dom().contains(sync_req_id);

            require pre.sync_requests[sync_req_id] <= pre.stable_index();
            update sync_requests = pre.sync_requests.remove(sync_req_id);
        }
    }

    /// Noop transition allows lower level state machine (which refines to this) to
    /// do any internal bookkeeping (which isn't reflected in refined state) within a transition.
    transition!{
        noop(label: Label) {
            require let Label::Noop = label;
        }
    }

    //  TODO(jonh): Unhappy that the invariant (proof work) is in the same file as the model
    #[invariant]
    pub open spec(checked) fn the_inv(self) -> bool {
        &&& 0 < self.versions.len()
        &&& self.versions.is_active(self.versions.len() - 1)
    }

    #[inductive(initialize)]
    fn initialize_inductive(post: Self) { }

    #[inductive(operate)]
    fn operate_inductive(pre: Self, post: Self, label: Label, new_versions: FloatingSeq<Version>, new_async_ephemeral: EphemeralState) { }

    #[inductive(crash)]
    fn crash_inductive(pre: Self, post: Self, label: Label) { }

    #[inductive(sync)]
    fn sync_inductive(pre: Self, post: Self, label: Label, new_stable_index: int) { }

    #[inductive(req_sync)]
    fn req_sync_inductive(pre: Self, post: Self, label: Label) { }

    #[inductive(reply_sync)]
    fn reply_sync_inductive(pre: Self, post: Self, label: Label) { }

    #[inductive(noop)]
    fn noop_inductive(pre: Self, post: Self, label: Label) { }

    // TODO: jonh is sad that I can't put this invariant & proof elsewhere. We separate
    // our state machine definitions from our invariant & refinement proof text.
//    #[inductive(operate)]
//    fn operate_inductive(pre: Self, post: Self, op: AsyncUILabel) { }
}}

} // verus!
fn main() {}