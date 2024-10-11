#![verifier::loop_isolation(false)]
#![allow(non_snake_case)]   // we should probably fix up the module names to be rust-snakey
#![allow(unused_imports)]

use builtin::*;
use builtin_macros::*;

use crate::spec::KeyType_t::*;
use crate::spec::MapSpec_t::*;
use crate::spec::SystemModel_t::*;
use crate::spec::Messages_t::*;


verus!{

pub trait ProgramModel {
    type State;
    // type Nondeterminism;

    spec fn init() -> Self::State
    ;

    // spec fn next(pre: Self::State, lbl: ProgramLabel, nd: Self::Nondeterminism) -> Option<Self::State>
    // ;

    // switch back to predicate style
    spec fn next(pre: Self::State, post: Self::State, lbl: ProgramLabel) -> bool
    ;

    // program model must always allow a new request to be accepted
    proof fn accept_request_always_enabled(pre: Self::State, req: Request) -> (post: Self::State)
    ensures Self::next(pre, post, ProgramLabel::AcceptRequest{req})
    ;
}

struct TrustedAPI<P: ProgramModel> {
    pub _p: std::marker::PhantomData<(P,)>,
    // TODO: ID to client map
}

// Prevent implementer from constructing Tokens (external body)
#[verifier::external_body]
#[verifier::reject_recursive_types(P)]
struct Token<P: ProgramModel> {
    state: Ghost<P::State>,
}

// Q(concurrency): can the auditor provide this interface without 
// knowing any concurrency strategy from the implementer side? 
// the provided TrustedAPI and token are what we expect 

impl<P: ProgramModel> Token<P> {
    #[verifier::external_body]
    pub closed spec fn view(&self) -> P::State {
        self.state@
    }

    // #[verifier::external_body]
    // pub closed spec fn is_app_token(&self) -> bool {
    //     true
    // }

    // #[verifier::external_body]
    // pub closed spec fn is_disk_token(&self) -> bool {
    //     true
    // }
}

// NOTE: `Tracked` keyword documentation can be found at
// https://verus-lang.github.io/verus/guide/reference-var-modes.html#cheat-sheet

// TrustedAPI is the interface provided by the auditor and is the only way for
// the implementer to interact with external world (application clients and disk).
// By defining this, the auditor can monitor all externally visible communication 
// and only allow such interactions if the implementor has proven that it is 
// allowed by the top level spec.

// NOTE(concurrency): P will be a verus sync trait to support shards
impl<P: ProgramModel> TrustedAPI<P> {
    // NOTE(concurrency): Right now P contains the entire state of the program model, 
    // in a concurrent world P would instead be a sharded state of the program model.
    // In a sharded world, the implementer may track requests and replies as multiset for easy composition.

    // NOTE(auditor): the auditor promises that each request has a unique ID (see SystemModel_t)
    // NOTE(concurrency): token passed in may be empty, token returned will be pre + new request
    #[verifier::external_body]
    pub fn receive_request(&self, pre: Tracked<Token<P>>) -> (req_post: (Request, Tracked<Token<P>>))
    ensures
        // ensures that the program model is able to advance upon receiving a request
        // safe to say so because of accept_request_always_enabled
        P::next(pre@@, req_post.1@@, ProgramLabel::AcceptRequest{req: req_post.0}),
    {
        // TODO(implementer): reads in a request, assign a unique ID,
        // for now pretend the user called for a query of key 0
        let req = Request {
            input: Input::QueryInput{ key: Key(0) },
            id: 0, 
        };
        (req, Tracked::assume_new())
    }

    // NOTE(auditor): after the implementation physically computes the reply and prove that the reply
    // corresponds to a valid transition, it may receive a token that allows for the reply to be sent
    #[verifier::external_body]
    proof fn execute(&self, tracked pre: Token<P>, post: Ghost<P::State>, req: &Request, reply: &Reply) -> (tracked out: Token<P>)
    requires
        P::next(pre@, post@, ProgramLabel::Execute{req: *req, reply: *reply}),
    ensures
        post@ == out@,
    {
        unimplemented!()
        //Tracked::assume_new()
    }

    // NOTE(concurrency): in a concurrent world there is no need to return a token, as pre should contain the 
    // reply token and is consumed by this function, for generality this API can just return an empty P for return
    #[verifier::external_body]
    pub fn send_reply(&self, reply: Reply, pre: Tracked<Token<P>>, post: Ghost<P::State>) -> (out: Tracked<Token<P>>)
    requires
        P::next(pre@@, post@, ProgramLabel::DeliverReply{reply}),
    ensures
        post@ == out@@,
    {
        // TODO(implementer): send reply to client, update ID to client map
        Tracked::assume_new()
//         Tracked(Ghost(P::next(pre@@, ProgramLabel::DeliverReply{reply}, nd@).unwrap()))
    }
}

//////////////////////////////////////////////////////////////////////////////

// use a state machine macro here?
pub struct ConcreteProgramModelState {
}

// pub struct ConcreteProgramModelNondeterminism {
// }

pub struct ConcreteProgramModel {
}

impl ProgramModel for ConcreteProgramModel {
    type State = ConcreteProgramModelState;
    // type Nondeterminism = ConcreteProgramModelNondeterminism;

    open spec fn init() -> Self::State
    {
        ConcreteProgramModelState{}
    }

    open spec fn next(pre: Self::State, post: Self::State, lbl: ProgramLabel) -> bool
    {
        true
    }

    proof fn accept_request_always_enabled(pre: Self::State, req: Request) -> (post: Self::State)
    {
        assume( false );
        (pre)
    }
}

struct Program {
}

impl Program {
    pub closed spec fn view(&self) -> <ConcreteProgramModel as ProgramModel>::State {
        ConcreteProgramModelState{}
    }

    pub fn compute_reply(&mut self, req: Request) -> Reply
    {
        Reply {
            output: Output::QueryOutput{ value: Value(0)},
            id: req.id,
        }
    }

    pub fn verified_main(&mut self, api: &TrustedAPI<ConcreteProgramModel>, Tracked(pm): Tracked<Token<ConcreteProgramModel>>) 
    requires
        pm@ == ConcreteProgramModel::init(),
    {
        let tracked mut pm = pm;
        loop {
            assert(self@ == pm@);

            // let nd = Ghost(ConcreteProgramModelNondeterminism{});
            let (req, Tracked(req_pm)) = api.receive_request(Tracked(pm));
            proof { pm = req_pm; }

            // TODO: advance concrete program state s.t.
            assert(self@ == pm@);
            
            // let ghost pre = self@;
            let reply = self.compute_reply(req);
            // let ghost post = self@;
            // assert(ConcreteProgramModel::next(pre, post, Execute(req, reply)));
            proof { pm = api.execute(pm, Ghost(self@), &req, &reply); }

            assert(self@ == pm@);

            let ghost pre = self@;
            // TODO: remove reply from concrete program state
            let Tracked(reply_pm) = api.send_reply(reply, Tracked(pm), Ghost(self@));
            proof { pm = reply_pm; }
        }

        // single threaded model:
        // 1 program model being tracked the entire execution, handed to application
        // at receive_request, returned to client upon a reply
    }
}

}
