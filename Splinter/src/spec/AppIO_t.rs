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
    type Nondeterminism;

    spec fn init() -> Self::State
    ;

    spec fn next(pre: Self::State, lbl: ProgramLabel, nd: Self::Nondeterminism) -> Option<Self::State>
    ;

    proof fn accept_request_always_enabled(pre: Self::State, req: Request) -> (out: (Self::Nondeterminism, Self::State))
    ensures Self::next(pre, ProgramLabel::AcceptRequest{req}, out.0) == Some(out.1)
    ;
}

struct TrustedAPI<P: ProgramModel> {
    pub _p: std::marker::PhantomData<(P,)>,
}

// Prevent implementer from constructing Tokens. (or use private struct?)
#[verifier::external_body]
#[verifier::reject_recursive_types(P)]
struct Token<P: ProgramModel> {
    state: Ghost<P::State>,
}

impl<P: ProgramModel> Token<P> {
    #[verifier::external_body]
    pub closed spec fn view(&self) -> P::State {
        self.state@
    }
}

// You REALLY want to read
// https://verus-lang.github.io/verus/guide/reference-var-modes.html#cheat-sheet

// how application interacts with unverified clients
impl<P: ProgramModel> TrustedAPI<P> {
    // Tracked is not a spec type but a linear type that must be consumed

    #[verifier::external_body]
    pub fn receive_request(&self, pre: Tracked<Token<P>>, nd: Ghost<P::Nondeterminism>) -> (req_post: (Request, Tracked<Token<P>>))
    ensures
        P::next(pre@@, ProgramLabel::AcceptRequest{req: req_post.0}, nd@) == Some(req_post.1@@),
    {
        // Pretend the user called for a query of key 0
        let req = Request {
            input: Input::QueryInput{ key: Key(0) },
            id: 0,
        };
//         let ghost o_post = P::next(pre@, ProgramLabel::AcceptRequest{req}, nd@);
//         assert( o_post is Some );
//         let tpost = Token{state: o_post.unwrap()};  // This code can call the ctor.
        (req, Tracked::assume_new())
    }

    #[verifier::external_body]
    proof fn execute(&self, tracked pre: Token<P>, req: &Request, reply: &Reply, nd: Ghost<P::Nondeterminism>) -> (tracked post: Token<P>)
    requires
        P::next(pre@, ProgramLabel::Execute{req: *req, reply: *reply}, nd@) is Some,
    ensures
        Some(post@) == P::next(pre@, ProgramLabel::Execute{req: *req, reply: *reply}, nd@),
    {
        unimplemented!()
        //Tracked::assume_new()
    }

    #[verifier::external_body]
    pub fn send_reply(&self, reply: Reply, pre: Tracked<Token<P>>, nd: Ghost<P::Nondeterminism>) -> (post: Tracked<Token<P>>)
    requires
        P::next(pre@@, ProgramLabel::DeliverReply{reply}, nd@) is Some,
    ensures
        Some(post@@) == P::next(pre@@, ProgramLabel::DeliverReply{reply}, nd@),
    {
        // TODO: actually transmit the reply
        Tracked::assume_new()
//         Tracked(Ghost(P::next(pre@@, ProgramLabel::DeliverReply{reply}, nd@).unwrap()))
    }
}

//////////////////////////////////////////////////////////////////////////////

// use a state machine macro here?
pub struct ConcreteProgramModelState {
}

pub struct ConcreteProgramModelNondeterminism {
}

pub struct ConcreteProgramModel {
}

impl ProgramModel for ConcreteProgramModel {
    type State = ConcreteProgramModelState;
    type Nondeterminism = ConcreteProgramModelNondeterminism;

    open spec fn init() -> Self::State
    {
        ConcreteProgramModelState{}
    }

    open spec fn next(pre: Self::State, lbl: ProgramLabel, nd: Self::Nondeterminism) -> Option<Self::State>
    {
        None
    }

    proof fn accept_request_always_enabled(pre: Self::State, req: Request) -> (out: (Self::Nondeterminism, Self::State))
    {
        assume( false );
        (ConcreteProgramModelNondeterminism{}, pre)
    }
}

struct Program {
}

impl Program {

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
            let nd = Ghost(ConcreteProgramModelNondeterminism{});
            let (req, Tracked(req_pm)) = api.receive_request(Tracked(pm), nd);
            proof { pm = req_pm; }
            let reply = self.compute_reply(req);

            proof { pm = api.execute(pm, &req, &reply, nd); }

            let Tracked(reply_pm) = api.send_reply(reply, Tracked(pm), nd);
            proof { pm = reply_pm; }
        }
        // single threaded model:
        // 1 program model being tracked the entire execution, handed to application
        // at receive_request, returned to client upon a reply

    }
}

}
