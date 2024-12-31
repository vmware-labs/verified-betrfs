use builtin::*;
use vstd::prelude::*;
use vstd::rwlock::*;
use vstd::invariant::*;
use std::sync::Arc;
use vstd::thread::*;

mod frac;
use crate::frac::*;

verus!{

type ID = int;

trait CallBackSemantics : Sized{
    type Param;         // input of call back (ghost resource)
    type GhostResult;   // output of call back (e.g. fractional resource)
    type ExecResult;

    spec fn requires(id: ID, p: Self::Param, e: Self::ExecResult) -> bool
    ;

    spec fn ensures(id: ID, p: Self::Param, e: Self::GhostResult) -> bool
    ;
}

trait GenericCallBack<S: CallBackSemantics> : Sized {
    type CBResult; // external result

    spec fn inv(&self) -> bool
        ;

    spec fn id(&self) -> ID // value based on S?
        ;

    // _inv_namespaces
    spec fn inv_namespace(&self) -> int
        ;

    spec fn other_namespace(&self) -> int
        ;

    spec fn post(&self, r: &S::ExecResult, cbr: &Self::CBResult) -> bool
        ;

    proof fn cb(tracked self, tracked p: S::Param, e: &S::ExecResult)
        -> (tracked out: (S::GhostResult, Self::CBResult))
    requires
        self.inv(),
        S::requires(self.id(), p, *e),
    ensures
        S::ensures(self.id(), p, out.0),
        self.post(e, &out.1),
    opens_invariants [ self.inv_namespace(), self.other_namespace() ]
    ;
}

// NOTE: the only difference is the param type in the callback proof fn
// this is needed to untie the lifetime of the param from the callback struct
trait GenericReadCallBack<S: CallBackSemantics> : Sized {
    type CBResult; // external result

    spec fn inv(&self) -> bool
        ;

    spec fn id(&self) -> ID // value based on S?
        ;

    // _inv_namespaces
    spec fn inv_namespace(&self) -> int
        ;

    spec fn other_namespace(&self) -> int
        ;

    spec fn post(&self, r: &S::ExecResult, cbr: &Self::CBResult) -> bool
        ;

    proof fn cb(tracked self, tracked p: &S::Param, e: &S::ExecResult)
        -> (tracked out: (S::GhostResult, Self::CBResult))
    requires
        self.inv(),
        S::requires(self.id(), *p, *e),
    ensures
        S::ensures(self.id(), *p, out.0),
        self.post(e, &out.1),
    opens_invariants [ self.inv_namespace(), self.other_namespace() ]
    ;
}

// NOTE: a workaround for opens_invariants not taking a set of namespaces
// does not open other_namespace
trait GenericSingleInvCallBack<S: CallBackSemantics> : Sized {
    type CBResult; // external result

    spec fn inv(&self) -> bool
        ;

    spec fn id(&self) -> ID // value based on S?
        ;

    // _inv_namespaces
    spec fn inv_namespace(&self) -> int
        ;

    spec fn post(&self, r: &S::ExecResult, cbr: &Self::CBResult) -> bool
        ;

    proof fn cb(tracked self, tracked p: S::Param, e: &S::ExecResult)
        -> (tracked out: (S::GhostResult, Self::CBResult))
    requires
        self.inv(),
        S::requires(self.id(), p, *e),
    ensures
        S::ensures(self.id(), p, out.0),
        self.post(e, &out.1),
    opens_invariants [ self.inv_namespace() ]
    ;
}

// NOTE: the only difference is the param type in the callback proof fn
// this is needed to untie the lifetime of the param from the callback struct
trait GenericSingleInvReadCallBack<S: CallBackSemantics> : Sized {
    type CBResult; // external result

    spec fn inv(&self) -> bool
        ;

    spec fn id(&self) -> ID // value based on S?
        ;

    // _inv_namespaces
    spec fn inv_namespace(&self) -> int
        ;

    spec fn post(&self, r: &S::ExecResult, cbr: &Self::CBResult) -> bool
        ;

    proof fn cb(tracked self, tracked p: &S::Param, e: &S::ExecResult)
        -> (tracked out: (S::GhostResult, Self::CBResult))
    requires
        self.inv(),
        S::requires(self.id(), *p, *e),
    ensures
        S::ensures(self.id(), *p, out.0),
        self.post(e, &out.1),
    opens_invariants [ self.inv_namespace() ]
    ;
}

} // verus
