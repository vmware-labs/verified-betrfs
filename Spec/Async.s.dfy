include "AtomicStateMachine.s.dfy"

module AsyncMod(atomic: AtomicStateMachineMod) {
  type ID(==, !new)
  datatype Request = Request(input: atomic.Input, id: ID)
  datatype Reply = Reply(output: atomic.Output, id: ID)

  datatype PersistentState = PersistentState(appv: atomic.Variables)

  // This "extra state" is carried around separately by the outer state machine
  // (CrashTolerant<>) because it disappears on Crash. (You could also imagine
  // carrying it inside the Variables and deleting it, but that's ugly in a
  // different way).
  datatype EphemeralState = EphemeralState(requests: set<Request>, replies: set<Reply>)

  datatype Variables = Variables(persistent: PersistentState, ephemeral: EphemeralState)

  function InitPersistentState() : PersistentState {
    PersistentState(atomic.InitState())
  }

  function InitEphemeralState() : EphemeralState {
    EphemeralState({}, {})
  }

  predicate DoRequest(v: Variables, v': Variables, req: Request) {
    && req !in v.ephemeral.requests  // disallow ID conflicts
    && v' == v.(ephemeral := v.ephemeral.(requests := v.ephemeral.requests + {req}))
  }

  // The serialization point for this request
  predicate DoExecute(v: Variables, v': Variables, req: Request, reply: Reply) {
    && reply.id == req.id
    && req in v.ephemeral.requests
    && reply !in v.ephemeral.replies  // disallow ID conflicts
    && atomic.Next(v.persistent.appv, v'.persistent.appv, req.input, reply.output)
    && v'.ephemeral.requests == v.ephemeral.requests - {req}
    && v'.ephemeral.replies == v.ephemeral.replies + {reply}
  }

  predicate DoReply(v: Variables, v': Variables, reply: Reply)
  {
    && reply in v.ephemeral.replies
    && v' == v.(ephemeral := v.ephemeral.(replies := v.ephemeral.replies - {reply}))
  }

  datatype UIOp =
    | RequestOp(req: Request)
    | ExecuteOp(req: Request, reply: Reply)
    | ReplyOp(reply: Reply)

  predicate NextStep(v: Variables, v': Variables, op: UIOp) {
    match op
      case RequestOp(req) => DoRequest(v, v', req)
      case ExecuteOp(req, reply) => DoExecute(v, v', req, reply)
      case ReplyOp(reply) => DoReply(v, v', reply)
  }

  predicate Next(v: Variables, v': Variables) {
    exists step :: NextStep(v, v', step)
  }
}
