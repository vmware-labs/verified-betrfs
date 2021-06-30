include "AtomicStateMachine.s.dfy"

module AsyncMod(atomic: AtomicStateMachineMod) {
  type ID(==, !new)
  datatype Request = Request(input: atomic.Input, id: ID)
  datatype Reply = Reply(output: atomic.Output, id: ID)

  datatype Variables = Variables(mapv: atomic.Variables, requests: set<Request>, replies: set<Reply>)

  function InitState() : Variables {
    Variables(atomic.InitState(), {}, {})
  }

  predicate DoRequest(v: Variables, v': Variables, req: Request) {
    // TODO Probably should disallow ID conflicts
    && v' == v.(requests := v.requests + {req})
  }

  // The serialization point for this request
  predicate DoExecute(v: Variables, v': Variables, req: Request, reply: Reply) {
    && reply.id == req.id
    && req in v.requests
    && atomic.Next(v.mapv, v'.mapv, req.input, reply.output)
    && v'.requests == v.requests - {req}
    && v'.replies == v.replies + {reply}
  }

  predicate DoReply(v: Variables, v': Variables, reply: Reply)
  {
    && reply in v.replies
    && v' == v.(replies := v.replies - {reply})
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
