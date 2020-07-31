include "BetreeSpec.i.dfy"

module SmallStepBetreeSpec {
  import opened KeyType
  import opened ValueType
  import opened G = BetreeGraph
  import opened Maps

  datatype QueryState =
    | InProgress(key: Key, delta: G.M.Message, ref: Reference)
    | Finished(key: Key, answer: Value)

  datatype QueryDescent = QueryDescent(
      query: QueryState,
      parent: Node,
      query': QueryState)

  predicate ValidQueryDescent(q: QueryDescent) {
    //&& WFNode(q.parent)
    && q.query.InProgress?
    && q.query'.key == q.query.key
    && q.query.key in q.parent.buffer
    && if G.M.Merge(q.query.delta, q.parent.buffer[q.query.key]).Define? then (
      && q.query' == Finished(q.query.key, G.M.Merge(q.query.delta, q.parent.buffer[q.query.key]).value)
    ) else (
      && q.query'.InProgress?
      && q.query'.delta == G.M.Merge(q.query.delta, q.parent.buffer[q.query.key])
      && IMapsTo(q.parent.children, q.query.key, q.query'.ref)
    )
  }

  function QueryDescentReads(q: QueryDescent): seq<ReadOp>
    requires ValidQueryDescent(q)
  {
    [ReadOp(q.query.ref, q.parent)]
  }

  function QueryDescentOps(q: QueryDescent): seq<Op> {
    []
  }

  datatype BetreeSmallStep =
    | BetreeQueryDescent(q: QueryDescent)

  // jonh: can this be called 'Next' at this layer?
  predicate ValidBetreeSmallStep(step: BetreeSmallStep)
  {
    match step {
      case BetreeQueryDescent(q) => ValidQueryDescent(q)
    }
  }

  function BetreeSmallStepReads(step: BetreeSmallStep) : seq<ReadOp>
  requires ValidBetreeSmallStep(step)
  {
    match step {
      case BetreeQueryDescent(q) => QueryDescentReads(q)
    }
  }

  function BetreeSmallStepOps(step: BetreeSmallStep) : seq<Op>
  requires ValidBetreeSmallStep(step)
  {
    match step {
      case BetreeQueryDescent(q) => QueryDescentOps(q)
    }
  }
}
