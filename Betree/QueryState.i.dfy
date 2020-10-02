include "BetreeSpec.i.dfy"

module QueryStates {
  import opened G = BetreeGraph
  import opened KeyType
  import opened ValueType
  import opened BetreeSpec`Internal
  import opened Maps

  //// Query Descent

  datatype QueryState =
    | InProgress(key: Key, delta: G.M.Delta, ref: Reference)
    | Finished(key: Key, answer: Value)
  
  datatype QueryDescent = QueryDescent(
      query: QueryState,
      parent: Node,
      query': QueryState)

  predicate ValidQueryDescent(q: QueryDescent) {
    && WFNode(q.parent)
    && q.query.InProgress?
    && q.query'.key == q.query.key
    && if q.parent.buffer[q.query.key].Define? then (
      && q.query' == Finished(
        q.query.key,
        G.M.ApplyDelta(q.query.delta, q.parent.buffer[q.query.key].value))
    ) else (
      && q.query'.InProgress?
      && q.query'.delta == G.M.CombineDeltas(q.query.delta, q.parent.buffer[q.query.key].delta)
      && IMapsTo(q.parent.children, q.query.key, q.query'.ref)
    )
  }

  function QueryDescentReads(q: QueryDescent): seq<ReadOp>
    requires ValidQueryDescent(q)
  {
    [ReadOp(q.query.ref, q.parent)]
  }

  function QueryDescentOps(q: QueryDescent): seq<Op>
  {
    []
  }
}
