include "InfiniteLog.i.dfy"

module InfiniteLogTokens(nrifc: NRIfc) {
  import opened RequestIds
  import opened Options
  import opened IL = InfiniteLogSSM(nrifc)

  /////////////////////
  // Token types. These represent the smallest discrete parts of the InfiniteLog state.
  // This is a way of dividing up the state into the pieces it will be convenient to
  // manipulate in our program.

  datatype {:glinear_fold} Readonly = Readonly(rid: RequestId, rs: ReadonlyState)
  {
    function defn(): M {
      M(map[], None, map[], map[], None, map[rid := rs], map[], map[])
    }
  }

  datatype {:glinear_fold} Ctail = Ctail(ctail: nat)
  {
    function defn(): M {
      M(map[], None, map[], map[], Some(ctail), map[], map[], map[])
    }
  }

  datatype {:glinear_fold} LocalTail = LocalTail(nodeId: NodeId, localTail: nat)
  {
    function defn(): M {
      M(map[], None, map[], map[nodeId := localTail], None, map[], map[], map[])
    }
  }

  datatype {:glinear_fold} Replica = Replica(nodeId: NodeId, state: nrifc.NRState)
  {
    function defn(): M {
      M(map[], None, map[nodeId := state], map[], None, map[], map[], map[])
    }
  }

  /////////////////////
  // The transitions.
  // These let us transform ghost state into other ghost state to represent
  // InfiniteLog transitions.

  // This lets us perform the transition
  //
  //    Readonly(rid, ReadonlyInit(op))         , Ctail(ctail)
  //      -->
  //    Readonly(rid, ReadonlyCtail(op, ctail)) , Ctail(ctail)
  //
  // which is effectively the `TransitionReadonlyReadCtail` transition.
  //
  // Note that it takes a `glinear` Readonly object and returns a new `glinear` Readonly
  // object. Since we only read from `ctail`, we don't need to update it, so we pass in
  // a `gshared` Ctail object. (This can be thought of a a readonly borrowed reference
  // to the Ctail object).

  glinear method perform_TransitionReadonlyReadCtail(
      glinear readonly: Readonly,
      gshared ctail: Ctail)
  returns (glinear readonly': Readonly)
  requires readonly.rs.ReadonlyInit?
  ensures readonly' == Readonly(readonly.rid, ReadonlyCtail(readonly.rs.op, ctail.ctail))
  //{
    // TODO fill in this body by showing that the transition in the contract corresponds to
    // the `TransitionReadonlyReadCtail` transition defined in InfiniteLog.
    // This requires calling into special "built-in" axioms provided by the framework
  //}

  //    Readonly(rid, ReadonlyCtail(op, ctail))               , LocalTail(nodeId, ltail)
  //      -->
  //    Readonly(rid, ReadonlyReadyToRead(op, nodeId, ctail)) , LocalTail(nodeId, ltail)

  glinear method perform_TransitionReadonlyReadyToRead(
      glinear readonly: Readonly,
      gshared ltail: LocalTail)
  returns (glinear readonly': Readonly)
  requires readonly.rs.ReadonlyCtail?
  requires ltail.localTail >= readonly.rs.ctail
  ensures readonly' == Readonly(readonly.rid,
      ReadonlyReadyToRead(readonly.rs.op, ltail.nodeId, readonly.rs.ctail))
  //{
    //TODO
  //}

  //    Readonly(rid, ReadonlyReadyToRead(op, nodeId, ctail)) , Replica(nodeId, state)
  //      -->
  //    Readonly(rid, ReadonlyDone(ret))                      , Replica(nodeId, state)

  glinear method perform_ReadonlyDone(
      glinear readonly: Readonly,
      gshared replica: Replica)
  returns (glinear readonly': Readonly)
  requires readonly.rs.ReadonlyReadyToRead?
  requires replica.nodeId == readonly.rs.nodeId
  ensures readonly' == Readonly(readonly.rid,
      ReadonlyDone(readonly.rs.op, nrifc.read(replica.state, readonly.rs.op), readonly.rs.ctail))
  //{
    //TODO
  //}
}
