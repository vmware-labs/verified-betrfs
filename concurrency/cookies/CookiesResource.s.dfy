module CookieIfc refines InputOutputIfc {
  datatype Input = Input(butter: nat, sugar: nat)
  datatype Output = Output(cookies: nat)
}

module CookieSpec refines StateMachine(CookieIfc) {
  datatype Variables = Variables(butter: nat, sugar: nat)

  predicate Init(s: Variables) {
    && s.butter == 0
    && s.sugar == 0
  }

  predicate Next(s: Variables, s': Variables, op: Ifc.Op) {
    match op {
      case Op(input, output) => (
        exists num_batches ::
          && batches <= s.butter + input.butter
          && batches <= s.sugar + input.sugar
          && s'.butter == s.butter + input.butter - batches
          && s'.sugar == s.sugar + input.sugar - batches
          && output == Output(6 * num_batches)
      )
    }
  }
}
