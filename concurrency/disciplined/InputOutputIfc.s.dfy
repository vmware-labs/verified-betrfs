// The general shape of a state machine interface.

module InputOutputIfc {
  type Input(!new)
  type Output(!new)

  datatype Op = Op(input: Input, output: Output)
}
