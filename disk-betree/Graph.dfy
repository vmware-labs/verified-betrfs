abstract module Graph {
  // Abstract features
  type Reference(!new,==)
  type Node(!new)
  function Root() : Reference
  function Successors(node: Node) : iset<Reference>

  type Graph = imap<Reference, Node>

  // TODO Transactable is a more natural place for this
  datatype Op =
    | AllocOp(ref: Reference, block: Node)
    | WriteOp(ref: Reference, block: Node)
}
