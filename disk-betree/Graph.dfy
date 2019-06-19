abstract module Graph {
  // Abstract features
  type Reference(!new,==)
  type Node(!new)
  function Root() : Reference
  function Successors(node: Node) : iset<Reference>

  type Graph = imap<Reference, Node>
}
