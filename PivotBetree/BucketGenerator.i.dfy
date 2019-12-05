include "BucketIterator.i.dfy"
//
// A mathematical description of bucket generators.
// It's like an iterator, but it doesn't directly refer to an actual bucket.
// The bucket may be implicit.
//

module BucketGenerator {
  import opened Options
  import opened Maps
  import opened BucketsLib
  import opened PivotsLib
  import opened ValueMessage
  import opened Sequences
  import opened BucketIterator

  datatype Generator =
    | BasicGenerator(
        // "Internals":
        bucket: Bucket,
        it: Iterator,

        // Bucket that the generator represents
        ghost remains: Bucket
      )

  protected predicate WF(g: Generator)
  {
    && WFIter(g.bucket, g.it)
    && (g.it.next.Done? ==> g.remains == map[])
    && (g.it.next.Next? ==> Keyspace.minimumOpt(g.remains.Keys) == Some(g.it.next.key))
  }

  // Generator operations:

  function {:opaque} GenTop(g: Generator) : (next : IteratorOutput)
  requires WF(g)
  ensures next.Done? ==> g.remains == map[]
  ensures next.Next? ==> Keyspace.minimumOpt(g.remains.Keys) == Some(next.key)
  {
    g.it.next
  }

  function {:opaque} GenPop(g: Generator) : (g' : Generator)
  requires WF(g)
  requires GenTop(g).Next?
  ensures WF(g')
  ensures g'.remains == MapRemove1(g.remains, GenTop(g).key)
  {
    BasicGenerator(
        g.bucket,
        IterInc(g.bucket, g.it),
        MapRemove1(g.remains, GenTop(g).key))
  }
}
