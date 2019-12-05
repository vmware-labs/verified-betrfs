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
    | MergeGenerator(
        // "Internals":
        top: Generator,
        bot: Generator,
        next: IteratorOutput,

        // Bucket that the generator represents
        ghost remains: Bucket
      )

  protected predicate WF(g: Generator)
  {
    && (g.BasicGenerator? ==> (
      && WFIter(g.bucket, g.it)
      && (g.it.next.Done? ==> g.remains == map[])
      && (g.it.next.Next? ==> Keyspace.minimumOpt(g.remains.Keys) == Some(g.it.next.key))
      && (g.it.next.Next? ==> g.remains == 
            map k | k in g.bucket && Keyspace.lte(g.it.next.key, k) :: g.bucket[k])
    ))
    && (g.MergeGenerator? ==> (
      && WF(g.top)
      && WF(g.bot)
      && (g.next.Next? ==> (
        && (forall k | k in g.top.remains :: Keyspace.lt(g.next.key, k))
        && (forall k | k in g.bot.remains :: Keyspace.lt(g.next.key, k))
        && g.remains == Lump(g.top.remains, g.bot.remains)[g.next.key := g.next.msg]
      ))
      && (g.next.Done? ==> (
        && g.top.remains == map[]
        && g.bot.remains == map[]
        && g.remains == map[]
      ))
    ))
  }

  // Generator operations:

  lemma lemmaMergeGenTop(g: Generator)
  requires WF(g)
  requires g.MergeGenerator?
  ensures g.next.Next? ==> Keyspace.minimumOpt(g.remains.Keys) == Some(g.next.key);
  {
    reveal_Lump();
    if g.next.Next? {
      assert g.next.key in g.remains.Keys;
      //assert forall k | k in g.remains.Keys :: Keyspace.lte(g.next.key, k);
      //assert Keyspace.minimumOpt(g.remains.Keys) == Some(g.next.key);
    }
  }

  function {:opaque} GenTop(g: Generator) : (next : IteratorOutput)
  requires WF(g)
  ensures next.Done? ==> g.remains == map[]
  ensures next.Next? ==> Keyspace.minimumOpt(g.remains.Keys) == Some(next.key)
  {
    match g {
      case BasicGenerator(bucket, it, remains) => (
        //assert g.it.next.Next? ==> Keyspace.minimumOpt(g.remains.Keys) == Some(g.it.next.key);
        g.it.next
      )
      case MergeGenerator(top, bot, next, remains) => (
        lemmaMergeGenTop(g);
        g.next
      )
    }
  }

  function BasicGenPop(g: Generator) : (g' : Generator)
  requires WF(g)
  requires GenTop(g).Next?
  requires g.BasicGenerator?
  {
    var remains := MapRemove1(g.remains, GenTop(g).key);

    BasicGenerator(
      g.bucket,
      IterInc(g.bucket, g.it),
      remains)
  }

  lemma lemmaBasicGenPop(g: Generator)
  requires BasicGenPop.requires(g)
  ensures WF(BasicGenPop(g))
  {
    var g' := BasicGenPop(g);
    if g'.it.next.Done? {
      forall k | k in g'.remains
      ensures false
      {
        noKeyBetweenIterAndIterInc(g.bucket, g.it, k);
      }
    }
    if g'.it.next.Next? {
      IterIncKeyGreater(g.bucket, g.it);
      //assert Keyspace.lte(g.it.next.key, g'.it.next.key);
      //assert g'.it.next.key in g.remains.Keys;
      //assert g'.it.next.key != GenTop(g).key;
      assert g'.it.next.key in g'.remains.Keys;
      forall k | k in g'.remains.Keys
      ensures Keyspace.lte(g'.it.next.key, k)
      {
        noKeyBetweenIterAndIterInc(g.bucket, g.it, k);
      }
    }
  }

  function MergeGenPop(g: Generator) : (g' : Generator)
  requires WF(g)
  requires GenTop(g).Next?
  requires g.MergeGenerator?
  decreases g, 0
  {
    var remains := MapRemove1(g.remains, GenTop(g).key);

    if GenTop(g.top).Next? && GenTop(g.bot).Next?
        && GenTop(g.top).key == GenTop(g.bot).key then (
      MergeGenerator(
        GenPop(g.top),
        GenPop(g.bot),
        Next(GenTop(g.top).key,
            Merge(GenTop(g.top).msg, GenTop(g.bot).msg)),
        remains)
    ) else if GenTop(g.top).Next?
        && (GenTop(g.bot).Next? ==> Keyspace.lt(GenTop(g.top).key, GenTop(g.bot).key)) then (
      MergeGenerator(
        GenPop(g.top),
        g.bot,
        GenTop(g.top),
        remains)
    ) else if GenTop(g.bot).Next? then (
      MergeGenerator(
        g.top,
        GenPop(g.bot),
        GenTop(g.bot),
        remains)
    ) else (
      MergeGenerator(
        g.top,
        g.bot,
        Done,
        remains)
    )
  }

  lemma lemmaMergeGenPop(g: Generator)
  requires WF(g)
  requires GenTop(g).Next?
  requires g.MergeGenerator?
  decreases g, 1
  ensures WF(MergeGenPop(g))
  {
    reveal_Lump();
    var g' := MergeGenPop(g);
    assert g'.MergeGenerator?;
  }

  function {:opaque} GenPop(g: Generator) : (g' : Generator)
  requires WF(g)
  requires GenTop(g).Next?
  ensures WF(g')
  ensures g'.remains == MapRemove1(g.remains, GenTop(g).key)
  decreases g, 2
  {
    reveal_GenTop();

    match g {
      case BasicGenerator(bucket, it, remains) => (
        lemmaBasicGenPop(g);
        BasicGenPop(g)
      )
      case MergeGenerator(top, bot, next, remains) => (
        lemmaMergeGenPop(g);
        MergeGenPop(g)
      )
    }
  }

  function {:opaque} GenLump(top: Generator, bot: Generator) : (g : Generator)
  requires WF(top)
  requires WF(bot)
  ensures WF(g)
  {
  }
}
