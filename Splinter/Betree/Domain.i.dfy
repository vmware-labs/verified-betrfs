// Copyright 2018-2021 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, and University of Washington
// SPDX-License-Identifier: BSD-2-Clause

include "PagedBetree.i.dfy"
include "../../lib/Base/total_order.i.dfy"
include "../../lib/Buckets/BoundedPivotsLib.i.dfy"

module DomainMod {
  import opened KeyType
  import opened Upperbounded_Lexicographic_Byte_Order_Impl
  import opened Upperbounded_Lexicographic_Byte_Order_Impl.Ord
  import opened BoundedPivotsLib

  type Element = Upperbounded_Lexicographic_Byte_Order_Impl.Ord.Element

  // end is exclusive
  datatype Domain = EmptyDomain | Domain(start: Element, end: Element)
  {
    // TODO(tony/jonh): Side-quest: get ride of all this opaque nonsense! I think we fixed it at the root, in BoundedPivotsLib.
    // Key comparisons are a trigger party
    predicate {:opaque} SaneKeys()
    {
      && (!EmptyDomain? ==>
          && lt(start, end) // TODO(timeout): sure wish the opaque were working
          && start.Element?
          && ElementIsKey(start)
          && (end.Element? ==> ElementIsKey(end))
        )
    }

    predicate WF() {
      && SaneKeys()
    }

    predicate Contains(key: Key) {
      && !EmptyDomain?
      && lte(start, Element(key)) // TODO(timeout): sure wish the opaque were working
      && lt(Element(key), end)
    }

    // TODO(jonh): Why are these unused?
//    function IntersectInner(r2: Domain) : Domain
//      requires Domain?
//      requires r2.Domain?
//      requires lte(start, r2.start)
//    {
//      if lte(end, r2.start)
//      then EmptyDomain
//      else if lt(end, r2.end)
//      then Domain(r2.start, end)
//      else Domain(r2.start, r2.end)
//    }
//
//    function Intersect(r2: Domain) : Domain
//    {
//      if EmptyDomain? || r2.EmptyDomain?
//      then this
//      else if lte(start, r2.start)
//      then this.IntersectInner(r2)
//      else r2.IntersectInner(this)
//    }

    // Interpret a domain for use with an abstract Buffer.
    function KeySet() : iset<Key>
    {
      iset key | Contains(key)
    }
  }

  function TotalDomain() : (out: Domain)
    ensures out.WF()
    ensures out.Domain?
  {
    var out := Domain(Upperbounded_Lexicographic_Byte_Order_Impl.Ord.GetSmallestElement(), Max_Element);
    out.reveal_SaneKeys();
    out
  }
}
