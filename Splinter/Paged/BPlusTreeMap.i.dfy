// Copyright 2018-2021 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, and University of Washington
// SPDX-License-Identifier: BSD-2-Clause

include "StampedMap.i.dfy"
include "MsgHistory.i.dfy"

abstract module BPlusTreeMap refines MapIfc {
  import opened TotalKMMapMod
  import opened StampedMapMod
  import opened MsgHistoryMod
  import opened ValueMessage
  import opened KeyType
  import opened LSNMod

  import KeySpace : Total_Order  // TODO(jonh): Functorize me

  //////////////////////////////////////////////////////////////////////////////
  // Define a B+ tree and its gritty bits

  // Left pivot is inclusive, right pivot is exclusive.
  datatype BPlusNode =
      IndexNode(pivots: seq<Key>, children: seq<BPlusNode>)
    | LeafNode(values: map<Key, Value>)
  {
    predicate WF() {
      && (IndexNode? ==>
        && 0 < |children| // a single-pivot index would be correct but useless (empty)
        && |pivots| == |children| + 1
        && KeySpace.IsStrictlySorted(pivots)
        )
    }

    predicate KeyBetween(lowInclusive: Key, needle: Key, highExclusive: Key)
    {
      && KeySpace.lte(lowInclusive, needle)
      && KeySpace.lt(needle, highExclusive)
    }

    predicate KeysBetween(lowInclusive: Key, needles: set<Key>, highExclusive: Key)
    {
      forall needle | needle in needles :: KeyBetween(lowInclusive, needle, highExclusive)
    }

    predicate ValidIndex()
      requires IndexNode?
    {
      forall pi | 0<=pi<|children| ::
          && KeysInRange(pivots[pi], pivots[pi+1], children[pi].Keys())
          && (match children[pi]
            case IndexNode(childPivots, _) =>
              && childPivots[0] == pivots[pi]
              && Last(childPivots) == pivots[pi+1]
              && ValidIndex(children[pi])
            case LeafNode(values) =>
              (forall k | k in values :: KeyBetween(pivots[pi], k, pivots[pi+1]))
            )
    }

    predicate Valid()
    {
      && WF()
      && (Index? ==> ValidIndex())
    }

    predicate KeyAtChild(pi: nat, k: Key)
      requires Index?
      requires Valid()
      requires 0<=pi<|children|
    {
      KeyBetween(pivots[pi], k, pivots[pi+1]) && k in children[pi].I()
    }

    function IndexI() : (out:map<Key, Value>)
      requires Index?
      requires Valid()
      ensures KeysBetween(pivots[0], out.Keys, Last(pivots))
    {
      var keys := set pi, k | KeyAtChild(pi, k);
      map  k | k in keys :: var pi :| KeyAtChild(pi, k); children[pi].I()[k]
    }

    function I() : (out:map<Key, Value>)
      requires Valid()
      ensures Index? ==> KeysBetween(pivots[0], out.Keys, Last(pivots))
    {
      match this
        case Leaf(values) => values
        case Index(pivots, children) => IndexI()
    }
  }

  //////////////////////////////////////////////////////////////////////////////
  // Satisfy the MapIfc

  type Map = BPlusNode

  predicate WF(mapp: Map)

  function I(mapp: Map) : (out: StampedMap)

  // "Accessors" that are restricted ways we expect coordination implementation
  // to need to inspect the map (efficiently)

  function Mkfs() : (out: Map)
    ensures WF(out)
    ensures I(out) == StampedMapMod.Empty()

  // The LSNs (exclusive) whose effect this map represents
  function SeqEnd(mapp: Map) : (out: LSN)
    requires WF(mapp)
    ensures out == I(mapp).seqEnd

  function ApplyPuts(mapp: Map, puts: MsgHistory) : (out: Map)
    requires WF(mapp)
    requires puts.WF()
    requires puts.CanFollow(SeqEnd(mapp))
    ensures WF(out)
    ensures I(out) == MapPlusHistory(I(mapp), puts)

  function Query(mapp: Map, key: Key) : (out: Value)
    requires WF(mapp)
    ensures assert TotalKMMapMod.AnyKey(key); out == I(mapp).mi[key].value
}
