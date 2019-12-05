include "ImplModel.i.dfy"
include "ImplModelCache.i.dfy"
include "../lib/Base/Option.s.dfy"
include "../lib/Base/Sets.i.dfy"
include "../PivotBetree/PivotBetreeSpec.i.dfy"
include "ModelBucket.i.dfy"

// See dependency graph in MainImpl.dfy

module ImplModelSucc { 
  import opened ImplModel
  import opened ImplModelIO
  import opened ImplModelCache

  import opened Options
  import opened Maps
  import opened Sets
  import opened Sequences
  import opened NativeTypes

  import opened BucketsLib
  import opened BucketWeights
  import opened Bounds
  import PivotsLib

  import opened ModelBucket
  import opened Lexicographic_Byte_Order

  import PBS = PivotBetreeSpec`Internal

  datatype PathResult =
      | Path(buckets: seq<Bucket>, upTo: Option<Key>)
      | Fetch(ref: BT.G.Reference)
      | Failure

  // TODO update lru queue when traversing

  function {:opaque} getPath(k: Constants, s: Variables, key: Key, acc: seq<Bucket>, upTo: Option<Key>, ref: BT.G.Reference, counter: uint64) : (pr : PathResult)
  requires Inv(k, s)
  requires s.Ready?
  decreases counter
  {
    if ref in s.cache then (
      var node := s.cache[ref];
      var r := Pivots.Route(node.pivotTable, key);
      var bucket := node.buckets[r];
      var acc' := acc + [bucket];
      var upTo' := 
        if r == |node.pivotTable| then (
          upTo
        ) else (
          var ub := node.pivotTable[r];
          if upTo.Some? then (
            var k: Key := if lt(upTo.value, ub) then upTo.value else ub;
            Some(k)
          ) else (
            Some(ub)
          )
        );

      if node.children.Some? then (
        if counter == 0 then (
          Failure
        ) else (
          getPath(k, s, key, acc', upTo', node.children.value[r], counter - 1)
        )
      ) else (
        Path(acc', upTo')
      )
    ) else (
      Fetch(ref)
    )
  }

  ////////////////
  //// doSucc

  function doSucc(k: Constants, s: Variables, io: IO, start: UI.RangeStart, maxToFind: int)
    : (Variables, IO, Option<SuccCollectionResult>)
  requires Inv(k, s)
  requires io.IOInit?
  requires maxToFind >= 1
  {
    if (s.Unready?) then (
      var (s', io') := PageInIndirectionTableReq(k, s, io);
      (s', io', None)
    ) else (
      var startKey := if start.NegativeInf? then [] else start.key;

      lemmaGetPathValidFetch(k, s, startKey, 40);
      var pr := getPath(k, s, startKey, [], None, BT.G.Root(), 40);

      match pr {
        case Path(buckets, upTo) => (
          var res := GetSuccessorInBucketStack(buckets, maxToFind, start, upTo);
          (s, io, Some(res))
        )
        case Fetch(ref) => (
          var (s', io') := PageInReq(k, s, io, ref);
          (s', io', None)
        )
        case Failure => (
          (s, io, None)
        )
      }
    )
  }

  /////////////////////////////////
  /////////////////////////////////
  ///////////////////////////////// Proof stuff
  /////////////////////////////////
  /////////////////////////////////

  predicate LookupBucketsProps(lookup: PBS.Lookup, buckets: seq<Bucket>, upTo: Option<Key>, startKey: Key)
  {
    && PBS.WFLookupForKey(lookup, startKey)
    && upTo == PBS.LookupUpperBound(lookup, startKey)
    && Last(lookup).node.children.None?
    && |lookup| == |buckets|
    && (forall i | 0 <= i < |lookup| :: buckets[i] == lookup[i].node.buckets[Pivots.Route(lookup[i].node.pivotTable, startKey)])
  }

  lemma lemmaGetPathResult(k: Constants, s: Variables, startKey: Key, acc: seq<Bucket>, lookup: PBS.Lookup, upTo: Option<Key>, ref: BT.G.Reference, counter: uint64)
  returns (lookup' : PBS.Lookup)
  requires Inv(k, s)
  requires s.Ready?
  requires ref in s.ephemeralIndirectionTable.graph
  requires |lookup| > 0 ==> PBS.WFLookupForKey(lookup, startKey)
  requires |lookup| > 0 ==> Last(lookup).node.children.Some?
  requires |lookup| > 0 ==> ref == Last(lookup).node.children.value[Pivots.Route(Last(lookup).node.pivotTable, startKey)]
  requires |lookup| == 0 ==> ref == BT.G.Root()
  requires upTo == PBS.LookupUpperBound(lookup, startKey)
  requires |lookup| == |acc|
  requires forall i | 0 <= i < |lookup| :: acc[i] == lookup[i].node.buckets[Pivots.Route(lookup[i].node.pivotTable, startKey)]
  requires forall i | 0 <= i < |lookup| :: lookup[i].ref in s.cache && lookup[i].node == INode(s.cache[lookup[i].ref])
  decreases counter
  ensures var pr := getPath(k, s, startKey, acc, upTo, ref, counter);
      && (pr.Fetch? ==> pr.ref in s.ephemeralIndirectionTable.locs)
      && (pr.Path? ==> LookupBucketsProps(lookup', pr.buckets, pr.upTo, startKey))
  {
    reveal_getPath();

    if ref in s.cache {
      var node := s.cache[ref];
      var r := Pivots.Route(node.pivotTable, startKey);
      var bucket := node.buckets[r];
      var acc1 := acc + [bucket];
      var lookup1 := lookup + [BT.G.ReadOp(ref, INode(node))];

      forall idx | PBS.ValidLayerIndex(lookup1, idx) && idx < |lookup1| - 1
      ensures PBS.LookupFollowsChildRefAtLayer(startKey, lookup1, idx)
      {
        if idx == |lookup1| - 2 {
          assert PBS.LookupFollowsChildRefAtLayer(startKey, lookup1, idx);
        } else {
          assert PBS.LookupFollowsChildRefAtLayer(startKey, lookup, idx);
          assert PBS.LookupFollowsChildRefAtLayer(startKey, lookup1, idx);
        }
      }

      var upTo' := 
        if r == |node.pivotTable| then (
          upTo
        ) else (
          var ub := node.pivotTable[r];
          if upTo.Some? then (
            var k: Key := if lt(upTo.value, ub) then upTo.value else ub;
            Some(k)
          ) else (
            Some(ub)
          )
        );

      PBS.reveal_LookupUpperBound();

      if node.children.Some? {
        if counter == 0 {
        } else {
          lemmaChildInGraph(k, s, ref, node.children.value[r]);

          lookup' := lemmaGetPathResult(k, s, startKey, acc1, lookup1, upTo', node.children.value[r], counter - 1);
        }
      } else {
        lookup' := lookup1;
      }
    } else {
    }
  }

  lemma lemmaGetPathValidFetch(k: Constants, s: Variables, startKey: Key, counter: uint64)
  requires Inv(k, s)
  requires s.Ready?
  decreases counter
  ensures var pr := getPath(k, s, startKey, [], None, BT.G.Root(), counter);
      && (pr.Fetch? ==> pr.ref in s.ephemeralIndirectionTable.locs)
  {
    PBS.reveal_LookupUpperBound();
    var _ := lemmaGetPathResult(k, s, startKey, [], [], None, BT.G.Root(), counter);
  }

  lemma lemmaGetPathValidLookup(k: Constants, s: Variables, startKey: Key, counter: uint64)
  returns (lookup' : PBS.Lookup)
  requires Inv(k, s)
  requires s.Ready?
  decreases counter
  ensures var pr := getPath(k, s, startKey, [], None, BT.G.Root(), counter);
      && (pr.Path? ==> LookupBucketsProps(lookup', pr.buckets, pr.upTo, startKey))
  {
    PBS.reveal_LookupUpperBound();
    lookup' := lemmaGetPathResult(k, s, startKey, [], [], None, BT.G.Root(), counter);
  }
}
