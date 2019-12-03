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
  //// getMinKey

  function getMinKeyIter(iters: seq<Iterator>, i: int, cur: Option<Key>) : (res : Option<Key>)
  requires 0 <= i <= |iters|
  decreases |iters| - i
  {
    if i == |iters| then (
      cur
    ) else (
      var it := iters[i];
      if it.next.Some? then (
        if cur.Some? then (
          var minK := if lt(cur.value, it.next.value.key) then Some(cur.value) else Some(it.next.value.key);
          getMinKeyIter(iters, i+1, minK)
        ) else (
          getMinKeyIter(iters, i+1, Some(it.next.value.key))
        )
      ) else (
        getMinKeyIter(iters, i+1, cur)
      )
    )
  }

  function {:opaque} getMinKey(iters: seq<Iterator>) : Option<Key>
  {
    getMinKeyIter(iters, 0, None)
  }

  ////////////////
  //// evalKeyIter

  function evalKeyIter(buckets: seq<Bucket>, iters: seq<Iterator>, key: Key, m: Message, i: int) : Message
  requires |buckets| == |iters|
  requires forall j | 0 <= j < |iters| :: WFIter(buckets[j], iters[j])
  requires 0 <= i <= |buckets|
  decreases |buckets| - i
  {
    if i == |iters| then (
      m
    ) else (
      var m' :=
        if iters[i].next.Some? && iters[i].next.value.key == key then (
          Messages.Merge(m, iters[i].next.value.msg)
        ) else (
          m
        );
      evalKeyIter(buckets, iters, key, m', i+1)
    )
  }

  function {:opaque} evalKey(buckets: seq<Bucket>, iters: seq<Iterator>, key: Key) : Message
  requires |buckets| == |iters|
  requires forall j | 0 <= j < |iters| :: WFIter(buckets[j], iters[j])
  {
    evalKeyIter(buckets, iters, key, Messages.Update(Messages.NopDelta()), 0)
  }

  ////////////////
  //// advance

  function advanceIter(buckets: seq<Bucket>, iters: seq<Iterator>, key: Key, upTo: Option<Key>, i: int, res: seq<Iterator>) : (iters' : seq<Iterator>)
  requires |buckets| == |iters|
  requires forall j | 0 <= j < |iters| :: WFIter(buckets[j], iters[j])
  requires 0 <= i <= |buckets|
  requires |res| == i
  requires forall j | 0 <= j < |res| :: WFIter(buckets[j], res[j])
  ensures |iters'| == |iters|
  ensures forall j | 0 <= j < |iters'| :: WFIter(buckets[j], iters'[j])
  decreases |buckets| - i
  {
    if i == |iters| then (
      res
    ) else (
      var newIter := 
        if iters[i].next.Some? && iters[i].next.value.key == key then (
          var next := IterInc(buckets[i], iters[i]);
          if next.next.Some? && (upTo.Some? ==> lt(next.next.value.key, upTo.value)) then (
            next
          ) else (
            IterEnd(buckets[i])
          )
        ) else (
          iters[i]
        );
      advanceIter(buckets, iters, key, upTo, i+1, res + [newIter])
    )
  }

  function {:opaque} advance(buckets: seq<Bucket>, iters: seq<Iterator>, key: Key, upTo: Option<Key>) : (iters' : seq<Iterator>)
  requires |buckets| == |iters|
  requires forall j | 0 <= j < |iters| :: WFIter(buckets[j], iters[j])
  ensures |iters'| == |iters|
  ensures forall j | 0 <= j < |iters'| :: WFIter(buckets[j], iters'[j])
  {
    advanceIter(buckets, iters, key, upTo, 0, [])
  }

  ////////////////
  //// initQueue

  function {:opaque} initIterator(bucket: Bucket, start: UI.RangeStart, upTo: Option<Key>) : (it : Iterator)
  ensures WFIter(bucket, it)
  {
    var it := match start {
      case SInclusive(key) => IterFindFirstGe(bucket, key)
      case SExclusive(key) => IterFindFirstGt(bucket, key)
      case NegativeInf => IterStart(bucket)
    };
    if it.next.Some? && (upTo.Some? ==> lt(it.next.value.key, upTo.value)) then
      it
    else
      IterEnd(bucket)
  }

  function initQueueIter(buckets: seq<Bucket>, start: UI.RangeStart, upTo: Option<Key>, i: int, acc: seq<Iterator>) : (its : seq<Iterator>)
  requires |acc| == i
  requires 0 <= i <= |buckets|
  requires forall i | 0 <= i < |acc| :: WFIter(buckets[i], acc[i])
  ensures |its| == |buckets|
  ensures forall i | 0 <= i < |its| :: WFIter(buckets[i], its[i])
  decreases |buckets| - i
  {
    if i == |buckets| then (
      acc
    ) else (
      var bucket := buckets[i];
      var it := initIterator(buckets[i], start, upTo);
      initQueueIter(buckets, start, upTo, i+1, acc + [it])
    )
  }

  function {:opaque} initQueue(buckets: seq<Bucket>, start: UI.RangeStart, upTo: Option<Key>) : (its : seq<Iterator>)
  ensures |its| == |buckets|
  ensures forall i | 0 <= i < |its| :: WFIter(buckets[i], its[i])
  {
    initQueueIter(buckets, start, upTo, 0, [])
  }

  ////////////////
  //// collectSuccessors

  datatype SuccCollectionResult =
      SuccCollectionResult(results: seq<UI.SuccResult>, end: UI.RangeEnd)

  function collectSuccessorsIter(buckets: seq<Bucket>, iters: seq<Iterator>, upTo: Option<Key>, maxToFind: int, acc: seq<UI.SuccResult>) : SuccCollectionResult
  requires |buckets| == |iters|
  requires forall j | 0 <= j < |iters| :: WFIter(buckets[j], iters[j])
  requires |acc| <= maxToFind
  requires maxToFind >= 1

  decreases decreaserSum(iters)
  {
    if |acc| == maxToFind then (
      SuccCollectionResult(acc, UI.EInclusive(Last(acc).key))
    ) else (
      var keyOpt := getMinKey(iters);
      if keyOpt.Some? then (
        var key := keyOpt.value;
        var m := evalKey(buckets, iters, key);
        var def := Messages.Merge(m, Messages.DefineDefault()).value;
        var acc' :=
          if def == Messages.DefaultValue() then (
            acc
          ) else (
            acc + [UI.SuccResult(key, def)]
          );

        lemmaAdvanceDecreases(buckets, iters, upTo);
        var iters' := advance(buckets, iters, key, upTo);

        collectSuccessorsIter(buckets, iters', upTo, maxToFind, acc')
      ) else (
        var end := if upTo.Some? then UI.EExclusive(upTo.value) else UI.PositiveInf;
        SuccCollectionResult(acc, end)
      )
    )
  }

  function collectSuccessors(buckets: seq<Bucket>, start: UI.RangeStart, upTo: Option<Key>, maxToFind: int) : SuccCollectionResult
  requires maxToFind >= 1
  {
    var iters := initQueue(buckets, start, upTo);
    collectSuccessorsIter(buckets, iters, upTo, maxToFind, [])
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
          var res := collectSuccessors(buckets, start, upTo, maxToFind);
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

  ////////////////
  //// some lemmas for termination

  lemma getMinKeyExistsIter(iters: seq<Iterator>, i: int, cur: Option<Key>, j0: int) returns (j : int)
  requires 0 <= i <= |iters|
  requires
      cur.Some? ==> 0 <= j0 < |iters| && iters[j0].next.Some? && iters[j0].next.value.key == cur.value
  ensures var key := getMinKeyIter(iters, i, cur);
      key.Some? ==> 0 <= j < |iters| && iters[j].next.Some? && iters[j].next.value.key == key.value
  decreases |iters| - i
  {
    if i == |iters| {
      j := j0;
    } else {
      var it := iters[i];
      if it.next.Some? {
        if cur.Some? {
          var minK := if lt(cur.value, it.next.value.key) then Some(cur.value) else Some(it.next.value.key);
          j := getMinKeyExistsIter(iters, i+1, minK, if lt(cur.value, it.next.value.key) then j0 else i);
        } else {
          j := getMinKeyExistsIter(iters, i+1, Some(it.next.value.key), i);
        }
      } else {
        j := getMinKeyExistsIter(iters, i+1, cur, j0);
      }
    }
  }

  lemma getMinKeyExists(iters: seq<Iterator>) returns (j : int)
  ensures var key := getMinKey(iters);
      key.Some? ==> 0 <= j < |iters| && iters[j].next.Some? && iters[j].next.value.key == key.value
  {
    reveal_getMinKey();
    j := getMinKeyExistsIter(iters, 0, None, 0);
  }

  lemma lemmaAdvanceDecreasesIter(buckets: seq<Bucket>, iters: seq<Iterator>, key: Key, upTo: Option<Key>, i: int, res: seq<Iterator>, j: int)
  requires advanceIter.requires(buckets, iters, key, upTo, i, res)
  requires 0 <= j < |iters| && iters[j].next.Some? && iters[j].next.value.key == key

  requires j < i ==> decreaserSum(res) < decreaserSum(iters[..i])
  requires decreaserSum(res) <= decreaserSum(iters[..i])

  ensures decreaserSum(advanceIter(buckets, iters, key, upTo, i, res))
      < decreaserSum(iters)
  decreases |buckets| - i
  {
    if i == |iters| {
      assert iters[..i] == iters;
    } else {
      //assert WFIter(buckets[i], iters[i]);

      //assert IterEnd(buckets[i]).decreaser == 0
      //    <= iters[i].decreaser;

      var newIter := 
        if iters[i].next.Some? && iters[i].next.value.key == key then (
          var next := IterInc(buckets[i], iters[i]);
          if next.next.Some? && (upTo.Some? ==> lt(next.next.value.key, upTo.value)) then (
            next
          ) else (
            IterEnd(buckets[i])
          )
        ) else (
          iters[i]
        );
      //assert newIter.decreaser <= iters[i].decreaser;
      //assert j == i ==> newIter.decreaser < iters[i].decreaser;
      assert DropLast(iters[..i+1]) == iters[..i];
      assert Last(iters[..i+1]) == iters[i];
      assert DropLast(res + [newIter]) == res;
      assert Last(res + [newIter]) == newIter;
      lemmaAdvanceDecreasesIter(buckets, iters, key, upTo, i+1, res + [newIter], j);
    }
  }

  lemma lemmaAdvanceDecreases(buckets: seq<Bucket>, iters: seq<Iterator>, upTo: Option<Key>)
  requires |buckets| == |iters|
  requires forall j | 0 <= j < |iters| :: WFIter(buckets[j], iters[j])
  requires getMinKey(iters).Some?
  ensures decreaserSum(advance(buckets, iters, getMinKey(iters).value, upTo))
      < decreaserSum(iters)
  {
    reveal_advance();
    var j := getMinKeyExists(iters);
    lemmaAdvanceDecreasesIter(buckets, iters, getMinKey(iters).value, upTo, 0, [], j);
  }

  ////////////////
  //// some more lemmas

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

  lemma getMinKeyLteAllIter(iters: seq<Iterator>, i: int, cur: Option<Key>, j: int)
  requires 0 <= i <= |iters|
  requires 0 <= j < |iters|
  requires j < i ==> cur.Some? && iters[j].next.Some? ==> lte(cur.value, iters[j].next.value.key)
  requires j < i ==> iters[j].next.Some? ==> cur.Some?
  ensures var key := getMinKeyIter(iters, i, cur);
      && (key.Some? && iters[j].next.Some? ==> lte(key.value, iters[j].next.value.key))
      && (iters[j].next.Some? ==> key.Some?)
  decreases |iters| - i
  {
    if i == |iters| {
    } else {
      var it := iters[i];
      if it.next.Some? {
        if cur.Some? {
          var minK := if lt(cur.value, it.next.value.key) then Some(cur.value) else Some(it.next.value.key);
          //assert lte(minK.value, cur.value);
          //assert lte(minK.value, it.next.value.key);
          if j == i {
            assert j < i+1 ==> iters[j].next.Some? ==> lte(minK.value, iters[j].next.value.key);
          } else {
            assert j < i+1 ==> iters[j].next.Some? ==> lte(minK.value, iters[j].next.value.key);
          }
          getMinKeyLteAllIter(iters, i+1, minK, j);
        } else {
          getMinKeyLteAllIter(iters, i+1, Some(it.next.value.key), j);
        }
      } else {
        getMinKeyLteAllIter(iters, i+1, cur, j);
      }
    }
  }

  lemma getMinKeyLteAll(iters: seq<Iterator>, j: int)
  requires 0 <= j < |iters|
  ensures var key := getMinKey(iters);
      && (key.Some? && iters[j].next.Some? ==> lte(key.value, iters[j].next.value.key))
      && (iters[j].next.Some? ==> key.Some?)
  {
    reveal_getMinKey();
    getMinKeyLteAllIter(iters, 0, None, j);
  }

  predicate KeyAccountedFor(
      buckets: seq<Bucket>, its: seq<Iterator>, succs: seq<UI.SuccResult>, key: Key)
  requires |buckets| == |its|
  {
    || PBS.BufferDefinesEmptyValue(PBS.InterpretBucketStack(buckets, key))
    || (exists j | 0 <= j < |succs| :: succs[j].key == key)
    || (forall j | 0 <= j < |buckets| :: key in buckets[j] ==>
          its[j].next.Some? ==> lte(its[j].next.value.key, key))
  }

  predicate ItsConsistent(buckets: seq<Bucket>, its: seq<Iterator>, i: int, j: int, key: Key)
  requires |buckets| == |its|
  requires 0 <= i < |its|
  requires 0 <= j < |its|
  {
    key in buckets[i] && key in buckets[j] ==>
      ((its[i].next.Some? && lte(its[i].next.value.key, key)) ==>
       (its[j].next.Some? && lte(its[j].next.value.key, key)))
  }

  predicate {:opaque} SuccKeysOrdered(succs: seq<UI.SuccResult>)
  {
    forall i, j | 0 <= i < j < |succs| :: lt(succs[i].key, succs[j].key)
  }

  predicate {:opaque} SuccsBeforeIts(its: seq<Iterator>, succs: seq<UI.SuccResult>)
  {
    forall i, j | 0 <= i < |succs| && 0 <= j < |its| && its[j].next.Some? :: lt(succs[i].key, its[j].next.value.key)
  }

  predicate IterProps(buckets: seq<Bucket>, its: seq<Iterator>, succs: seq<UI.SuccResult>, start: UI.RangeStart, end: UI.RangeEnd)
  {
    && |buckets| == |its|
    && (forall j | 0 <= j < |its| :: WFIter(buckets[j], its[j]))
    && (forall key | MS.InRange(start, key, end) :: KeyAccountedFor(buckets, its, succs, key))
    && (forall i | 0 <= i < |succs| :: PBS.BufferDefinesValue(PBS.InterpretBucketStack(buckets, succs[i].key), succs[i].value))
    && (forall i | 0 <= i < |succs| :: succs[i].value != MS.EmptyValue())
    && (forall i | 0 <= i < |succs| :: MS.InRange(start, succs[i].key, end))
    && SuccKeysOrdered(succs)
    && SuccsBeforeIts(its, succs)
    && (forall j | 0 <= j < |its| && its[j].next.Some? :: MS.InRange(start, its[j].next.value.key, end))
    && (forall key, i, j | 0 <= i < |its| && 0 <= j < |its| && MS.InRange(start, key, end) :: ItsConsistent(buckets, its, i, j, key))
  }

  lemma evalKeyIsInterpIter(buckets: seq<Bucket>, iters: seq<Iterator>, succs: seq<UI.SuccResult>, start: UI.RangeStart, end: UI.RangeEnd, m: Message, i: int)
  requires 0 <= i <= |iters|
  requires IterProps(buckets, iters, succs, start, end)
  requires getMinKey(iters).Some?
  requires m == PBS.InterpretBucketStack(buckets[..i], getMinKey(iters).value)
  decreases |buckets| - i
  ensures evalKeyIter(buckets, iters, getMinKey(iters).value, m, i)
     == PBS.InterpretBucketStack(buckets, getMinKey(iters).value)
  {
    if i == |iters| {
      assert buckets[..i] == buckets;
    } else {
      var key := getMinKey(iters).value;
      if (key in buckets[i]) {
        var j := getMinKeyExists(iters);
        assert ItsConsistent(buckets, iters, j, i, key);
        assert lte(iters[i].next.value.key, key);

        getMinKeyLteAll(iters, i);
        assert lte(key, iters[i].next.value.key);

        assert iters[i].next.Some?;
        assert iters[i].next.value.key == key;
        assert buckets[i][key] == iters[i].next.value.msg;
      } else {
        assert !(iters[i].next.Some? && iters[i].next.value.key == key);
      }
      
      var m' :=
        if iters[i].next.Some? && iters[i].next.value.key == key then (
          Messages.Merge(m, iters[i].next.value.msg)
        ) else (
          m
        );
      assert DropLast(buckets[..i+1]) == buckets[..i];
      assert Last(buckets[..i+1]) == buckets[i];
      evalKeyIsInterpIter(buckets, iters, succs, start, end, m', i+1);
    }
  }

  lemma evalKeyIsInterp(buckets: seq<Bucket>, iters: seq<Iterator>, succs: seq<UI.SuccResult>, start: UI.RangeStart, end: UI.RangeEnd)
  requires IterProps(buckets, iters, succs, start, end)
  ensures getMinKey(iters).Some? ==>
        evalKey(buckets, iters, getMinKey(iters).value)
     == PBS.InterpretBucketStack(buckets, getMinKey(iters).value)
  {
    reveal_evalKey();
    if getMinKey(iters).Some? {
      evalKeyIsInterpIter(buckets, iters, succs, start, end, Messages.Update(Messages.NopDelta()), 0);
    }
  }

  predicate AdvanceRelation(bucket: Bucket, iter: Iterator, iter': Iterator, key: Key, upTo: Option<Key>)
  {
    && (iter.next.None? ==> iter' == iter)
    && (iter.next.Some? && iter.next.value.key != key ==> iter' == iter)
    && (iter.next.Some? && iter.next.value.key == key ==>
      var next := IterInc(bucket, iter);
      && (next.next.None? ==> iter' == IterEnd(bucket))
      && (next.next.Some? && upTo.None? ==> iter' == next)
      && (next.next.Some? && upTo.Some? && lt(next.next.value.key, upTo.value) ==> iter' == next)
      && (next.next.Some? && upTo.Some? && lte(upTo.value, next.next.value.key) ==> iter' == IterEnd(bucket))
    )
  }

  lemma advanceResultIter(buckets: seq<Bucket>, iters: seq<Iterator>, key: Key, upTo: Option<Key>, i: int, res: seq<Iterator>)
  requires |buckets| == |iters|
  requires forall j | 0 <= j < |iters| :: WFIter(buckets[j], iters[j])
  requires 0 <= i <= |buckets|
  requires |res| == i
  requires forall j | 0 <= j < |res| :: WFIter(buckets[j], res[j])
  requires forall i | 0 <= i < |res| :: AdvanceRelation(buckets[i], iters[i], res[i], key, upTo)
  decreases |buckets| - i
  ensures var iters' := advanceIter(buckets, iters, key, upTo, i, res);
    forall i | 0 <= i < |iters| :: AdvanceRelation(buckets[i], iters[i], iters'[i], key, upTo)
  {
    if i == |iters| {
    } else {
      var newIter := 
        if iters[i].next.Some? && iters[i].next.value.key == key then (
          var next := IterInc(buckets[i], iters[i]);
          if next.next.Some? && (upTo.Some? ==> lt(next.next.value.key, upTo.value)) then (
            next
          ) else (
            IterEnd(buckets[i])
          )
        ) else (
          iters[i]
        );
      assert AdvanceRelation(buckets[i], iters[i], newIter, key, upTo);
      advanceResultIter(buckets, iters, key, upTo, i+1, res + [newIter]);
    }
  }

  lemma advanceResult(buckets: seq<Bucket>, iters: seq<Iterator>, key: Key, upTo: Option<Key>)
  requires |buckets| == |iters|
  requires forall j | 0 <= j < |iters| :: WFIter(buckets[j], iters[j])
  ensures var iters' := advance(buckets, iters, key, upTo);
    forall i | 0 <= i < |iters| :: AdvanceRelation(buckets[i], iters[i], iters'[i], key, upTo)
  {
    reveal_advance();
    advanceResultIter(buckets, iters, key, upTo, 0, []);
  }

  lemma advancePreservesSuccInvariants(buckets: seq<Bucket>, its: seq<Iterator>, succs: seq<UI.SuccResult>, succs': seq<UI.SuccResult>, start: UI.RangeStart, end: UI.RangeEnd, upTo: Option<Key>)
  requires |buckets| == |its|
  requires forall j | 0 <= j < |its| :: WFIter(buckets[j], its[j])
  requires SuccKeysOrdered(succs)
  requires SuccsBeforeIts(its, succs)

  requires getMinKey(its).Some?
  requires 
    && (succs' != succs ==>
      && |succs'| == |succs| + 1
      && (forall j | 0 <= j < |succs| :: succs'[j] == succs[j])
      && succs'[|succs'| - 1].key == getMinKey(its).value
    )

  ensures SuccKeysOrdered(succs')
  ensures SuccsBeforeIts(advance(buckets, its, getMinKey(its).value, upTo), succs')
  {
    reveal_SuccKeysOrdered();
    reveal_SuccsBeforeIts();
    var key := getMinKey(its).value;
    var its' := advance(buckets, its, getMinKey(its).value, upTo);

    if (succs' != succs) {
      forall i, j | 0 <= i < j < |succs'|
      ensures lt(succs'[i].key, succs'[j].key)
      {
        if j == |succs'| - 1 {
          var p := getMinKeyExists(its);
          assert lt(succs[i].key, its[p].next.value.key);
        }
      }
    }

    forall i, j | 0 <= i < |succs'| && 0 <= j < |its'| && its'[j].next.Some?
    ensures lt(succs'[i].key, its'[j].next.value.key)
    {
      advanceResult(buckets, its, key, upTo);
      assert AdvanceRelation(buckets[j], its[j], its'[j], key, upTo);
      IterIncKeyGreater(buckets[j], its[j]);

      if i < |succs| {
        assert lt(succs[i].key, its[j].next.value.key);
        assert lt(succs'[i].key, its'[j].next.value.key);
      } else {
        getMinKeyLteAll(its, j);
        assert lt(succs'[i].key, its'[j].next.value.key);
      }
    }
  }

  lemma advancePreservesInvariants(buckets: seq<Bucket>, its: seq<Iterator>, succs: seq<UI.SuccResult>, succs': seq<UI.SuccResult>, start: UI.RangeStart, end: UI.RangeEnd, upTo: Option<Key>)
  requires IterProps(buckets, its, succs, start, end)

  requires getMinKey(its).Some?
  requires 
    var key := getMinKey(its).value;
    var m := evalKey(buckets, its, key);
    var def := Messages.Merge(m, Messages.DefineDefault()).value;
    && (def == Messages.DefaultValue() ==> succs' == succs)
    && (def != Messages.DefaultValue() ==>
      && |succs'| == |succs| + 1
      && (forall j | 0 <= j < |succs| :: succs'[j] == succs[j])
      && succs'[|succs'| - 1] == UI.SuccResult(key, def)
    )

  requires upTo.Some? ==> end == UI.EExclusive(upTo.value)
  requires upTo.None? ==> end == UI.PositiveInf

  ensures IterProps(buckets,
      advance(buckets, its, getMinKey(its).value, upTo),
      succs', start, end)
  {
    var key := getMinKey(its).value;
    var m := evalKey(buckets, its, key);
    var def := Messages.Merge(m, Messages.DefineDefault()).value;

    evalKeyIsInterp(buckets, its, succs, start, end);

    var its' := advance(buckets, its, getMinKey(its).value, upTo);

    forall k | MS.InRange(start, k, end)
    ensures KeyAccountedFor(buckets, its', succs', k)
    {
      assert KeyAccountedFor(buckets, its, succs, k);
      if PBS.BufferDefinesEmptyValue(PBS.InterpretBucketStack(buckets, k)) {
        assert KeyAccountedFor(buckets, its', succs', k);
      } else if (exists j | 0 <= j < |succs| :: succs[j].key == k) {
        assert KeyAccountedFor(buckets, its', succs', k);
      } else {
        assert forall j | 0 <= j < |buckets| :: k in buckets[j] ==>
            its[j].next.Some? ==> lte(its[j].next.value.key, k);
        if k == key {
          if def == Messages.DefaultValue() {
            assert PBS.BufferDefinesEmptyValue(PBS.InterpretBucketStack(buckets, k));
            assert KeyAccountedFor(buckets, its', succs', k);
          } else {
            assert succs'[|succs'| - 1].key == k;
            assert KeyAccountedFor(buckets, its', succs', k);
          }
        } else {
          forall j | 0 <= j < |buckets| && k in buckets[j] && its'[j].next.Some?
          ensures lte(its'[j].next.value.key, k);
          {
            advanceResult(buckets, its, key, upTo);
            assert AdvanceRelation(buckets[j], its[j], its'[j], key, upTo);
            noKeyBetweenIterAndIterInc(buckets[j], its[j], k);
            assert its[j].next.Some?;
            assert lte(its[j].next.value.key, k);
          }
          assert KeyAccountedFor(buckets, its', succs', k);
        }
      }
    }

    forall i | 0 <= i < |succs'|
    ensures PBS.BufferDefinesValue(PBS.InterpretBucketStack(buckets, succs'[i].key), succs'[i].value)
    {
      if i < |succs| {
        assert PBS.BufferDefinesValue(PBS.InterpretBucketStack(buckets, succs[i].key), succs[i].value);
      }
    }

    forall i | 0 <= i < |succs'|
    ensures MS.InRange(start, succs'[i].key, end)
    {
      if i < |succs| {
        assert MS.InRange(start, succs[i].key, end);
      } else {
        var j := getMinKeyExists(its);
        assert MS.InRange(start, its[j].next.value.key, end);
      }
    }

    forall j | 0 <= j < |its'| && its'[j].next.Some?
    ensures MS.InRange(start, its'[j].next.value.key, end)
    {
      advanceResult(buckets, its, key, upTo);
      assert AdvanceRelation(buckets[j], its[j], its'[j], key, upTo);
      IterIncKeyGreater(buckets[j], its[j]);

      assert MS.InRange(start, its[j].next.value.key, end);
      assert start.SInclusive? || start.SExclusive? ==>
          lte(start.key, its[j].next.value.key);
    }

    forall k, i, j | 0 <= i < |its'| && 0 <= j < |its'| && MS.InRange(start, k, end)
    ensures ItsConsistent(buckets, its', i, j, k)
    {
      assert ItsConsistent(buckets, its, i, j, k);

      advanceResult(buckets, its, key, upTo);

      if k in buckets[i] && k in buckets[j] &&
            (its'[i].next.Some? && lte(its'[i].next.value.key, k)) {
        assert AdvanceRelation(buckets[j], its[j], its'[j], key, upTo);
        assert AdvanceRelation(buckets[i], its[i], its'[i], key, upTo);

        IterIncKeyGreater(buckets[i], its[i]);

        //assert its[j].next.Some?;
        //assert lte(its[j].next.value.key, k);

        noKeyBetweenIterAndIterInc(buckets[j], its[j], k);

        getMinKeyLteAll(its, i);
        assert k != key;

        /*if its'[j] == its[j] {
          assert its'[j].next.Some?;
          assert lte(its'[j].next.value.key, k);
        } else if its'[j] == IterEnd(buckets[j]) {
          assert false;
        } else if its'[j] == IterInc(buckets[j], its[j]) {
          assert its'[j].next.Some?;
          assert lte(its'[j].next.value.key, k);
        }*/
      }
    }

    advancePreservesSuccInvariants(buckets, its, succs, succs', start, end, upTo);
  }

  lemma initQueueResultIter(buckets: seq<Bucket>, start: UI.RangeStart, upTo: Option<Key>, i: int, acc: seq<Iterator>)
  requires |acc| == i
  requires 0 <= i <= |buckets|
  requires forall i | 0 <= i < |acc| :: WFIter(buckets[i], acc[i])
  requires forall i | 0 <= i < |acc| :: acc[i] == initIterator(buckets[i], start, upTo)
  decreases |buckets| - i
  ensures var its := initQueueIter(buckets, start, upTo, i, acc);
      forall i | 0 <= i < |buckets| :: its[i] == initIterator(buckets[i], start, upTo)
  {
    if i == |buckets| {
    } else {
      var bucket := buckets[i];
      var it := initIterator(buckets[i], start, upTo);
      initQueueResultIter(buckets, start, upTo, i+1, acc + [it]);
    }
  }

  lemma initQueueResult(buckets: seq<Bucket>, start: UI.RangeStart, upTo: Option<Key>)
  ensures var its := initQueue(buckets, start, upTo);
      forall i | 0 <= i < |buckets| :: its[i] == initIterator(buckets[i], start, upTo)
  {
    reveal_initQueue();
    initQueueResultIter(buckets, start, upTo, 0, []);
  }

  lemma initQueueInvariant(buckets: seq<Bucket>, start: UI.RangeStart, end: UI.RangeEnd, upTo: Option<Key>)
  requires upTo.Some? ==> end == UI.EExclusive(upTo.value)
  requires upTo.None? ==> end == UI.PositiveInf
  ensures IterProps(buckets, initQueue(buckets, start, upTo), [], start, end)
  {
    reveal_SuccKeysOrdered();
    reveal_SuccsBeforeIts();
    reveal_initIterator();

    var its := initQueue(buckets, start, upTo);
    initQueueResult(buckets, start, upTo);

    forall key | MS.InRange(start, key, end)
    ensures KeyAccountedFor(buckets, its, [], key)
    {
    }

    forall j | 0 <= j < |its| && its[j].next.Some?
    ensures MS.InRange(start, its[j].next.value.key, end)
    {
    }

    forall key, i, j | 0 <= i < |its| && 0 <= j < |its| && MS.InRange(start, key, end)
    ensures ItsConsistent(buckets, its, i, j, key)
    {
      //assert its[j] == initIterator(buckets[j], start, upTo);

      /*var it := match start {
        case SInclusive(k) => IterFindFirstGe(buckets[i], k)
        case SExclusive(k) => IterFindFirstGt(buckets[i], k)
        case NegativeInf => IterStart(buckets[i])
      };*/

      //assert upTo.Some? ==> lt(key, upTo.value);
      if key in buckets[i] && key in buckets[j] &&
          (its[i].next.Some? && lte(its[i].next.value.key, key)) {
        if start.SInclusive? {
          //assert lte(start.key, key);
          noKeyBetweenIterFindFirstGe(buckets[j], start.key, key);
          //assert it.next.Some?;
          //assert lte(it.next.value.key, key);
        }
        else if start.SExclusive? {
          //assert lt(start.key, key);
          noKeyBetweenIterFindFirstGt(buckets[j], start.key, key);
          //assert ItsConsistent(buckets, its, i, j, key);
          //assert it.next.Some?;
          //assert lte(it.next.value.key, key);
        }
        else {
          noKeyBeforeIterStart(buckets[j], key);
          //assert ItsConsistent(buckets, its, i, j, key);
          //assert it.next.Some?;
          //assert lte(it.next.value.key, key);
        }
      }
    }
  }
}
