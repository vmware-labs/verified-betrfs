include "../lib/Marshalling/GenericMarshalling.i.dfy"
include "BlockCacheSystemCrashSafeBlockInterfaceRefinement.dfy"
include "PivotBetreeSpec.dfy"
include "Message.dfy"
include "../tla-tree/MissingLibrary.dfy"

module Marshalling {
  import opened GenericMarshalling
  import opened MissingLibrary
  import opened NativeTypes
  import opened Sequences
  import BC = BetreeGraphBlockCache
  import BT = PivotBetreeSpec`Internal
  import M = ValueMessage
  import ReferenceType`Internal
  import LBAType`Internal
  import ValueWithDefault`Internal
  import Pivots = PivotsLib
  import MS = MapSpec
  import Keyspace = MS.Keyspace

  type Reference = BC.Reference
  type LBA = BC.LBA
  type Sector = BC.Sector
  type Message = M.Message
  type Bucket = BT.G.Bucket
  type Key = BT.G.Key
  type Node = BT.G.Node

  /////// Grammar

  function method SuperblockGrammar() : G
  ensures ValidGrammar(SuperblockGrammar())
  {
    // (Reference, LBA, refcount) triples
    GArray(GTuple([GUint64, GUint64, GUint64]))
  }

  function method MessageGrammar() : G
  ensures ValidGrammar(MessageGrammar())
  {
    // Always a Define message.
    GByteArray
  }

  function method BucketGrammar() : G
  ensures ValidGrammar(BucketGrammar())
  {
    GArray(GTuple([GByteArray, MessageGrammar()]))
  }

  function method PivotNodeGrammar() : G
  ensures ValidGrammar(PivotNodeGrammar())
  {
    GTuple([
        GArray(GByteArray), // pivots
        GArray(GUint64), // children
        GArray(BucketGrammar()) 
    ])
  }

  function method SectorGrammar() : G
  ensures ValidGrammar(SectorGrammar())
  {
    GTaggedUnion([SuperblockGrammar(), PivotNodeGrammar()])    
  }

  /////// Conversion to PivotNode

  function method valToReference(v: V) : Reference
  requires ValInGrammar(v, GUint64)
  {
    v.u
  }

  function method valToLBA(v: V) : LBA
  requires ValInGrammar(v, GUint64)
  {
    v.u
  }

  function method valToInt(v: V) : int
  requires ValInGrammar(v, GUint64)
  {
    v.u as int
  }

  function method valToLBAsAndRefcounts(a: seq<V>) : Option<(map<Reference, LBA>, map<Reference, int>)>
  requires forall i | 0 <= i < |a| :: ValInGrammar(a[i], GTuple([GUint64, GUint64, GUint64]))
  ensures var s := valToLBAsAndRefcounts(a) ; s.Some? ==> 0 !in s.value.0.Values
  ensures var s := valToLBAsAndRefcounts(a) ; s.Some? ==> s.value.0.Keys == s.value.1.Keys
  {
    if |a| == 0 then
      Some((map[], map[]))
    else (
      var res := valToLBAsAndRefcounts(DropLast(a));
      match res {
        case Some((lbas, refcounts)) => (
          var tuple := Last(a);
          var ref := valToReference(tuple.t[0]);
          var lba := valToLBA(tuple.t[1]);
          var refcount := valToInt(tuple.t[2]);
          if ref in refcounts || lba == 0 then (
            None
          ) else (
            Some((lbas[ref := lba], refcounts[ref := refcount]))
          )
        )
        case None => None
      }
    )
  }

  function method valToSuperblock(v: V) : Option<BC.Superblock>
  requires ValInGrammar(v, SuperblockGrammar())
  ensures var s := valToSuperblock(v) ; s.Some? ==> BC.WFSuperblock(BC.Constants(), s.value)
  {
    var res := valToLBAsAndRefcounts(v.a);
    match res {
      case Some(res) => Some(BC.Superblock(res.0, res.1))
      case None => None
    }
  }

  function method valToMessage(v: V) : Option<Message>
  requires ValInGrammar(v, MessageGrammar())
  {
    Some(M.Define(v.b))
  }

  function method valToKeyMessageMap(a: seq<V>, pivotTable: seq<Key>, i: int) : Option<Bucket>
  requires forall i | 0 <= i < |a| :: ValInGrammar(a[i], GTuple([GByteArray, MessageGrammar()]))
  requires Pivots.WFPivots(pivotTable)
  ensures var s := valToKeyMessageMap(a, pivotTable, i) ; s.Some? ==> forall key | key in s.value :: Pivots.Route(pivotTable, key) == i
  {
    if |a| == 0 then
      Some(map[])
    else (
      var res := valToKeyMessageMap(DropLast(a), pivotTable, i);
      match res {
        case Some(m) => (
          var tuple := Last(a);
          assert ValInGrammar(tuple, GTuple([GByteArray, MessageGrammar()]));
          var key := tuple.t[0].b;
          var msg := valToMessage(tuple.t[1]);
          if key in m || Pivots.Route(pivotTable, key) != i then (
            None
          ) else (
            Some(m[key := msg.value])
          )
        )
        case None => None
      }
    )
  }

  function method valToBucket(v: V, pivotTable: seq<Key>, i: int) : Option<Bucket>
  requires ValInGrammar(v, BucketGrammar())
  requires Pivots.WFPivots(pivotTable)
  {
    valToKeyMessageMap(v.a, pivotTable, i)
  }

  function method valToKey(v: V) : Key
  requires ValInGrammar(v, GByteArray)
  {
    v.b
  }

  function method valToPivots(a: seq<V>) : Option<seq<Key>>
  requires forall i | 0 <= i < |a| :: ValInGrammar(a[i], GByteArray)
  ensures var s := valToPivots(a) ; s.Some? ==> Pivots.WFPivots(s.value)
  {
    if |a| == 0 then
      Some([])
    else
      match valToPivots(DropLast(a)) {
        case None => None
        case Some(pref) => (
          var key := valToKey(Last(a));

          if (|key| != 0 && (|pref| > 0 ==> Keyspace.lt(Last(pref), key))) then (
            Keyspace.reveal_seq_lte();
            Keyspace.IsNotMinimum([], key);
            Keyspace.StrictlySortedAugment(pref, key);

            Some(pref + [key])
          ) else (
            None
          )
        )
      }
  }

  function method valToChildren(a: seq<V>) : Option<seq<Reference>>
  requires forall i | 0 <= i < |a| :: ValInGrammar(a[i], GUint64)
  {
    if |a| == 0 then
      Some([])
    else
      match valToChildren(DropLast(a)) {
        case None => None
        case Some(pref) => Some(pref + [valToReference(Last(a))])
      }
  }

  function method valToBuckets(a: seq<V>, pivotTable: seq<Key>) : Option<seq<Bucket>>
  requires Pivots.WFPivots(pivotTable)
  requires forall i | 0 <= i < |a| :: ValInGrammar(a[i], BucketGrammar())
  ensures var s := valToBuckets(a, pivotTable) ; s.Some? ==> |s.value| == |a|
  ensures var s := valToBuckets(a, pivotTable) ; s.Some? ==> forall i | 0 <= i < |s.value| :: forall key | key in s.value[i] :: Pivots.Route(pivotTable, key) == i
  {
    if |a| == 0 then
      Some([])
    else (
      match valToBuckets(DropLast(a), pivotTable) {
        case None => None
        case Some(pref) => (
          match valToBucket(Last(a), pivotTable, |pref|) {
            case Some(bucket) => Some(pref + [bucket])
            case None => None
          }
        )
      }
    )
  }

  function method {:fuel ValInGrammar,2} valToPivotNode(v: V) : Option<Node>
  requires ValInGrammar(v, PivotNodeGrammar())
  ensures var s := valToPivotNode(v); s.Some? ==> BT.WFNode(s.value)
  {
    match valToPivots(v.t[0].a) {
      case None => None
      case Some(pivots) => (
        match valToChildren(v.t[1].a) {
          case None => None
          case Some(children) => (
            if ((|children| == 0 || |children| == |pivots| + 1) && |v.t[2].a| == |pivots| + 1) then (
              match valToBuckets(v.t[2].a, pivots) {
                case None => None
                case Some(buckets) => (
                  Some(BT.G.Node(pivots, if |children| == 0 then None else Some(children), buckets))
                )
              }
            ) else (
              None
            )
          )
        }
      )
    }
  }

  function method valToSector(v: V) : Option<Sector>
  requires ValInGrammar(v, SectorGrammar())
  ensures var s := valToSector(v);
      s.Some? && s.value.SectorSuperblock? ==> BC.WFSuperblock(BC.Constants(), s.value.superblock)
  ensures var s := valToSector(v);
      s.Some? && s.value.SectorBlock? ==> BT.WFNode(s.value.block)
  {
    if v.c == 0 then (
      match valToSuperblock(v.val) {
        case Some(s) => Some(BC.SectorSuperblock(s))
        case None => None
      }
    ) else (
      match valToPivotNode(v.val) {
        case Some(s) => Some(BC.SectorBlock(s))
        case None => None
      }
    )
  }

  function method {:opaque} parseSector(data: seq<byte>) : Option<Sector>
  requires |data| < 0x1_0000_0000_0000_0000;
  ensures var s := parseSector(data);
      s.Some? && s.value.SectorSuperblock? ==> BC.WFSuperblock(BC.Constants(), s.value.superblock)
  ensures var s := parseSector(data);
      s.Some? && s.value.SectorBlock? ==> BT.WFNode(s.value.block)

  {
    match parse_Val(data, SectorGrammar()).0 {
      case Some(v) => valToSector(v)
      case None => None
    }
  }
}
