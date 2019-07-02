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
  import BT = PivotBetreeSpec
  import M = ValueMessage
  import ReferenceType
  import LBAType

  type Reference = BC.Reference
  type LBA = BC.LBA
  type Sector = BC.Sector
  type Message = M.Message
  type Bucket = BT.G.Bucket
  type Key = BT.G.Key
  type Node = BT.G.Node

  /////// Grammar

  function SuperblockGrammar() : G
  ensures ValidGrammar(SuperblockGrammar())
  {
    // (Reference, LBA, refcount) triples
    GArray(GTuple([GUint64, GUint64, GUint64]))
  }

  function MessageGrammar() : G
  ensures ValidGrammar(MessageGrammar())
  {
    // Always a Define message.
    GByteArray
  }

  function BucketGrammar() : G
  ensures ValidGrammar(BucketGrammar())
  {
    GArray(GTuple([GByteArray, MessageGrammar()]))
  }

  function PivotNodeGrammar() : G
  ensures ValidGrammar(PivotNodeGrammar())
  {
    GTuple([
        GArray(GByteArray), // pivots
        GArray(GUint64), // children
        GArray(BucketGrammar()) 
    ])
  }

  function SectorGrammar() : G
  ensures ValidGrammar(SectorGrammar())
  {
    GTaggedUnion([SuperblockGrammar(), PivotNodeGrammar()])    
  }

  function method valToReference(v: V) : Reference
  requires ValInGrammar(v, GUint64)
  {
    ReferenceType.toRef(v.u)
  }

  function method valToLBA(v: V) : LBA
  requires ValInGrammar(v, GUint64)
  {
    LBAType.toLBA(v.u)
  }

  function method valToInt(v: V) : int
  requires ValInGrammar(v, GUint64)
  {
    v.u as int
  }

  function method valToLBAsAndRefcounts(a: seq<V>) : Option<(map<Reference, LBA>, map<Reference, int>)>
  requires forall i | 0 <= i < |a| :: ValInGrammar(a[i], GTuple([GUint64, GUint64, GUint64]))
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
          if ref in refcounts then (
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

  function method valToKeyMessageMap(a: seq<V>) : Option<Bucket>
  requires forall i | 0 <= i < |a| :: ValInGrammar(a[i], GTuple([GByteArray, MessageGrammar()]))
  {
    if |a| == 0 then
      Some(map[])
    else (
      var res := valToKeyMessageMap(DropLast(a));
      match res {
        case Some(m) => (
          var tuple := Last(a);
          var key := tuple.t[0].b;
          var msg := valToMessage(tuple.t[1]);
          if key in res then (
            None
          ) else (
            Some(res[key := msg.value])
          )
        )
        case None => None
      }
    )
  }

  function method valToBucket(v: V) : Option<Bucket>
  requires ValInGrammar(v, BucketGrammar())
  {
    valToKeyMessageMap(v.a)
  }

  function method valToPivots(a: seq<V>) : Option<seq<Key>>
  requires forall i | 0 <= i < |a| :: ValInGrammar(a[i], GByteArray)
  {
    if |a| == 0 then
      Some([])
    else
      match valToPivots(DropLast(a)) {
        case None => None
        case Some(pref) => Some(pref + [valToKey(Last(a))])
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

  function method valToBuckets(a: seq<V>) : Option<seq<Bucket>>
  requires forall i | 0 <= i < |a| :: ValInGrammar(a[i], BucketGrammar())
  {
    if |a| == 0 then
      Some([])
    else (
      match valToBuckets(DropLast(a)) {
        case None => None
        case Some(pref) => (
          match valToBucket(Last(a)) {
            case Some(bucket) => Some(pref + [bucket])
            case None => None
          }
        )
      }
    )
  }

  function method valToPivotNode(v: V) : Option<Node>
  requires ValInGrammar(v, PivotNodeGrammar())
  {
    match valToPivots(v.t[0]) {
      case None => None
      case Some(pivots) => (
        match valToChildren(v.t[1]) {
          case None => None
          case Some(children) => (
            if (|children| == 0 || |children| == |pivots| + 1) then (
              match valToBuckets(v.t[2]) {
                case None => None
                case Some(buckets) => (
                  Node(pivots, if |children| == 0 then None else Some(children), buckets)
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
  {
    if v.c == 0 then (
      match valToSuperblock(v.val) {
        case Some(s) => SectorSuperblock(s)
        case None => None
      }
    ) else (
      match valToPivotNode(v.val) {
        case Some(s) => SectorBlock(s)
        case None => None
      }
    )
  }

  function method {:opaque} parseSector(data: seq<byte>) : Option<Sector>
  {
    match parse_Val(data, SectorGrammar()) {
      case Some(v) => valToSector(v)
      case None => None
    }
  }
}
