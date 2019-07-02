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
  import opened Maps
  import BC = BetreeGraphBlockCache

  import BT = PivotBetreeSpec`Internal

  // This is one of the few places where we actually
  // care what a reference, lba etc. are,
  // so we open all these things up.
  // This lets us see, e.g., that a reference fits
  // in a 64-bit int.
  import M = ValueMessage`Internal
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
  ensures var s := valToSuperblock(v) ; s.Some? ==> BC.WFPersistentSuperblock(s.value)
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
  ensures var s := valToKeyMessageMap(a, pivotTable, i) ; s.Some? ==> BT.WFBucket(s.value, pivotTable, i)
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
  ensures var s := valToBucket(v, pivotTable, i) ; s.Some? ==> BT.WFBucket(s.value, pivotTable, i)
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
  ensures var s := valToBuckets(a, pivotTable) ; s.Some? ==> forall i | 0 <= i < |s.value| :: BT.WFBucket(s.value[i], pivotTable, i)
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
      s.Some? && s.value.SectorSuperblock? ==> BC.WFPersistentSuperblock(s.value.superblock)
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

  /////// Conversion from PivotNode to a val

  function method refToVal(ref: Reference) : V
  ensures ValidVal(refToVal(ref))
  {
    VUint64(ref)
  }

  function method lbaToVal(lba: LBA) : V
  ensures ValidVal(lbaToVal(lba))
  {
    VUint64(lba)
  }

  function method refcountToVal(refcount: int) : Option<V>
  ensures refcountToVal(refcount).Some? ==> ValidVal(refcountToVal(refcount).value)
  {
    if (0 <= refcount < 0x1_0000_0000_0000_000) then (
      Some(VUint64(refcount as uint64))
    ) else (
      None
    )
  }

  method {:fuel ValInGrammar,2} lbasRefcountsToVal(lbas: map<Reference, LBA>, refcounts: map<Reference, int>) returns (v: Option<V>)
  requires lbas.Keys == refcounts.Keys
  requires 0 !in lbas.Values
  requires |lbas| < 0x1_0000_0000_0000_0000
  ensures v.Some? ==> ValidVal(v.value)
  ensures v.Some? ==> ValInGrammar(v.value, SuperblockGrammar());
  ensures v.Some? ==> |v.value.a| == |lbas|
  ensures v.Some? ==> valToLBAsAndRefcounts(v.value.a) == Some((lbas, refcounts));
  {
    if (|lbas| == 0) {
      assert lbas == map[];
      assert refcounts == map[];
      return Some(VArray([]));
    } else {
      var ref :| ref in lbas.Keys;
      var vpref := lbasRefcountsToVal(MapRemove(lbas, {ref}), MapRemove(refcounts, {ref}));
      match vpref {
        case None => return None;
        case Some(vpref) => {
          var lba := lbas[ref];
          var refcount := refcountToVal(refcounts[ref]);
          if refcount.Some? {
            var tuple := VTuple([refToVal(ref), lbaToVal(lba), refcount.value]);

            //assert valToLBAsAndRefcounts(vpref.a) == Some((MapRemove(lbas, {ref}), MapRemove(refcounts, {ref})));
            assert MapRemove(lbas, {ref})[ref := lba] == lbas;
            assert MapRemove(refcounts, {ref})[ref := refcounts[ref]] == refcounts;
            //assert ref == valToReference(tuple.t[0]);
            //assert lba == valToReference(tuple.t[1]);
            //assert !(ref in MapRemove(refcounts, {ref}));
            //assert !(lba == 0);
            //assert valToLBAsAndRefcounts(vpref.a + [tuple]) == Some((lbas, refcounts));

            return Some(VArray(vpref.a + [tuple]));
          } else {
            return None;
          }
        }
      }
    }
  }

  method messageToVal(m: Message) returns (v : Option<V>)
  requires m != M.IdentityMessage()
  ensures v.Some? ==> ValidVal(v.value)
  ensures v.Some? ==> ValInGrammar(v.value, MessageGrammar())
  ensures v.Some? ==> valToMessage(v.value) == Some(m)
  {
    if |m.value| < 0x1_0000_0000_0000_0000 {
      return Some(VByteArray(m.value));
    } else {
      return None;
    }
  }

  // We pass in pivotTable and i so we can state the pre- and post-conditions.
  method {:fuel ValInGrammar,2} bucketToVal(bucket: Bucket, ghost pivotTable: Pivots.PivotTable, ghost i: int) returns (v: Option<V>)
  requires Pivots.WFPivots(pivotTable)
  requires BT.WFBucket(bucket, pivotTable, i)
  requires |bucket| < 0x1_0000_0000_0000_0000
  ensures v.Some? ==> ValInGrammar(v.value, BucketGrammar())
  ensures v.Some? ==> |v.value.a| == |bucket|
  ensures v.Some? ==> ValidVal(v.value)
  ensures v.Some? ==> valToBucket(v.value, pivotTable, i) == Some(bucket)
  {
    if (|bucket| == 0) {
      return Some(VArray([]));
    } else {
      var key :| key in bucket;

      if (|key| >= 0x1_0000_0000_0000_0000) { return None; }
      
      var msg := bucket[key];
      var bucket' := MapRemove(bucket, {key});
      var v' := bucketToVal(bucket', pivotTable, i);
      match v' {
        case None => { return None; }
        case Some(VArray(pref)) => {
          var vmsg := messageToVal(msg);
          match vmsg {
            case None => { return None; }
            case Some(vmsg) => {
              var pair := VTuple([VByteArray(key), vmsg]);
              assert bucket'[key := msg] == bucket;

              assert |pref + [pair]| == |bucket|; // observe
              forall v | v in pref + [pair]
              ensures ValidVal(v)
              {
              }

              return Some(VArray(pref + [pair])); 
            }
          }
        }
      }
    } 
  }

  method bucketsToVal(buckets: seq<Bucket>, ghost pivotTable: Pivots.PivotTable) returns (v: Option<V>)
  requires Pivots.WFPivots(pivotTable)
  requires forall i | 0 <= i < |buckets| :: BT.WFBucket(buckets[i], pivotTable, i)
  requires |buckets| < 0x1_0000_0000_0000_0000
  ensures v.Some? ==> ValidVal(v.value)
  ensures v.Some? ==> ValInGrammar(v.value, GArray(BucketGrammar()))
  ensures v.Some? ==> |v.value.a| == |buckets|
  ensures v.Some? ==> valToBuckets(v.value.a, pivotTable) == Some(buckets)
  {
    if |buckets| == 0 {
      return Some(VArray([]));
    } else {
      var pref := bucketsToVal(DropLast(buckets), pivotTable);
      match pref {
        case None => { return None; }
        case Some(pref) => {
          var bucket := Last(buckets);
          if (|bucket| >= 0x1_0000_0000_0000_0000) { return None; }
          var bucketVal := bucketToVal(bucket, pivotTable, |buckets| - 1);
          match bucketVal {
            case None => { return None; }
            case Some(bucketVal) => {
              assert buckets == DropLast(buckets) + [Last(buckets)]; // observe
              return Some(VArray(pref.a + [bucketVal]));
            }
          }
        }
      }
    }
  }

  lemma KeyInPivotsIsNonempty(pivots: seq<Key>, key: Key)
  requires Pivots.WFPivots(pivots)
  requires |pivots| > 0
  requires Last(pivots) == key
  ensures |key| != 0;
  {
    var e := Keyspace.SmallerElement(pivots[0]);
    Keyspace.reveal_IsStrictlySorted();
    assert Keyspace.lte(pivots[0], key);
    assert Keyspace.lt(e, key);
    Keyspace.reveal_seq_lte();
    assert key != [];
  }

  method pivotsToVal(pivots: seq<Key>) returns (v : Option<V>)
  requires Pivots.WFPivots(pivots)
  requires |pivots| < 0x1_0000_0000_0000_0000
  ensures v.Some? ==> ValidVal(v.value)
  ensures v.Some? ==> ValInGrammar(v.value, GArray(GByteArray))
  ensures v.Some? ==> |v.value.a| == |pivots|
  ensures v.Some? ==> valToPivots(v.value.a) == Some(pivots)
  {
    if |pivots| == 0 {
      return Some(VArray([]));
    } else {
      var pivots' := DropLast(pivots);
      Keyspace.StrictlySortedPop(pivots);
      var prefOpt := pivotsToVal(pivots');
      if prefOpt.None? { return None; }
      var pref := prefOpt.value;

      var key := Last(pivots);
      if (|key| >= 0x1_0000_0000_0000_0000) { return None; }

      var last := VByteArray(key);
      assert ValidVal(last); // observe

      assert pivots == DropLast(pivots) + [key];
      KeyInPivotsIsNonempty(pivots, key);
      assert |key| != 0;
      if |pivots'| > 0 {
        Keyspace.IsStrictlySortedImpliesLt(pivots, |pivots| - 2, |pivots| - 1);
        assert Keyspace.lt(Last(pivots'), key);
      }

      return Some(VArray(pref.a + [last]));
    }
  }

  method childrenToVal(children: seq<Reference>) returns (v : V)
  requires |children| < 0x1_0000_0000_0000_0000
  ensures ValidVal(v)
  ensures ValInGrammar(v, GArray(GUint64))
  ensures valToChildren(v.a) == Some(children)
  ensures |v.a| == |children|
  {
    if |children| == 0 {
      return VArray([]);
    } else {
      var children' := DropLast(children);
      var pref := childrenToVal(children');
      var child := Last(children);
      var last := VUint64(child);
      assert children == DropLast(children) + [child];
      return VArray(pref.a + [last]);
    }
  }

  method nodeToVal(node: Node) returns (v : Option<V>)
  requires BT.WFNode(node)
  ensures v.Some? ==> ValidVal(v.value)
  ensures v.Some? ==> ValInGrammar(v.value, PivotNodeGrammar())
  ensures v.Some? ==> valToPivotNode(v.value) == Some(node)
  {
    forall i | 0 <= i < |node.buckets|
    ensures BT.WFBucket(node.buckets[i], node.pivotTable, i);
    {
      assert BT.NodeHasWFBucketAt(node, i);
    }

    if (|node.buckets| >= 0x1_0000_0000_0000_0000) { return None; }
    var buckets := bucketsToVal(node.buckets, node.pivotTable);

    match buckets {
      case None => { return None; }
      case Some(buckets) => {
        var pivots := pivotsToVal(node.pivotTable);
        if (pivots.None?) { return None; }

        var children;
        if node.children.Some? {
          children := childrenToVal(node.children.value);
        } else {
          children := VArray([]);
        }
          
        return Some(VTuple([pivots.value, children, buckets]));
      }
    }
  }

  method sectorToVal(sector: Sector) returns (v : Option<V>)
  requires sector.SectorSuperblock? ==> BC.WFPersistentSuperblock(sector.superblock);
  requires sector.SectorBlock? ==> BT.WFNode(sector.block);
  ensures v.Some? ==> ValidVal(v.value)
  ensures v.Some? ==> ValInGrammar(v.value, SectorGrammar());
  ensures v.Some? ==> valToSector(v.value) == Some(sector)
  {
    match sector {
      case SectorSuperblock(Superblock(lbas, refcounts)) => {
        if |lbas| < 0x1_0000_0000_0000_0000 {
          var w := lbasRefcountsToVal(lbas, refcounts);
          match w {
            case Some(v) => return Some(VCase(0, v));
            case None => return None;
          }
        } else {
          return None;
        }
      }
      case SectorBlock(node) => {
        var w := nodeToVal(node);
        match w {
          case Some(v) => return Some(VCase(1, v));
          case None => return None;
        }
      }
    }
  }
  
  /////// Marshalling and de-marshalling

  function method {:opaque} parseSector(data: seq<byte>) : Option<Sector>
  ensures var s := parseSector(data);
      s.Some? && s.value.SectorSuperblock? ==> BC.WFPersistentSuperblock(s.value.superblock)
  ensures var s := parseSector(data);
      s.Some? && s.value.SectorBlock? ==> BT.WFNode(s.value.block)

  {
    if |data| < 0x1_0000_0000_0000_0000 then (
      match parse_Val(data, SectorGrammar()).0 {
        case Some(v) => valToSector(v)
        case None => None
      }
    ) else (
      None
    )
  }

  method ParseSector(data: array<byte>) returns (s : Option<Sector>)
  requires data.Length < 0x1_0000_0000_0000_0000;
  ensures s.Some? && s.value.SectorSuperblock? ==> BC.WFPersistentSuperblock(s.value.superblock)
  ensures s.Some? && s.value.SectorBlock? ==> BT.WFNode(s.value.block)
  {
    var success, v, rest_index := ParseVal(data, 0, SectorGrammar());
    if success {
      var s := valToSector(v);
      return s;
    } else {
      return None;
    }
  }

  method MarshallSector(sector: Sector) returns (data : array?<byte>)
  requires sector.SectorSuperblock? ==> BC.WFPersistentSuperblock(sector.superblock);
  requires sector.SectorBlock? ==> BT.WFNode(sector.block);
  ensures data != null ==> parseSector(data[..]) == Some(sector)
  {
    var v := sectorToVal(sector);
    match v {
      case None => return null;
      case Some(v) => {
        if (SizeOfV(v) < 0x1_0000_0000_0000_0000) {
          var data := Marshall(v, SectorGrammar());
          reveal_parseSector();
          return data;
        } else {
          return null;
        }
      }
    }
  }
}
