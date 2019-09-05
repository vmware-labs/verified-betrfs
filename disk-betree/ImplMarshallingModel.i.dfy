include "../lib/Marshalling/GenericMarshalling.i.dfy"
include "PivotBetreeSpec.i.dfy"
include "Message.i.dfy"
include "ImplModel.i.dfy"
include "KMTable.i.dfy"
include "../lib/Crypto.s.dfy"
include "../lib/Option.s.dfy"
include "../lib/MutableMap.i.dfy"

module ImplMarshallingModel {
  import opened GenericMarshalling
  import opened Options
  import opened NativeTypes
  import opened Sequences
  import opened Maps
  import opened BucketsLib
  import opened BucketWeights
  import opened Bounds
  import BC = BetreeGraphBlockCache
  import IM = ImplModel
  import KMTable`Internal
  import KVList
  import Crypto
  import Native

  import BT = PivotBetreeSpec`Internal

  // This is one of the few places where we actually
  // care what a reference, lba etc. are,
  // so we open all these things up.
  // This lets us see, e.g., that a reference fits
  // in a 64-bit int.
  import M = ValueMessage`Internal
  import ReferenceType`Internal
  import LBAType
  import ValueWithDefault`Internal

  import Pivots = PivotsLib
  import MS = MapSpec
  import Keyspace = MS.Keyspace

  import MM = MutableMap

  type Reference = BC.Reference
  type LBA = BC.LBA
  type Location = BC.Location
  type Sector = IM.Sector
  type Message = M.Message
  type Key = BT.G.Key
  type Node = IM.Node

  /////// Grammar

  function method IndirectionTableGrammar() : G
  ensures ValidGrammar(IndirectionTableGrammar())
  {
    // (Reference, address, len, successor-list) triples
    GArray(GTuple([GUint64, GUint64, GUint64, GUint64Array]))
  }

  function method BucketGrammar() : G
  ensures ValidGrammar(BucketGrammar())
  {
    GTuple([
      GArray(GByteArray),
      GArray(GByteArray)
    ])
  }

  function method PivotNodeGrammar() : G
  ensures ValidGrammar(PivotNodeGrammar())
  {
    GTuple([
        GArray(GByteArray), // pivots
        GUint64Array, // children
        GArray(BucketGrammar()) 
    ])
  }

  function method SectorGrammar() : G
  ensures ValidGrammar(SectorGrammar())
  {
    GTaggedUnion([IndirectionTableGrammar(), PivotNodeGrammar()])    
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

  function method valToChildren(v: V) : Option<seq<Reference>>
  requires ValInGrammar(v, GUint64Array)
  {
    Some(v.ua)
  }

  function method {:fuel ValInGrammar,3} valToLocsAndSuccs(a: seq<V>) : (s : Option<map<uint64, (Option<Location>, seq<Reference>)>>)
  requires forall i | 0 <= i < |a| :: ValInGrammar(a[i], GTuple([GUint64, GUint64, GUint64, GUint64Array]))
  ensures s.Some? ==> forall v | v in s.value.Values :: v.0.Some? && BC.ValidLocationForNode(v.0.value)
  {
    if |a| == 0 then
      Some(map[])
    else (
      var res := valToLocsAndSuccs(DropLast(a));
      match res {
        case Some(table) => (
          var tuple := Last(a);
          var ref := valToReference(tuple.t[0]);
          var lba := valToLBA(tuple.t[1]);
          var len := tuple.t[2].u;
          var succs := valToChildren(tuple.t[3]);
          match succs {
            case None => None
            case Some(succs) => (
              var loc := LBAType.Location(lba, len);
              if ref in table || lba == 0 || !LBAType.ValidLocation(loc) then (
                None
              ) else (
                Some(table[ref := (Some(loc), succs)])
              )
            )
          }
        )
        case None => None
      }
    )
  }

  function valToIndirectionTable(v: V) : (s : Option<IM.IndirectionTable>)
  requires ValInGrammar(v, IndirectionTableGrammar())
  ensures s.Some? ==> BC.WFCompleteIndirectionTable(IM.IIndirectionTable(s.value))
  {
    var res := valToLocsAndSuccs(v.a);
    match res {
      case Some(res) => (
        var graph := IM.IIndirectionTable(res).graph;
        if BT.G.Root() in graph && BC.GraphClosed(graph) then (
          Some(res)
        ) else (
          None
        )
      )
      case None => None
    }
  }

  function valToUint64Seq(v: V) : (s : seq<uint64>)
  requires ValInGrammar(v, GUint64Array)
  {
    v.ua
  }

  function valToStrictlySortedKeySeq(v: V) : (s : Option<seq<Key>>)
  requires ValidVal(v)
  requires ValInGrammar(v, GArray(GByteArray))
  ensures s.Some? ==> Keyspace.IsStrictlySorted(s.value)
  ensures s.Some? ==> |s.value| == |v.a|
  decreases |v.a|
  {
    if |v.a| == 0 then
      Some([])
    else
      match valToStrictlySortedKeySeq(VArray(DropLast(v.a))) {
        case None => None
        case Some(pref) => (
          assert ValInGrammar(Last(v.a), GByteArray);
          var key := Last(v.a).b;

          if (|key| <= Keyspace.MaxLen() as int && (|pref| > 0 ==> Keyspace.lt(Last(pref), key))) then (
            Keyspace.reveal_seq_lte();
            Keyspace.StrictlySortedAugment(pref, key);

            var k : Key := key;

            Some(pref + [k])
          ) else (
            None
          )
        )
      }
  }

  function valToPivots(v: V) : (s : Option<seq<Key>>)
  requires ValidVal(v)
  requires ValInGrammar(v, GArray(GByteArray))
  ensures s.Some? ==> Pivots.WFPivots(s.value)
  {
    var s := valToStrictlySortedKeySeq(v);
    if s.Some? && (|s.value| > 0 ==> |s.value[0]| != 0) then (
      if |s.value| > 0 then (
        Keyspace.reveal_seq_lte();
        Keyspace.IsNotMinimum([], s.value[0]);
        s
      ) else (
        s
      )
    ) else (
      None
    )
  }

  function {:fuel ValInGrammar,2} valToMessageSeq(v: V) : (s : Option<seq<Message>>)
  requires ValidVal(v)
  requires ValInGrammar(v, GArray(GByteArray))
  ensures s.Some? ==> forall i | 0 <= i < |s.value| :: s.value[i] != M.IdentityMessage()
  ensures s.Some? ==> |s.value| == |v.a|
  decreases |v.a|
  {
    if |v.a| == 0 then Some([]) else (
      assert ValInGrammar(Last(v.a), GByteArray);
      var pref := valToMessageSeq(VArray(DropLast(v.a)));
      if pref.Some? && |Last(v.a).b| <= ValueWithDefault.MaxLen() as int then (
        var val : ValueWithDefault.Value := Last(v.a).b;
        var msg := M.Define(val);
        Some(pref.value + [msg])
      ) else (
        None
      )
    )
  }

  function {:fuel ValInGrammar,2} valToBucket(v: V, pivotTable: seq<Key>, i: int) : (s : Option<KMTable.KMT>)
  requires ValidVal(v)
  requires ValInGrammar(v, BucketGrammar())
  requires Pivots.WFPivots(pivotTable)
  requires 0 <= i <= |pivotTable|
  {
    var keys := valToStrictlySortedKeySeq(v.t[0]);
    var values := valToMessageSeq(v.t[1]);

    if keys.Some? && values.Some? then (
      var kvl := KVList.Kvl(keys.value, values.value);

      if KVList.WF(kvl) && WFBucketAt(KVList.I(kvl), pivotTable, i) then
        assume WeightBucket(KVList.I(kvl)) < 0x1_0000_0000_0000_0000;
        var kmt := KMTable.toKmt(kvl);
        Some(kmt)
      else
        None
    ) else (
      None
    )
  }

  function IKMTableOpt(table : Option<KMTable.KMT>): Option<map<Key, Message>>
  requires table.Some? ==> KMTable.WF(table.value)
  {
    if table.Some? then
      Some(KMTable.I(table.value))
    else
      None
  }

  function valToBuckets(a: seq<V>, pivotTable: seq<Key>) : (s : Option<seq<KMTable.KMT>>)
  requires Pivots.WFPivots(pivotTable)
  requires forall i | 0 <= i < |a| :: ValidVal(a[i])
  requires forall i | 0 <= i < |a| :: ValInGrammar(a[i], BucketGrammar())
  requires |a| <= |pivotTable| + 1
  ensures s.Some? ==> |s.value| == |a|
  ensures s.Some? ==> forall i | 0 <= i < |s.value| :: KMTable.WF(s.value[i]) && WFBucketAt(KMTable.I(s.value[i]), pivotTable, i)
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

  function ISeqKMTableOpt(s : Option<seq<KMTable.KMT>>): Option<seq<map<Key, Message>>>
  requires s.Some? ==> forall i: nat :: i < |s.value| ==> KMTable.WF(s.value[i])
  {
    if s.Some? then
      Some(Apply(KMTable.I, s.value))
    else
      None
  }

  function {:fuel ValInGrammar,2} valToNode(v: V) : (s : Option<Node>)
  requires ValidVal(v)
  requires ValInGrammar(v, PivotNodeGrammar())
  // Pivots.NumBuckets(node.pivotTable) == |node.buckets|
  ensures s.Some? ==> IM.WFNode(s.value)
  ensures s.Some? ==> BT.WFNode(IM.INode(s.value))
  {
    assert ValidVal(v.t[0]);
    match valToPivots(v.t[0]) {
      case None => None
      case Some(pivots) => (
        match valToChildren(v.t[1]) {
          case None => None
          case Some(children) => (
            if ((|children| == 0 || |children| == |pivots| + 1) && |v.t[2].a| == |pivots| + 1) then (
              assert ValidVal(v.t[2]);
              match valToBuckets(v.t[2].a, pivots) {
                case None => None
                case Some(buckets) => (
                  if
                    && |buckets| <= MaxNumChildren()
                    && WeightBucketList(KMTable.ISeq(buckets)) <= MaxTotalBucketWeight()
                  then (
                    var node := IM.Node(pivots, if |children| == 0 then None else Some(children), buckets);
                    Some(node)
                  ) else (
                    None
                  )
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

  function valToSector(v: V) : (s : Option<Sector>)
  requires ValidVal(v)
  requires ValInGrammar(v, SectorGrammar())
  {
    if v.c == 0 then (
      match valToIndirectionTable(v.val) {
        case Some(s) => Some(IM.SectorIndirectionTable(s))
        case None => None
      }
    ) else (
      match valToNode(v.val) {
        case Some(s) => Some(IM.SectorBlock(s))
        case None => None
      }
    )
  }


  /////// Conversion from PivotNode to a val

  function method refToVal(ref: Reference) : (v : V)
  ensures ValidVal(v)
  ensures SizeOfV(v) == 8
  {
    VUint64(ref)
  }

  function method lbaToVal(lba: LBA) : (v : V)
  ensures ValidVal(v)
  ensures SizeOfV(v) == 8
  {
    VUint64(lba)
  }

  /////// Marshalling and de-marshalling

  function {:opaque} parseSector(data: seq<byte>) : (s : Option<Sector>)
  ensures s.Some? ==> IM.WFSector(s.value)
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

  /////// Marshalling and de-marshalling with checksums

  function {:opaque} parseCheckedSector(data: seq<byte>) : (s : Option<Sector>)
  ensures s.Some? ==> IM.WFSector(s.value)
  {
    if |data| >= 32 && Crypto.Crc32(data[32..]) == data[..32] then
      parseSector(data[32..])
    else
      None
  }
}
