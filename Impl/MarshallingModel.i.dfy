include "../lib/Marshalling/GenericMarshalling.i.dfy"
include "../PivotBetree/PivotBetreeSpec.i.dfy"
include "../lib/Base/Message.i.dfy"
include "StateModel.i.dfy"
include "../lib/Base/Crypto.s.dfy"
include "../lib/Base/Option.s.dfy"
include "../lib/Base/NativeArrays.s.dfy"
include "../lib/DataStructures/MutableMapImpl.i.dfy"
include "KVList.i.dfy"
//
// Parses bytes and returns the data structure (a Pivot-Node Sector) used by
// the Model.
//
// Annoyingly, our marshaling framework doesn't enforce bijectivity.
// So we talk only about parsing, and define marshal(X) as anything
// that produces an output that parses to X.
//
// TODO(jonh): rename to ModelParsing.
//

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
  import SM = StateModel
  import KVList
  import Crypto
  import NativeArrays
  import IndirectionTableModel
  import SeqComparison

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
  import Keyspace = Lexicographic_Byte_Order

  import MM = MutableMap

  type Reference = BC.Reference
  type LBA = BC.LBA
  type Location = BC.Location
  type Sector = SM.Sector
  type Node = SM.Node

  /////// Grammar

  function method BucketGrammar() : G
  ensures ValidGrammar(BucketGrammar())
  {
    GTuple([
      GKeyArray,
      GMessageArray
    ])
  }

  function method PivotNodeGrammar() : G
  ensures ValidGrammar(PivotNodeGrammar())
  {
    GTuple([
        GKeyArray, // pivots
        GUint64Array, // children
        GArray(BucketGrammar()) 
    ])
  }

  function method SectorGrammar() : G
  ensures ValidGrammar(SectorGrammar())
  {
    GTaggedUnion([IndirectionTableModel.IndirectionTableGrammar(), PivotNodeGrammar()])    
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

  function method valToChildren(v: V) : Option<seq<Reference>>
  requires ValInGrammar(v, GUint64Array)
  {
    Some(v.ua)
  }


  function valToUint64Seq(v: V) : (s : seq<uint64>)
  requires ValInGrammar(v, GUint64Array)
  {
    v.ua
  }

  predicate isStrictlySortedKeySeqIterate(a: seq<Key>, i: int)
  requires 1 <= i <= |a|
  decreases |a| - i
  ensures isStrictlySortedKeySeqIterate(a, i) <==> Keyspace.IsStrictlySorted(a[i-1..])
  {
    Keyspace.reveal_IsStrictlySorted();

    if i == |a| then (
      true
    ) else (
      if (Keyspace.lt(a[i-1], a[i])) then (
        isStrictlySortedKeySeqIterate(a, i+1)
      ) else (
        false
      )
    )
  }

  predicate {:opaque} isStrictlySortedKeySeq(a: seq<Key>)
  ensures isStrictlySortedKeySeq(a) <==> Keyspace.IsStrictlySorted(a)
  {
    Keyspace.reveal_IsStrictlySorted();

    if |a| >= 2 then (
      isStrictlySortedKeySeqIterate(a, 1)
    ) else (
      true
    )
  }

  function valToStrictlySortedKeySeq(v: V) : (s : Option<seq<Key>>)
  requires ValidVal(v)
  requires ValInGrammar(v, GKeyArray)
  ensures s.Some? ==> Keyspace.IsStrictlySorted(s.value)
  ensures s.Some? ==> |s.value| == |v.baa|
  decreases |v.baa|
  {
    if isStrictlySortedKeySeq(v.baa) then
      var blah : seq<Key> := v.baa;
      Some(v.baa)
    else
      None
  }

  function valToPivots(v: V) : (s : Option<seq<Key>>)
  requires ValidVal(v)
  requires ValInGrammar(v, GKeyArray)
  ensures s.Some? ==> Pivots.WFPivots(s.value)
  ensures s.Some? ==> |s.value| == |v.baa|
  {
    var s := valToStrictlySortedKeySeq(v);
    if s.Some? && (|s.value| > 0 ==> |s.value[0]| != 0) then (
      if |s.value| > 0 then (
        SeqComparison.reveal_lte();
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
  requires ValInGrammar(v, GMessageArray)
  ensures s.Some? ==> forall i | 0 <= i < |s.value| :: s.value[i] != M.IdentityMessage()
  ensures s.Some? ==> |s.value| == |v.ma|
  decreases |v.ma|
  {
    assert forall i | 0 <= i < |v.ma| :: ValidMessage(v.ma[i]);
    Some(v.ma)
  }

  function {:fuel ValInGrammar,2} valToBucket(v: V, pivotTable: seq<Key>, i: int) : (s : Option<KVList.Kvl>)
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
        Some(kvl)
      else
        None
    ) else (
      None
    )
  }

  function IKVListOpt(table : Option<KVList.Kvl>): Option<map<Key, Message>>
  requires table.Some? ==> KVList.WF(table.value)
  {
    if table.Some? then
      Some(KVList.I(table.value))
    else
      None
  }

  function valToBuckets(a: seq<V>, pivotTable: seq<Key>) : (s : Option<seq<Bucket>>)
  requires Pivots.WFPivots(pivotTable)
  requires forall i | 0 <= i < |a| :: ValidVal(a[i])
  requires forall i | 0 <= i < |a| :: ValInGrammar(a[i], BucketGrammar())
  requires |a| <= |pivotTable| + 1
  ensures s.Some? ==> |s.value| == |a|
  ensures s.Some? ==> forall i | 0 <= i < |s.value| :: WFBucketAt(s.value[i], pivotTable, i)
  {
    if |a| == 0 then
      Some([])
    else (
      match valToBuckets(DropLast(a), pivotTable) {
        case None => None
        case Some(pref) => (
          match valToBucket(Last(a), pivotTable, |pref|) {
            case Some(bucket) => Some(pref + [KVList.I(bucket)])
            case None => None
          }
        )
      }
    )
  }

  function {:fuel ValInGrammar,2} valToNode(v: V) : (s : Option<Node>)
  requires ValidVal(v)
  requires ValInGrammar(v, PivotNodeGrammar())
  // Pivots.NumBuckets(node.pivotTable) == |node.buckets|
  ensures s.Some? ==> SM.WFNode(s.value)
  ensures s.Some? ==> BT.WFNode(SM.INode(s.value))
  {
    assert ValidVal(v.t[0]);
    assert ValidVal(v.t[1]);
    assert ValidVal(v.t[2]);
    var pivots_len := |v.t[0].baa| as uint64;
    var children_len := |v.t[1].ua| as uint64;
    var buckets_len := |v.t[2].a| as uint64;

    if (
       && pivots_len <= MaxNumChildrenUint64() - 1
       && (children_len == 0 || children_len == pivots_len + 1)
       && buckets_len == pivots_len + 1
    ) then (
      assert ValidVal(v.t[0]);
      match valToPivots(v.t[0]) {
        case None => None
        case Some(pivots) => (
          match valToChildren(v.t[1]) {
            case None => None
            case Some(children) => (
              assert ValidVal(v.t[2]);
              match valToBuckets(v.t[2].a, pivots) {
                case None => None
                case Some(buckets) => (
                  if WeightBucketList(buckets) <= MaxTotalBucketWeight() then (
                    var node := SM.Node(
                      pivots,
                      if |children| == 0 then None else Some(children),
                      buckets);
                    Some(node)
                  ) else (
                    None
                  )
                )
              }
            )
          }
        )
      }
    ) else (
      None
    )
  }

  function valToSector(v: V) : (s : Option<Sector>)
  requires ValidVal(v)
  requires ValInGrammar(v, SectorGrammar())
  {
    if v.c == 0 then (
      match IndirectionTableModel.valToIndirectionTable(v.val) {
        case Some(s) => Some(SM.SectorIndirectionTable(s))
        case None => None
      }
    ) else (
      match valToNode(v.val) {
        case Some(s) => Some(SM.SectorBlock(s))
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
  ensures s.Some? ==> SM.WFSector(s.value)
  ensures s.Some? && s.value.SectorIndirectionTable? ==>
      IndirectionTableModel.TrackingGarbage(s.value.indirectionTable)
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
  ensures s.Some? ==> SM.WFSector(s.value)
  ensures s.Some? && s.value.SectorIndirectionTable? ==>
      IndirectionTableModel.TrackingGarbage(s.value.indirectionTable)
  {
    if |data| >= 32 && Crypto.Crc32C(data[32..]) == data[..32] then
      parseSector(data[32..])
    else
      None
  }
}
