include "../ByteBlockCacheSystem/Marshalling.i.dfy"
include "StateModel.i.dfy"
include "IndirectionTableModel.i.dfy"

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

module MarshallingModel {
  import opened GenericMarshalling
  import opened Options
  import opened NativeTypes
  import opened Sequences
  import opened Maps
  import opened BucketsLib
  import opened BucketWeights
  import opened Bounds
  import BC = BlockCache
  import SM = StateModel
  import Crypto
  import NativeArrays
  import IndirectionTableModel
  import SeqComparison
  import Marshalling
  import PackedKVMarshalling
  import PackedKV
  
  import BT = PivotBetreeSpec`Internal

  // This is one of the few places where we actually
  // care what a reference, lba etc. are,
  // so we open all these things up.
  // This lets us see, e.g., that a reference fits
  // in a 64-bit int.
  import M = ValueMessage`Internal
  import ReferenceType`Internal
  import ValueType`Internal

  import Pivots = PivotsLib
  import MS = MapSpec
  import Keyspace = Lexicographic_Byte_Order

  import MM = MutableMap

  type Key = Keyspace.Element
  type Reference = BC.Reference
  type Sector = SM.Sector
  type Node = SM.Node

  /////// Some lemmas that are useful in Impl

  lemma WeightBucketListLteSize(v: V, buckets: seq<Bucket>)
  requires v.VArray?
  requires Marshalling.valToBuckets.requires(v.a)
  requires Marshalling.valToBuckets(v.a) == Some(buckets)
  ensures WeightBucketList(buckets) <= SizeOfV(v)

  decreases |v.a|
  {
    if |buckets| == 0 {
      reveal_WeightBucketList();
    } else {
      var prebuckets := DropLast(buckets);
      var prev := VArray(DropLast(v.a));
      var lastbucket := Last(buckets);
      var lastv := Last(v.a);

      assert WeightBucket(lastbucket) <= SizeOfV(lastv)
      by {
        var pkv := PackedKVMarshalling.fromVal(lastv).value;
        PackedKVMarshalling.SizeOfVPackedKVIsBucketWeight(pkv);
        PackedKVMarshalling.uniqueMarshalling(lastv);
      }

      calc <= {
        WeightBucketList(buckets);
        { reveal_WeightBucketList(); }
        WeightBucketList(prebuckets) + WeightBucket(lastbucket);
        { WeightBucketListLteSize(prev, prebuckets); }
        SizeOfV(prev) + WeightBucket(lastbucket);
        {
          lemma_SeqSum_prefix(prev.a, lastv);
          assert v.a == prev.a + [lastv];
        }
        SizeOfV(v);
      }
    }
  }

  lemma SizeOfVTupleElem_le_SizeOfV(v: V, i: int)
  requires v.VTuple?
  requires 0 <= i < |v.t|
  ensures SizeOfV(v.t[i]) <= SizeOfV(v)

  decreases |v.t|
  {
    lemma_SeqSum_prefix(DropLast(v.t), Last(v.t));
    assert DropLast(v.t) + [Last(v.t)] == v.t;
    if i < |v.t| - 1 {
      SizeOfVTupleElem_le_SizeOfV(VTuple(DropLast(v.t)), i);
    }
  }

  lemma SizeOfVArrayElem_le_SizeOfV(v: V, i: int)
  requires v.VArray?
  requires 0 <= i < |v.a|
  ensures SizeOfV(v.a[i]) <= SizeOfV(v)

  decreases |v.a|
  {
    lemma_SeqSum_prefix(DropLast(v.a), Last(v.a));
    assert DropLast(v.a) + [Last(v.a)] == v.a;
    if i < |v.a| - 1 {
      SizeOfVArrayElem_le_SizeOfV(VArray(DropLast(v.a)), i);
    }
  }

  lemma SizeOfVArrayElem_le_SizeOfV_forall(v: V)
  requires v.VArray?
  ensures forall i | 0 <= i < |v.a| :: SizeOfV(v.a[i]) <= SizeOfV(v)
  {
    forall i | 0 <= i < |v.a| ensures SizeOfV(v.a[i]) <= SizeOfV(v)
    {
      SizeOfVArrayElem_le_SizeOfV(v, i);
    }
  }

  /////// Conversion from PivotNode to a val

  function method refToVal(ref: Reference) : (v : V)
  ensures ValidVal(v)
  ensures SizeOfV(v) == 8
  {
    VUint64(ref)
  }

  function {:fuel ValInGrammar,2} valToNode(v: V) : (s : Option<Node>)
  requires ValidVal(v)
  requires ValInGrammar(v, Marshalling.PivotNodeGrammar())
  ensures s.Some? ==> SM.WFNode(s.value)
  ensures s.Some? ==> BT.WFNode(SM.INode(s.value))
  {
    // TODO(travis): is there any reason to SM.Node be a different
    // type than BC.G.Node?
    var node := Marshalling.valToNode(v);
    if node.Some? then (
      Some(SM.Node(node.value.pivotTable, node.value.children, node.value.buckets))
    ) else (
      None
    )
  }

  /////// Marshalling and de-marshalling

  function valToSector(v: V) : (s : Option<Sector>)
  requires ValidVal(v)
  requires ValInGrammar(v, Marshalling.SectorGrammar())
  {
    if v.c == 0 then (
      match Marshalling.valToSuperblock(v.val) {
        case Some(s) => Some(SM.SectorSuperblock(s))
        case None => None
      }
    ) else if v.c == 1 then (
      match IndirectionTableModel.valToIndirectionTable(v.val) {
        case Some(s) => Some(SM.SectorIndirectionTable(s))
        case None => None
      }
    ) else (
      match valToNode(v.val) {
        case Some(s) => Some(SM.SectorNode(s))
        case None => None
      }
    )
  }

  function {:opaque} parseSector(data: seq<byte>) : (s : Option<Sector>)
  ensures s.Some? ==> SM.WFSector(s.value)
  ensures s.Some? ==> Some(SM.ISector(s.value)) == Marshalling.parseSector(data)
  ensures s.None? ==> Marshalling.parseSector(data).None?
  ensures s.Some? && s.value.SectorIndirectionTable? ==>
      IndirectionTableModel.TrackingGarbage(s.value.indirectionTable)
  {
    Marshalling.reveal_parseSector();

    if |data| < 0x1_0000_0000_0000_0000 then (
      match parse_Val(data, Marshalling.SectorGrammar()).0 {
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
  ensures s.Some? ==> Some(SM.ISector(s.value)) == Marshalling.parseCheckedSector(data)
  ensures s.None? ==> Marshalling.parseCheckedSector(data).None?
  ensures s.Some? && s.value.SectorIndirectionTable? ==>
      IndirectionTableModel.TrackingGarbage(s.value.indirectionTable)
  {
    Marshalling.reveal_parseCheckedSector();

    if |data| >= 32 && Crypto.Crc32C(data[32..]) == data[..32] then
      parseSector(data[32..])
    else
      None
  }

}
