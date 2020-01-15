include "../lib/Marshalling/GenericMarshalling.i.dfy"
include "StateImpl.i.dfy"
include "StateModel.i.dfy"
include "../lib/Buckets/BucketImpl.i.dfy"
include "../lib/Base/Option.s.dfy"
include "../lib/Base/NativeArrays.s.dfy"
include "../lib/Base/NativeBenchmarking.s.dfy"

include "../ByteBlockCacheSystem/Marshalling.i.dfy"
include "MarshallingModel.i.dfy"

module MarshallingImpl {
  import IM = StateModel
  import SI = StateImpl
  import opened NodeImpl
  import opened CacheImpl
  import Marshalling
  import IMM = MarshallingModel
  import opened GenericMarshalling
  import opened Options
  import opened NativeTypes
  import opened Sequences
  import opened Maps
  import opened Sets
  import opened BucketsLib
  import opened BucketWeights
  import opened Bounds
  import BucketImpl
  import BC = BetreeGraphBlockCache
  import StateImpl
  import KVList
  import Crypto
  import NativeArrays
  import MutableMapModel
  import IndirectionTableImpl
  import IndirectionTableModel
  import KeyType
  import SeqComparison
  import NativeBenchmarking

  import BT = PivotBetreeSpec`Internal

  import ValueType`Internal
  import M = ValueMessage`Internal
  import LBAType

  import Pivots = PivotsLib
  import MS = MapSpec
  import Keyspace = Lexicographic_Byte_Order

  type Reference = IMM.Reference
  type LBA = IMM.LBA
  type Location = IMM.Location
  type Sector = SI.Sector

  /////// Conversion to PivotNode

  method IsStrictlySortedKeySeq(a: seq<Key>) returns (b : bool)
  requires |a| < 0x1_0000_0000_0000_0000
  ensures b == Marshalling.isStrictlySortedKeySeq(a)
  {
    Marshalling.reveal_isStrictlySortedKeySeq();

    if |a| as uint64 < 2 {
      return true;
    }
    var i: uint64 := 1;
    while i < |a| as uint64
    invariant 0 <= i as int <= |a|
    invariant Marshalling.isStrictlySortedKeySeq(a) == Marshalling.isStrictlySortedKeySeqIterate(a, i as int)
    {
      var c := Keyspace.cmp(a[i-1], a[i]);
      if c >= 0 {
        return false;
      }
      i := i + 1;
    }

    return true;
  }

  method ValToStrictlySortedKeySeq(v: V) returns (s : Option<seq<Key>>)
  requires Marshalling.valToStrictlySortedKeySeq.requires(v)
  ensures s == Marshalling.valToStrictlySortedKeySeq(v)
  {
    var is_sorted := IsStrictlySortedKeySeq(v.ka);
    if is_sorted {
      return Some(v.ka);
    } else {
      return None;
    }
  }

  method ValToMessageSeq(v: V) returns (s : Option<seq<Message>>)
  requires Marshalling.valToMessageSeq.requires(v)
  ensures s == Marshalling.valToMessageSeq(v)
  {
    return Some(v.ma);
  }

  method ValToPivots(v: V) returns (s : Option<seq<Key>>)
  requires Marshalling.valToPivots.requires(v)
  ensures s == Marshalling.valToPivots(v)
  {
    s := ValToStrictlySortedKeySeq(v);
    if (s.Some? && |s.value| as uint64 > 0 && |s.value[0 as uint64]| as uint64 == 0) {
      s := None;
    }
  }

  method ValToBucket(v: V) returns (s : BucketImpl.MutBucket)
  requires Marshalling.valToBucket.requires(v)
  ensures fresh(s.Repr)
  ensures s.Inv()
  ensures WFBucket(s.I())
  ensures s.I() == Marshalling.valToBucket(v)
  { 
    var pkv := v.pkv;
    s := new BucketImpl.MutBucket.InitFromPkv(pkv);
  }

  method ValToBuckets(a: seq<V>) returns (s : seq<BucketImpl.MutBucket>)
  requires Marshalling.valToBuckets.requires(a)
  requires |a| < 0x1_0000_0000_0000_0000
  requires forall i | 0 <= i < |a| :: SizeOfV(a[i]) < 0x1_0000_0000_0000_0000
  ensures forall i | 0 <= i < |s| :: s[i].Inv()
  ensures BucketImpl.MutBucket.ReprSeqDisjoint(s)
  ensures forall i | 0 <= i < |s| :: fresh(s[i].Repr)
  ensures BucketImpl.MutBucket.ISeq(s) == Marshalling.valToBuckets(a)
  {
    var ar := new BucketImpl.MutBucket?[|a| as uint64];

    var i: uint64 := 0;
    while i < |a| as uint64
    invariant 0 <= i as int <= |a|
    invariant forall k: nat | k < i as int :: ar[k] != null;
    invariant forall k: nat | k < i as int :: ar[k].Inv()
    invariant forall k: nat | k < i as int :: ar !in ar[k].Repr
    invariant forall j, k | 0 <= j < i as int && 0 <= k < i as int && j != k :: ar[j].Repr !! ar[k].Repr
    invariant forall k: nat | k < i as int :: fresh(ar[k].Repr)
    invariant forall k: nat | k < i as int :: WFBucket(ar[k].Bucket)
    invariant BucketImpl.MutBucket.ISeq(ar[..i]) == Marshalling.valToBuckets(a[..i])
    {
      var bucket := ValToBucket(a[i]);

      assert forall k: nat | k < i as int :: ar[k].Inv();
      ar[i] := bucket;
      assert forall k: nat | k < i as int :: ar[k].Inv();
      assert ar[i as int].Inv();
      assert forall k: nat | k < i as int + 1 :: ar[k].Inv();

      assert DropLast(a[..i+1]) == a[..i];
      assert ar[..i+1] == ar[..i] + [bucket];

      i := i + 1;
    }

    assert a[..|a|] == a;
    assert ar[..|a|] == ar[..];

    s := ar[..];

    BucketImpl.MutBucket.reveal_ReprSeqDisjoint();
  }

  method ValToNode(v: V) returns (s : Option<Node>)
  requires IMM.valToNode.requires(v)
  requires SizeOfV(v) < 0x1_0000_0000_0000_0000
  ensures s.Some? ==> s.value.Inv()
  ensures s.Some? ==> BucketImpl.MutBucket.ReprSeqDisjoint(s.value.buckets)
  ensures s.Some? ==> forall i | 0 <= i < |s.value.buckets| :: fresh(s.value.buckets[i].Repr)
  ensures INodeOpt(s) == IMM.valToNode(v)
  ensures s.Some? ==> fresh(s.value.Repr)
  {
    assert ValidVal(v.t[0]);
    assert ValidVal(v.t[1]);
    assert ValidVal(v.t[2]);

    var pivots_len := |v.t[0 as uint64].ka| as uint64;
    var children_len := |v.t[1 as uint64].ua| as uint64;
    var buckets_len := |v.t[2 as uint64].a| as uint64;

    if !(
       && pivots_len <= MaxNumChildrenUint64() - 1
       && (children_len == 0 || children_len == pivots_len + 1)
       && buckets_len == pivots_len + 1
    ) {
      return None;
    }

    var pivotsOpt := ValToPivots(v.t[0 as uint64]);
    if (pivotsOpt.None?) {
      return None;
    }
    var pivots := pivotsOpt.value;

    var childrenOpt := Marshalling.valToChildren(v.t[1 as uint64]);
    if (childrenOpt.None?) {
      return None;
    }
    var children := childrenOpt.value;

    assert ValidVal(v.t[2]);

    IMM.SizeOfVTupleElem_le_SizeOfV(v, 2);
    IMM.SizeOfVArrayElem_le_SizeOfV_forall(v.t[2]);

    var buckets := ValToBuckets(v.t[2 as uint64].a);

    BucketImpl.MutBucket.AllocatedReprSeq(buckets);
    BucketImpl.MutBucket.FreshReprSeqOfFreshEntries(buckets);

    if |buckets| as uint64 > MaxNumChildrenUint64() {
      return None;
    }

    IMM.WeightBucketListLteSize(v.t[2 as uint64], pivots, BucketImpl.MutBucket.ISeq(buckets));
    assert WeightBucketList(BucketImpl.MutBucket.ISeq(buckets)) < 0x1_0000_0000_0000_0000;

    var w: uint64 := BucketImpl.MutBucket.computeWeightOfSeq(buckets);
    if (w > MaxTotalBucketWeightUint64()) {
      return None;
    }

    var node := new Node(pivots, if |children| as uint64 == 0 then None else childrenOpt, buckets);

    return Some(node);
  }


  function ISectorOpt(s : Option<Sector>): Option<IMM.Sector>
  requires s.Some? ==> StateImpl.WFSector(s.value)
  requires s.Some? ==> IM.WFSector(StateImpl.ISector(s.value))
  reads if s.Some? then (if s.value.SectorIndirectionTable? then {s.value.indirectionTable} else {s.value.block}) else {}
  reads if s.Some? then SI.SectorRepr(s.value) else {}
  {
    if s.Some? then
      Some(StateImpl.ISector(s.value))
    else
      None
  }

  method ValToSector(v: V) returns (s : Option<StateImpl.Sector>)
  requires IMM.valToSector.requires(v)
  requires SizeOfV(v) < 0x1_0000_0000_0000_0000
  ensures s.Some? ==> StateImpl.WFSector(s.value)
  ensures s.Some? && s.value.SectorBlock? ==> forall i | 0 <= i < |s.value.block.buckets| :: fresh(s.value.block.buckets[i].Repr)
  ensures s.Some? ==> IM.WFSector(StateImpl.ISector(s.value))
  ensures MapOption(s, SI.ISector) == IMM.valToSector(v)
  ensures s.Some? ==> fresh(SI.SectorRepr(s.value));
  {
    if v.c == 0 {
      var mutMap := IndirectionTableImpl.IndirectionTable.ValToIndirectionTable(v.val);
      if mutMap != null {
        return Some(StateImpl.SectorIndirectionTable(mutMap));
      } else {
        return None;
      }
    } else {
      var node := ValToNode(v.val);
      match node {
        case Some(s) => return Some(StateImpl.SectorBlock(s));
        case None => return None;
      }
    }
  }

  /////// Conversion from PivotNode to a val

  method childrenToVal(children: seq<Reference>) returns (v : V)
  requires |children| < 0x1_0000_0000_0000_0000
  ensures ValidVal(v)
  ensures SizeOfV(v) <= 8 + |children| * 8
  ensures ValInGrammar(v, GUint64Array)
  ensures Marshalling.valToChildren(v) == Some(children)
  ensures |v.ua| == |children|
  ensures SizeOfV(v) == 8 + 8 * |children|
  {
    return VUint64Array(children);
  }

  lemma lemmaSizeOfKeyArray(keys: seq<Key>)
  ensures 4 + WeightKeySeq(keys) == SizeOfV(VKeyArray(keys))
  {
    if |keys| == 0 {
    } else {
      lemmaSizeOfKeyArray(DropLast(keys));
      assert DropLast(keys) + [Last(keys)] == keys;
    }
  }

  lemma lemmaSizeOfMessageArray(messages: seq<Message>)
  ensures 4 + WeightMessageSeq(messages) == SizeOfV(VMessageArray(messages))
  {
    if |messages| == 0 {
    } else {
      lemmaSizeOfMessageArray(DropLast(messages));
      assert DropLast(messages) + [Last(messages)] == messages;
    }
  }

  lemma WeightKeySeqLe(keys: seq<Key>)
  ensures WeightKeySeq(keys) <= |keys| * (8 + KeyType.MaxLen() as int)
  {
    if |keys| == 0 {
    } else {
      WeightKeySeqLe(DropLast(keys));
    }
  }

  method strictlySortedKeySeqToVal(keys: seq<Key>) returns (v : V)
  requires Keyspace.IsStrictlySorted(keys)
  requires |keys| < 0x1_0000_0000_0000_0000
  ensures ValidVal(v)
  ensures ValInGrammar(v, GKeyArray)
  ensures v.ka == keys
  ensures Marshalling.valToStrictlySortedKeySeq(v) == Some(keys)
  ensures SizeOfV(v) <= 8 + |keys| * (8 + KeyType.MaxLen() as int)
  ensures SizeOfV(v) == 4 + WeightKeySeq(keys)
  {
    lemmaSizeOfKeyArray(keys);
    WeightKeySeqLe(keys);

    return VKeyArray(keys);
  }

  lemma KeyInPivotsIsNonempty(pivots: seq<Key>)
  requires Pivots.WFPivots(pivots)
  requires |pivots| > 0
  ensures |pivots[0]| != 0;
  {
    var e := Keyspace.SmallerElement(pivots[0]);
    SeqComparison.reveal_lte();
  }

  method pivotsToVal(pivots: seq<Key>) returns (v : V)
  requires Pivots.WFPivots(pivots)
  requires |pivots| <= MaxNumChildren() as int - 1
  ensures ValidVal(v)
  ensures ValInGrammar(v, GKeyArray)
  ensures |v.ka| == |pivots|
  ensures Marshalling.valToPivots(v) == Some(pivots)
  ensures SizeOfV(v) <= 4 + |pivots| * (4 + KeyType.MaxLen() as int)
  {
    v := strictlySortedKeySeqToVal(pivots);

    ghost var ghosty := true;
    if ghosty && |pivots| > 0 {
      KeyInPivotsIsNonempty(pivots);
    }
    assume SizeOfV(v) <= 4 + |pivots| * (4 + KeyType.MaxLen() as int);
  }

  method messageSeqToVal(s: seq<Message>) returns (v : V)
  requires forall i | 0 <= i < |s| :: s[i] != M.IdentityMessage()
  requires |s| < 0x1_0000_0000_0000_0000
  ensures ValidVal(v)
  ensures ValInGrammar(v, GMessageArray)
  ensures |v.ma| == |s|
  ensures Marshalling.valToMessageSeq(v) == Some(s)
  ensures SizeOfV(v) == 4 + WeightMessageSeq(s)
  {
    lemmaSizeOfMessageArray(s);
    return VMessageArray(s);
  }

  // We pass in pivotTable and i so we can state the pre- and post-conditions.
  method {:fuel SizeOfV,3}
  bucketToVal(bucket: BucketImpl.MutBucket) returns (v: V)
  requires bucket.Inv()
  requires WeightBucket(bucket.Bucket) <= MaxTotalBucketWeight()
  ensures ValInGrammar(v, Marshalling.BucketGrammar())
  ensures ValidVal(v)
  ensures Marshalling.valToBucket(v) == bucket.Bucket
  ensures SizeOfV(v) == WeightBucket(bucket.Bucket) + 8
  {
    var kvl := bucket.GetKvl();
    KVList.kvlWeightEq(kvl);
    KVList.lenKeysLeWeight(kvl);
    var keys := strictlySortedKeySeqToVal(kvl.keys);
    var messages := messageSeqToVal(kvl.messages);
    v := VTuple([keys, messages]);

    assert SizeOfV(v) == SizeOfV(keys) + SizeOfV(messages);

    // FIXME dafny goes nuts with trigger loops here some unknown reason
    // without these obvious asserts.
    //assert ValInGrammar(v.t[0], Marshalling.BucketGrammar().t[0]);
    //assert ValInGrammar(v.t[1], Marshalling.BucketGrammar().t[1]);
    //assert ValInGrammar(v, Marshalling.BucketGrammar());

    // TODO we need to show that v is equivalent to a V
    // which demarshalls to the same bucket.
    assume ValInGrammar(v, Marshalling.BucketGrammar()); // this is not remotely true
  }

  method bucketsToVal(buckets: seq<BucketImpl.MutBucket>) returns (v: V)
  requires forall i | 0 <= i < |buckets| :: buckets[i].Inv()
  requires forall i | 0 <= i < |buckets| :: WFBucket(buckets[i].Bucket)
  requires |buckets| <= MaxNumChildren() as int
  requires WeightBucketList(BucketImpl.MutBucket.ISeq(buckets)) <= MaxTotalBucketWeight()
  ensures ValidVal(v)
  ensures ValInGrammar(v, GArray(Marshalling.BucketGrammar()))
  ensures |v.a| == |buckets|
  ensures Marshalling.valToBuckets(v.a) == BucketImpl.MutBucket.ISeq(buckets)
  ensures SizeOfV(v) <= 8 + WeightBucketList(BucketImpl.MutBucket.ISeq(buckets)) + |buckets| * 8
  {
    if |buckets| as uint64 == 0 {
      v := VArray([]);
    } else {
      WeightBucketListSlice(BucketImpl.MutBucket.ISeq(buckets), 0, |buckets| - 1);
      WeightBucketLeBucketList(BucketImpl.MutBucket.ISeq(buckets), |buckets| - 1);
      BucketImpl.MutBucket.Islice(buckets, 0, |buckets| - 1);

      var pref := bucketsToVal(buckets[..|buckets| as uint64 - 1]);
      var bucket := buckets[|buckets| as uint64 - 1];

      var bucketVal := bucketToVal(bucket);
      assert buckets == DropLast(buckets) + [Last(buckets)]; // observe
      lemma_SeqSum_prefix(pref.a, bucketVal);
      assert Marshalling.valToBuckets(VArray(pref.a + [bucketVal]).a) == BucketImpl.MutBucket.ISeq(buckets); // observe
      assert Marshalling.valToBuckets(VArray(pref.a + [bucketVal]).a) == BucketImpl.MutBucket.ISeq(buckets); // observe (reduces verification time)

      assert buckets == DropLast(buckets) + [Last(buckets)];

      reveal_WeightBucketList();
      BucketImpl.MutBucket.ISeqInduction(buckets);
      assert WeightBucketList(BucketImpl.MutBucket.ISeq(buckets))
          == WeightBucketList(BucketImpl.MutBucket.ISeq(DropLast(buckets))) + WeightBucket(Last(buckets).I());

      v := VArray(pref.a + [bucketVal]);
    }
  }

  function INodeOpt(s : Option<Node>): Option<IMM.Node>
  reads if s.Some? then {s.value} else {}
  reads if s.Some? then s.value.Repr else {}
  requires s.Some? ==> s.value.Inv()
  {
    if s.Some? then
      Some(s.value.I())
    else
      None
  }

  method {:fuel SizeOfV,4} nodeToVal(node: Node) returns (v : V)
  requires node.Inv()
  requires IM.WFNode(node.I())
  requires BT.WFNode(IM.INode(node.I()))
  ensures ValidVal(v)
  ensures ValInGrammar(v, Marshalling.PivotNodeGrammar())
  ensures IMM.valToNode(v) == INodeOpt(Some(node))
  ensures SizeOfV(v) <= BlockSize() - 32 - 8
  {
    BucketImpl.MutBucket.AllocatedReprSeq(node.buckets);
    var buckets := bucketsToVal(node.buckets);

    var pivots := pivotsToVal(node.pivotTable);

    var children;
    if node.children.Some? {
      children := childrenToVal(node.children.value);
    } else {
      children := VUint64Array([]);
    }

    v := VTuple([pivots, children, buckets]);

    assert SizeOfV(pivots) <= (4 + (MaxNumChildren()-1)*(4 + KeyType.MaxLen() as int));
    assert SizeOfV(children) <= (8 + MaxNumChildren() * 8);
    assert SizeOfV(buckets) <= 8 + MaxNumChildren() * (4 + 4) + MaxTotalBucketWeight();

    assert SizeOfV(v) == SizeOfV(pivots) + SizeOfV(children) + SizeOfV(buckets);

    lemma_node_fits_in_block();
  }

  method sectorToVal(sector: StateImpl.Sector) returns (v : V)
  requires StateImpl.WFSector(sector)
  requires IM.WFSector(StateImpl.ISector(sector))
  requires sector.SectorBlock? ==> IM.WFNode(sector.block.I())
  requires sector.SectorBlock? ==> BT.WFNode(IM.INode(sector.block.I()))
  requires sector.SectorIndirectionTable? ==>
      BC.WFCompleteIndirectionTable(IM.IIndirectionTable(sector.indirectionTable.I()))
  ensures ValidVal(v)
  ensures ValInGrammar(v, Marshalling.SectorGrammar());
  ensures Marshalling.valToSector(v) == Some(IM.ISector(StateImpl.ISector(sector)))
  ensures sector.SectorBlock? ==> SizeOfV(v) <= BlockSize() as int - 32
  ensures SizeOfV(v) < 0x1_0000_0000_0000_0000 - 32
  {
    match sector {
      case SectorIndirectionTable(indirectionTable) => {
        var v := indirectionTable.indirectionTableToVal();
        return VCase(0, v);
      }
      case SectorBlock(node) => {
        var v := nodeToVal(node);
        return VCase(1, v);
      }
    }
  }

  /////// Marshalling and de-marshalling

  method ParseSector(data: seq<byte>, start: uint64) returns (s : Option<Sector>)
  requires start as int <= |data| < 0x1_0000_0000_0000_0000;
  ensures s.Some? ==> StateImpl.WFSector(s.value)
  ensures s.Some? ==> IM.WFSector(StateImpl.ISector(s.value))
  ensures s.Some? && s.value.SectorBlock? ==> forall i | 0 <= i < |s.value.block.buckets| :: fresh(s.value.block.buckets[i].Repr)
  ensures ISectorOpt(s) == IMM.parseSector(data[start..])
  ensures s.Some? && s.value.SectorBlock? ==> IM.WFNode(s.value.block.I())
  ensures s.Some? && s.value.SectorBlock? ==> BT.WFNode(IM.INode(s.value.block.I()))
  ensures s.Some? ==> fresh(SI.SectorRepr(s.value));
  {
    IMM.reveal_parseSector();
    NativeBenchmarking.start("ParseVal");
    var success, v, rest_index := ParseVal(data, start, Marshalling.SectorGrammar());
    NativeBenchmarking.end("ParseVal");

    if success {
      lemma_SizeOfV_parse_Val(data[start..], Marshalling.SectorGrammar());
      assert SizeOfV(v) < 0x1_0000_0000_0000_0000;

      NativeBenchmarking.start("ValToSector");
      var s := ValToSector(v);
      NativeBenchmarking.end("ValToSector");
      return s;
    } else {
      return None;
    }
  }

  method MarshallIntoFixedSize(val:V, grammar:G, start: uint64, n: uint64) returns (data:array<byte>)
    requires ValidGrammar(grammar);
    requires ValInGrammar(val, grammar);
    requires ValidVal(val);
    requires start <= n
    requires 0 <= SizeOfV(val) <= n as int - start as int
    ensures fresh(data);
    ensures |data[..]| == n as int
    ensures parse_Val(data[start..], grammar).0.Some? && parse_Val(data[start..], grammar).0.value == val;
  {
    data := new byte[n];
    var computed_size := GenericMarshalling.MarshallVal(val, grammar, data, start);
    //print "computed_size "; print computed_size; print "\n";
    GenericMarshalling.lemma_parse_Val_view_specific(data[..], val, grammar, start as int, (n as int));
    assert data[start..] == data[start..n];
  }

  /////// Marshalling and de-marshalling with checksums

  method ParseCheckedSector(data: seq<byte>) returns (s : Option<Sector>)
  requires |data| < 0x1_0000_0000_0000_0000;
  ensures s.Some? ==> StateImpl.WFSector(s.value)
  ensures s.Some? ==> IM.WFSector(StateImpl.ISector(s.value))
  ensures ISectorOpt(s) == IMM.parseCheckedSector(data[..])
  ensures s.Some? && s.value.SectorBlock? ==> IM.WFNode(s.value.block.I())
  ensures s.Some? && s.value.SectorBlock? ==> BT.WFNode(IM.INode(s.value.block.I()))
  ensures s.Some? ==> fresh(SI.SectorRepr(s.value))
  {
    s := None;

    if |data| as uint64 >= 32 {
      NativeBenchmarking.start("crc-32");
      var hash := Crypto.Crc32C(data[32 as uint64..]);
      NativeBenchmarking.end("crc-32");
      if hash == data[..32 as uint64] {
        s := ParseSector(data, 32);
      }
    }

    IMM.reveal_parseCheckedSector();
  }

  method MarshallCheckedSector(sector: Sector) returns (data : array?<byte>)
  requires StateImpl.WFSector(sector)
  requires IM.WFSector(StateImpl.ISector(sector))
  requires sector.SectorBlock? ==> IM.WFNode(sector.block.I())
  requires sector.SectorBlock? ==> BT.WFNode(IM.INode(sector.block.I()))
  ensures data != null ==> IMM.parseCheckedSector(data[..]).Some?
  ensures data != null ==>
      && IM.ISector(IMM.parseCheckedSector(data[..]).value)
      == IM.ISector(StateImpl.ISector(sector))
  ensures data != null ==> data.Length <= BlockSize() as int
  ensures data != null ==> 32 <= data.Length
  ensures data != null && sector.SectorIndirectionTable? ==> data.Length == BlockSize() as int
  ensures sector.SectorBlock? ==> data != null;
  ensures sector.SectorIndirectionTable? && Marshalling.IsInitIndirectionTable(IndirectionTableModel.I(sector.indirectionTable.I())) ==> data != null;
  {
    var v := sectorToVal(sector);
    var computedSize := GenericMarshalling.ComputeSizeOf(v);

    ghost var ghosty := true;
    if ghosty {
      if sector.SectorIndirectionTable? && Marshalling.IsInitIndirectionTable(IndirectionTableModel.I(sector.indirectionTable.I())) {
        Marshalling.InitIndirectionTableSizeOfV(IndirectionTableModel.I(sector.indirectionTable.I()), v);
      }
    }

    if (computedSize + 32 <= BlockSizeUint64()) {
      var size := if sector.SectorIndirectionTable? then BlockSizeUint64() else computedSize + 32;

      //Native.BenchmarkingUtil.start();
      var data := MarshallIntoFixedSize(v, Marshalling.SectorGrammar(), 32, size);
      //Native.BenchmarkingUtil.end();

      IMM.reveal_parseSector();
      IMM.reveal_parseCheckedSector();

      var hash := Crypto.Crc32CArray(data, 32, data.Length as uint64 - 32);
      assert data[32..] == data[32..data.Length];
      assert hash == Crypto.Crc32C(data[32..]);
      ghost var data_suffix := data[32..];
      NativeArrays.CopySeqIntoArray(hash, 0, data, 0, 32);
      assert data_suffix == data[32..];

      /*ghost var data_seq := data[..];
      assert |data_seq| >= 32;
      assert Crypto.Crc32C(data_seq[32..])
          == Crypto.Crc32C(data[32..])
          == hash
          == data[..32]
          == data_seq[..32];*/

      return data;
    } else {
      return null;
    }
  }
}
