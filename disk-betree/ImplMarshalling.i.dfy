include "../lib/Marshalling/GenericMarshalling.i.dfy"
include "ImplState.i.dfy"
include "ImplModel.i.dfy"
include "MutableBucket.i.dfy"
include "../lib/Base/Option.s.dfy"
include "../lib/Base/NativeArrays.s.dfy"

include "Marshalling.i.dfy"
include "ImplMarshallingModel.i.dfy"

module ImplMarshalling {
  import IM = ImplModel
  import IS = ImplState
  import opened ImplNode
  import opened ImplMutCache
  import Marshalling
  import IMM = ImplMarshallingModel
  import opened GenericMarshalling
  import opened Options
  import opened NativeTypes
  import opened Sequences
  import opened Maps
  import opened Sets
  import opened BucketsLib
  import opened BucketWeights
  import opened Bounds
  import MutableBucket
  import BC = BetreeGraphBlockCache
  import ImplState
  import KVList
  import Crypto
  import NativeArrays
  import MutableMapModel
  import IndirectionTableImpl
  import KeyType

  import BT = PivotBetreeSpec`Internal

  import ValueWithDefault`Internal
  import M = ValueMessage`Internal
  import LBAType

  import Pivots = PivotsLib
  import MS = MapSpec
  import Keyspace = Lexicographic_Byte_Order

  import MM = MutableMap

  type Reference = IMM.Reference
  type LBA = IMM.LBA
  type Location = IMM.Location
  type Sector = IS.Sector

  /////// Conversion to PivotNode

  method IsStrictlySortedKeySeq(a: seq<Key>) returns (b : bool)
  requires |a| < 0x1_0000_0000_0000_0000
  ensures b == IMM.isStrictlySortedKeySeq(a)
  {
    IMM.reveal_isStrictlySortedKeySeq();

    if |a| as uint64 < 2 {
      return true;
    }
    var i: uint64 := 1;
    while i < |a| as uint64
    invariant 0 <= i as int <= |a|
    invariant IMM.isStrictlySortedKeySeq(a) == IMM.isStrictlySortedKeySeqIterate(a, i as int)
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
  requires IMM.valToStrictlySortedKeySeq.requires(v)
  ensures s == IMM.valToStrictlySortedKeySeq(v)
  {
    var is_sorted := IsStrictlySortedKeySeq(v.baa);
    if is_sorted {
      return Some(v.baa);
    } else {
      return None;
    }
  }

  method ValToMessageSeq(v: V) returns (s : Option<seq<Message>>)
  requires IMM.valToMessageSeq.requires(v)
  ensures s == IMM.valToMessageSeq(v)
  {
    return Some(v.ma);
  }

  method ValToPivots(v: V) returns (s : Option<seq<Key>>)
  requires IMM.valToPivots.requires(v)
  ensures s == IMM.valToPivots(v)
  {
    s := ValToStrictlySortedKeySeq(v);
    if (s.Some? && |s.value| as uint64 > 0 && |s.value[0 as uint64]| as uint64 == 0) {
      s := None;
    }
  }

  method ValToBucket(v: V, pivotTable: seq<Key>, i: uint64) returns (s : Option<KVList.Kvl>)
  requires IMM.valToBucket.requires(v, pivotTable, i as int)
  ensures s.Some? ==> KVList.WF(s.value)
  ensures s.Some? ==> WFBucketAt(KVList.I(s.value), pivotTable, i as int)
  ensures s == IMM.valToBucket(v, pivotTable, i as int)
  {
    assert ValidVal(v.t[0]);

    var keys := ValToStrictlySortedKeySeq(v.t[0 as uint64]);

    if keys.None? {
      return None;
    }

    var values := ValToMessageSeq(v.t[1 as uint64]);

    if values.None? {
      return None;
    }

    var kvl := KVList.Kvl(keys.value, values.value);

    var wf := KVList.IsWF(kvl);
    if !wf {
      return None;
    }

    // Check that the keys fit in the desired bucket
    if |kvl.keys| as uint64 > 0 {
      if i > 0 {
        var c := Keyspace.cmp(pivotTable[i-1], kvl.keys[0 as uint64]);
        if (c > 0) {
          KVList.Imaps(kvl, 0);
          return None;
        }
      }

      assume |pivotTable| < 0x1_0000_0000_0000_0000;

      if i < |pivotTable| as uint64 {
        var c := Keyspace.cmp(pivotTable[i], kvl.keys[|kvl.keys| as uint64 - 1]);
        if (c <= 0) {
          KVList.Imaps(kvl, |kvl.keys| - 1);
          return None;
        }
      }
    }

    forall key | key in KVList.I(kvl)
    ensures Pivots.Route(pivotTable, key) == i as int
    ensures KVList.I(kvl)[key] != M.IdentityMessage()
    {
      var j := KVList.IndexOfKey(kvl, key);
      KVList  .Imaps(kvl, j);
      if |kvl.keys| > 0 {
        Keyspace.IsStrictlySortedImpliesLte(kvl.keys, 0, j);
        Keyspace.IsStrictlySortedImpliesLte(kvl.keys, j, |kvl.keys| - 1);
      }
      Pivots.RouteIs(pivotTable, key, i as int);
    }

    assert WFBucketAt(KVList.I(kvl), pivotTable, i as int);

    s := Some(kvl);
  }

  lemma LemmaValToBucketNone(a: seq<V>, pivotTable: seq<Key>, i: int)
  requires Pivots.WFPivots(pivotTable)
  requires forall i | 0 <= i < |a| :: ValidVal(a[i])
  requires forall i | 0 <= i < |a| :: ValInGrammar(a[i], IMM.BucketGrammar())
  requires |a| <= |pivotTable| + 1
  requires 0 <= i < |a|
  requires IMM.valToBucket(a[i], pivotTable, i) == None
  ensures IMM.valToBuckets(a, pivotTable) == None
  {
    if (|a| == i + 1) {
    } else {
      LemmaValToBucketNone(DropLast(a), pivotTable, i);
    }
  }

  method ValToBuckets(a: seq<V>, pivotTable: seq<Key>) returns (s : Option<seq<MutableBucket.MutBucket>>)
  requires IMM.valToBuckets.requires(a, pivotTable)
  ensures s.Some? ==> forall i | 0 <= i < |s.value| :: s.value[i].Inv()
  ensures s.Some? ==> MutableBucket.MutBucket.ReprSeqDisjoint(s.value)
  ensures s.Some? ==> forall i | 0 <= i < |s.value| :: fresh(s.value[i].Repr)
  ensures s.None? ==> IMM.valToBuckets(a, pivotTable) == None
  ensures s.Some? ==> Some(MutableBucket.MutBucket.ISeq(s.value)) == IMM.valToBuckets(a, pivotTable)
  {
    assume |a| < 0x1_0000_0000_0000_0000;

    var ar := new MutableBucket.MutBucket?[|a| as uint64];

    var i: uint64 := 0;
    while i < |a| as uint64
    invariant 0 <= i as int <= |a|
    invariant forall k: nat | k < i as int :: ar[k] != null;
    invariant forall k: nat | k < i as int :: ar[k].Inv()
    invariant forall k: nat | k < i as int :: ar !in ar[k].Repr
    invariant forall j, k | 0 <= j < i as int && 0 <= k < i as int && j != k :: ar[j].Repr !! ar[k].Repr
    invariant forall k: nat | k < i as int :: fresh(ar[k].Repr)
    invariant forall k: nat | k < i as int :: WFBucketAt(ar[k].Bucket, pivotTable, k)
    invariant IMM.valToBuckets(a[..i], pivotTable).Some?
    invariant MutableBucket.MutBucket.ISeq(ar[..i]) == IMM.valToBuckets(a[..i], pivotTable).value
    {
      var b := ValToBucket(a[i], pivotTable, i);
      if (b.None?) {
        s := None;

        LemmaValToBucketNone(a, pivotTable, i as int);
        return;
      }

      assume WeightBucket(KVList.I(b.value)) < 0x1_0000_0000_0000_0000;
      var bucket := new MutableBucket.MutBucket(b.value);
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

    s := Some(ar[..]);

    MutableBucket.MutBucket.reveal_ReprSeqDisjoint();
  }

  method ValToNode(v: V) returns (s : Option<Node>)
  requires IMM.valToNode.requires(v)
  ensures s.Some? ==> s.value.Inv()
  ensures s.Some? ==> MutableBucket.MutBucket.ReprSeqDisjoint(s.value.buckets)
  ensures s.Some? ==> forall i | 0 <= i < |s.value.buckets| :: fresh(s.value.buckets[i].Repr)
  ensures INodeOpt(s) == IMM.valToNode(v)
  {
    assert ValidVal(v.t[0]);
    var pivotsOpt := ValToPivots(v.t[0 as uint64]);
    if (pivotsOpt.None?) {
      return None;
    }
    var pivots := pivotsOpt.value;

    var childrenOpt := IMM.valToChildren(v.t[1 as uint64]);
    if (childrenOpt.None?) {
      return None;
    }
    var children := childrenOpt.value;

    assume |children| < 0x8000_0000_0000_0000;
    assume |pivots| < 0x8000_0000_0000_0000;
    assume |v.t[2 as uint64].a| < 0x1_0000_0000_0000_0000;

    if (!((|children| as uint64 == 0 || |children| as uint64 == |pivots| as uint64 + 1) && |v.t[2 as uint64].a| as uint64 == |pivots| as uint64 + 1)) {
      return None;
    }

    assert ValidVal(v.t[2]);
    var bucketsOpt := ValToBuckets(v.t[2 as uint64].a, pivots);
    if (bucketsOpt.None?) {
      return None;
    }
    var buckets := bucketsOpt.value;

    assume forall o | o in MutableBucket.MutBucket.ReprSeq(buckets) :: allocated(o);

    if |buckets| as uint64 > MaxNumChildrenUint64() {
      return None;
    }

    assume WeightBucketList(MutableBucket.MutBucket.ISeq(buckets)) < 0x1_0000_0000_0000_0000; // TODO we should be able to prove this using the fact that it was deserialized:
    var w: uint64 := MutableBucket.MutBucket.computeWeightOfSeq(buckets);
    if (w > MaxTotalBucketWeightUint64()) {
      return None;
    }

    var node := new Node(pivots, if |children| as uint64 == 0 then None else childrenOpt, buckets);

    return Some(node);
  }


  function ISectorOpt(s : Option<Sector>): Option<IMM.Sector>
  requires s.Some? ==> ImplState.WFSector(s.value)
  requires s.Some? ==> IM.WFSector(ImplState.ISector(s.value))
  reads if s.Some? then (if s.value.SectorIndirectionTable? then {s.value.indirectionTable} else {s.value.block}) else {}
  reads if s.Some? then IS.SectorRepr(s.value) else {}
  {
    if s.Some? then
      Some(ImplState.ISector(s.value))
    else
      None
  }

  method ValToSector(v: V) returns (s : Option<ImplState.Sector>)
  requires IMM.valToSector.requires(v)
  ensures s.Some? ==> ImplState.WFSector(s.value)
  ensures s.Some? && s.value.SectorBlock? ==> forall i | 0 <= i < |s.value.block.buckets| :: fresh(s.value.block.buckets[i].Repr)
  ensures s.Some? ==> IM.WFSector(ImplState.ISector(s.value))
  ensures MapOption(s, IS.ISector) == IMM.valToSector(v)
  {
    if v.c == 0 {
      var mutMap := IndirectionTableImpl.IndirectionTable.ValToIndirectionTable(v.val);
      if mutMap != null {
        return Some(ImplState.SectorIndirectionTable(mutMap));
      } else {
        return None;
      }
    } else {
      var node := ValToNode(v.val);
      match node {
        case Some(s) => return Some(ImplState.SectorBlock(s));
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
  ensures IMM.valToChildren(v) == Some(children)
  ensures |v.ua| == |children|
  ensures SizeOfV(v) == 8 + 8 * |children|
  {
    return VUint64Array(children);
  }

  method {:fuel ValidVal,2} uint64ArrayToVal(a: seq<uint64>) returns (v: V)
  requires |a| < 0x1_0000_0000_0000_0000
  ensures ValidVal(v)
  ensures ValInGrammar(v, GUint64Array)
  ensures SizeOfV(v) == 8 + 8 * |a|
  ensures |v.ua| == |a|
  ensures IMM.valToUint64Seq(v) == a
  {
    return VUint64Array(a);
  }

  lemma lemmaSizeOfKeyArray(keys: seq<Key>)
  ensures 8 + WeightKeySeq(keys) == SizeOfV(VKeyArray(keys))

  lemma lemmaSizeOfMessageArray(messages: seq<Message>)
  ensures 8 + WeightMessageSeq(messages) == SizeOfV(VMessageArray(messages))

  lemma WeightKeySeqLe(keys: seq<Key>)
  ensures WeightKeySeq(keys) <= |keys| * (8 + KeyType.MaxLen() as int)

  method strictlySortedKeySeqToVal(keys: seq<Key>) returns (v : V)
  requires Keyspace.IsStrictlySorted(keys)
  requires |keys| < 0x1_0000_0000_0000_0000
  ensures ValidVal(v)
  ensures ValInGrammar(v, GKeyArray)
  ensures v.baa == keys
  ensures IMM.valToStrictlySortedKeySeq(v) == Some(keys)
  ensures SizeOfV(v) <= 8 + |keys| * (8 + KeyType.MaxLen() as int)
  ensures SizeOfV(v) == 8 + WeightKeySeq(keys)
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
    Keyspace.reveal_seq_lte();
  }

  method pivotsToVal(pivots: seq<Key>) returns (v : V)
  requires Pivots.WFPivots(pivots)
  requires |pivots| <= MaxNumChildren() as int - 1
  ensures ValidVal(v)
  ensures ValInGrammar(v, GKeyArray)
  ensures |v.baa| == |pivots|
  ensures IMM.valToPivots(v) == Some(pivots)
  ensures SizeOfV(v) <= 8 + |pivots| * (8 + KeyType.MaxLen() as int)
  {
    v := strictlySortedKeySeqToVal(pivots);

    ghost var ghosty := true;
    if ghosty && |pivots| > 0 {
      KeyInPivotsIsNonempty(pivots);
    }
  }

  method messageSeqToVal(s: seq<Message>) returns (v : V)
  requires forall i | 0 <= i < |s| :: s[i] != M.IdentityMessage()
  requires |s| < 0x1_0000_0000_0000_0000
  ensures ValidVal(v)
  ensures ValInGrammar(v, GMessageArray)
  ensures |v.ma| == |s|
  ensures IMM.valToMessageSeq(v) == Some(s)
  ensures SizeOfV(v) == 8 + WeightMessageSeq(s)
  {
    lemmaSizeOfMessageArray(s);
    return VMessageArray(s);
  }

  // We pass in pivotTable and i so we can state the pre- and post-conditions.
  method {:fuel SizeOfV,3}
  bucketToVal(bucket: MutableBucket.MutBucket, ghost pivotTable: Pivots.PivotTable, ghost i: int) returns (v: V)
  requires Pivots.WFPivots(pivotTable)
  requires bucket.Inv()
  requires WeightBucket(bucket.Bucket) <= MaxTotalBucketWeight()
  requires WFBucketAt(bucket.Bucket, pivotTable, i)
  requires 0 <= i <= |pivotTable|
  ensures ValInGrammar(v, IMM.BucketGrammar())
  ensures ValidVal(v)
  ensures IMM.valToBucket(v, pivotTable, i).Some?;
  ensures KVList.I(IMM.valToBucket(v, pivotTable, i).value) == bucket.Bucket
  ensures SizeOfV(v) == WeightBucket(bucket.Bucket) + 16
  {
    var kvl := bucket.GetKvl();
    KVList.kvlWeightEq(kvl);
    KVList.lenKeysLeWeight(kvl);
    var keys := strictlySortedKeySeqToVal(kvl.keys);
    var values := messageSeqToVal(kvl.values);
    v := VTuple([keys, values]);

    assert SizeOfV(v) == SizeOfV(keys) + SizeOfV(values);

    // FIXME dafny goes nuts with trigger loops here some unknown reason
    // without these obvious asserts.
    assert ValInGrammar(v.t[0], IMM.BucketGrammar().t[0]);
    assert ValInGrammar(v.t[1], IMM.BucketGrammar().t[1]);
    assert ValInGrammar(v, IMM.BucketGrammar());
  }

  method bucketsToVal(buckets: seq<MutableBucket.MutBucket>, ghost pivotTable: Pivots.PivotTable) returns (v: V)
  requires Pivots.WFPivots(pivotTable)
  requires forall i | 0 <= i < |buckets| :: buckets[i].Inv()
  requires forall i | 0 <= i < |buckets| :: WFBucketAt(buckets[i].Bucket, pivotTable, i)
  requires |buckets| <= MaxNumChildren() as int
  requires |buckets| <= |pivotTable| + 1
  requires WeightBucketList(MutableBucket.MutBucket.ISeq(buckets)) <= MaxTotalBucketWeight()
  ensures ValidVal(v)
  ensures ValInGrammar(v, GArray(IMM.BucketGrammar()))
  ensures |v.a| == |buckets|
  ensures IMM.valToBuckets(v.a, pivotTable) == Some(MutableBucket.MutBucket.ISeq(buckets))
  ensures SizeOfV(v) <= 8 + WeightBucketList(MutableBucket.MutBucket.ISeq(buckets)) + |buckets| * 16
  {
    if |buckets| as uint64 == 0 {
      v := VArray([]);
    } else {
      WeightBucketListSlice(MutableBucket.MutBucket.ISeq(buckets), 0, |buckets| - 1);
      WeightBucketLeBucketList(MutableBucket.MutBucket.ISeq(buckets), |buckets| - 1);
      MutableBucket.MutBucket.Islice(buckets, 0, |buckets| - 1);

      var pref := bucketsToVal(buckets[..|buckets| as uint64 - 1], pivotTable);
      var bucket := buckets[|buckets| as uint64 - 1];

      var bucketVal := bucketToVal(bucket, pivotTable, |buckets| - 1);
      assert buckets == DropLast(buckets) + [Last(buckets)]; // observe
      lemma_SeqSum_prefix(pref.a, bucketVal);
      assert IMM.valToBuckets(VArray(pref.a + [bucketVal]).a, pivotTable).Some?; // observe
      assert IMM.valToBuckets(VArray(pref.a + [bucketVal]).a, pivotTable).value == MutableBucket.MutBucket.ISeq(buckets); // observe
      assert IMM.valToBuckets(VArray(pref.a + [bucketVal]).a, pivotTable) == Some(MutableBucket.MutBucket.ISeq(buckets)); // observe (reduces verification time)

      assert buckets == DropLast(buckets) + [Last(buckets)];

      reveal_WeightBucketList();
      MutableBucket.MutBucket.ISeqInduction(buckets);
      assert WeightBucketList(MutableBucket.MutBucket.ISeq(buckets))
          == WeightBucketList(MutableBucket.MutBucket.ISeq(DropLast(buckets))) + WeightBucket(MutableBucket.MutBucket.I(Last(buckets)));

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
  ensures ValInGrammar(v, IMM.PivotNodeGrammar())
  ensures IMM.valToNode(v) == INodeOpt(Some(node))
  ensures SizeOfV(v) <= BlockSize() - 32 - 8
  {
    assume forall o | o in MutableBucket.MutBucket.ReprSeq(node.buckets) :: allocated(o);
    var buckets := bucketsToVal(node.buckets, node.pivotTable);

    var pivots := pivotsToVal(node.pivotTable);

    var children;
    if node.children.Some? {
      children := childrenToVal(node.children.value);
    } else {
      children := VUint64Array([]);
    }

    v := VTuple([pivots, children, buckets]);

    assert SizeOfV(pivots) <= 320000;
    assert SizeOfV(children) <= 264;
    assert SizeOfV(buckets) <= 8068312;

    assert SizeOfV(v) == SizeOfV(pivots) + SizeOfV(children) + SizeOfV(buckets);
    //assert IMM.valToNode(v).Some?;
    //assert IMM.valToNode(v).value == node.I();
  }

  method sectorToVal(sector: ImplState.Sector) returns (v : Option<V>)
  requires ImplState.WFSector(sector)
  requires IM.WFSector(ImplState.ISector(sector))
  requires sector.SectorBlock? ==> IM.WFNode(sector.block.I())
  requires sector.SectorBlock? ==> BT.WFNode(IM.INode(sector.block.I()))
  requires sector.SectorIndirectionTable? ==>
      BC.WFCompleteIndirectionTable(IM.IIndirectionTable(sector.indirectionTable.I()))
  ensures v.Some? ==> ValidVal(v.value)
  ensures v.Some? ==> ValInGrammar(v.value, IMM.SectorGrammar());
  ensures v.Some? ==> Marshalling.valToSector(v.value) == Some(IM.ISector(ImplState.ISector(sector)))
  ensures sector.SectorBlock? ==> v.Some?
  ensures sector.SectorBlock? ==> SizeOfV(v.value) <= BlockSize() as int - 32
  ensures v.Some? ==> SizeOfV(v.value) < 0x1_0000_0000_0000_0000 - 32
  {
    match sector {
      case SectorIndirectionTable(indirectionTable) => {
        var v := indirectionTable.indirectionTableToVal();
        if v.Some? {
          return Some(VCase(0, v.value));
        } else {
          return None;
        }
      }
      case SectorBlock(node) => {
        var v := nodeToVal(node);
        return Some(VCase(1, v));
      }
    }
  }

  /////// Marshalling and de-marshalling

  method ParseSector(data: seq<byte>, start: uint64) returns (s : Option<Sector>)
  requires start as int <= |data| < 0x1_0000_0000_0000_0000;
  ensures s.Some? ==> ImplState.WFSector(s.value)
  ensures s.Some? ==> IM.WFSector(ImplState.ISector(s.value))
  ensures s.Some? && s.value.SectorBlock? ==> forall i | 0 <= i < |s.value.block.buckets| :: fresh(s.value.block.buckets[i].Repr)
  ensures ISectorOpt(s) == IMM.parseSector(data[start..])
  ensures s.Some? && s.value.SectorBlock? ==> IM.WFNode(s.value.block.I())
  ensures s.Some? && s.value.SectorBlock? ==> BT.WFNode(IM.INode(s.value.block.I()))
  {
    IMM.reveal_parseSector();
    var success, v, rest_index := ParseVal(data, start, IMM.SectorGrammar());
    if success {
      var s := ValToSector(v);
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
  ensures s.Some? ==> ImplState.WFSector(s.value)
  ensures s.Some? ==> IM.WFSector(ImplState.ISector(s.value))
  ensures ISectorOpt(s) == IMM.parseCheckedSector(data[..])
  ensures s.Some? && s.value.SectorBlock? ==> IM.WFNode(s.value.block.I())
  ensures s.Some? && s.value.SectorBlock? ==> BT.WFNode(IM.INode(s.value.block.I()))
  ensures s.Some? ==> fresh(IS.SectorRepr(s.value))
  {
    s := None;

    if |data| as uint64 >= 32 {
      var hash := Crypto.Crc32C(data[32 as uint64..]);
      if hash == data[..32 as uint64] {
        s := ParseSector(data, 32);
      }
    }

    IMM.reveal_parseCheckedSector();

    assume s.Some? ==> fresh(IS.SectorRepr(s.value));
  }

  method MarshallCheckedSector(sector: Sector) returns (data : array?<byte>)
  requires ImplState.WFSector(sector)
  requires IM.WFSector(ImplState.ISector(sector))
  requires sector.SectorBlock? ==> IM.WFNode(sector.block.I())
  requires sector.SectorBlock? ==> BT.WFNode(IM.INode(sector.block.I()))
  ensures data != null ==> IMM.parseCheckedSector(data[..]).Some?
  ensures data != null ==>
      && IM.ISector(IMM.parseCheckedSector(data[..]).value)
      == IM.ISector(ImplState.ISector(sector))
  ensures data != null ==> data.Length <= BlockSize() as int
  ensures data != null ==> 32 <= data.Length
  ensures data != null && sector.SectorIndirectionTable? ==> data.Length == BlockSize() as int
  ensures sector.SectorBlock? ==> data != null;
  {
    var v := sectorToVal(sector);
    match v {
      case None => return null;
      case Some(v) => {
        var computedSize := GenericMarshalling.ComputeSizeOf(v);

        if (computedSize + 32 <= BlockSizeUint64()) {
          var size := if sector.SectorIndirectionTable? then BlockSizeUint64() else computedSize + 32;

          //Native.BenchmarkingUtil.start();
          var data := MarshallIntoFixedSize(v, IMM.SectorGrammar(), 32, size);
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
  }
}
