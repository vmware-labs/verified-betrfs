include "../lib/Marshalling/GenericMarshalling.i.dfy"
include "StateSectorImpl.i.dfy"
include "../lib/Buckets/BucketImpl.i.dfy"
include "../lib/Base/Option.s.dfy"
include "../lib/Lang/System/NativeArrays.s.dfy"
include "../lib/Base/NativeBenchmarking.s.dfy"
include "../lib/Base/LinearOption.i.dfy"
include "../lib/Crypto/CRC32CArrayImpl.i.dfy"
include "../lib/Crypto/CRC32CImpl.i.dfy"

include "../ByteBlockCacheSystem/Marshalling.i.dfy"
include "MarshallingModel.i.dfy"
include "CacheImpl.i.dfy"

module MarshallingImpl {
  import SSM = StateSectorModel
  import SSI = StateSectorImpl
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
  import SectorType
  import BucketImpl
  import BC = BlockCache
  import JC = JournalCache

  import CRC32_C
  import CRC32_C_Impl
  import CRC32_C_Array_Impl
  import NativeArrays
  import MutableMapModel
  import IndirectionTable
  import KeyType
  import SeqComparison
  import NativeBenchmarking
  import opened NativePackedInts
  import opened LinearOption
  import opened LinearSequence_s
  import opened LinearSequence_i

  import BT = PivotBetreeSpec`Internal

  import ValueType`Internal
  import M = ValueMessage`Internal

  import Pivots = BoundedPivotsLib
  import MS = MapSpec

  import PackedKVMarshalling
  import PackedKV
  import DPKV = DynamicPkv
  import PSA = PackedStringArray
  import PSAM = PackedStringArrayMarshalling

  type Key = KeyType.Key
  type Reference = IMM.Reference
  type Sector = SSI.Sector

  /////// Conversion to PivotNode

  method IsStrictlySortedPivots(pivots: Pivots.PivotTable) returns (b : bool)
  requires |pivots| < 0x1_0000_0000_0000_0000
  ensures b == Marshalling.isStrictlySortedPivots(pivots)
  {
    Marshalling.reveal_isStrictlySortedPivots();

    if |pivots| as uint64 < 2 {
      return true;
    }
    var i: uint64 := 1;
    while i < |pivots| as uint64
    invariant 0 <= i as int <= |pivots|
    invariant Marshalling.isStrictlySortedPivots(pivots) 
      == Marshalling.isStrictlySortedPivotsIterate(pivots, i as int)
    {
      var c := Pivots.KeyspaceImpl.cmp(pivots[i-1], pivots[i]);
      if c >= 0 {
        return false;
      }
      i := i + 1;
    }

    return true;
  }

  method KeyValSeqToPivots(vs: seq<V>) returns (result: Option<Pivots.PivotTable>)
    requires |vs| < Uint64UpperBound()
    requires forall i | 0 <= i < |vs| :: ValidVal(vs[i])
    requires forall i | 0 <= i < |vs| :: ValInGrammar(vs[i], GByteArray)
    ensures result == Marshalling.keyValSeqToPivots(vs)
  {
    var aresult: array<Pivots.Element> := new Pivots.Element[|vs| as uint64];

    var i: uint64 := 0;
    while i < |vs| as uint64
      invariant i as nat <= |vs|
      invariant Marshalling.keyValSeqToPivots(vs[..i]).Some?
      invariant aresult[..i] == Marshalling.keyValSeqToPivots(vs[..i]).value
    {
      if KeyType.MaxLen() < |vs[i].b| as uint64 {
        return None;
      }
      aresult[i] := Marshalling.keyToPivot(vs[i].b, i >= 1);
      i := i + 1;
    }
    assert vs[..i] == vs;
    return Some(aresult[..i]);
  }
  
  method valToStrictlySortedPivots(v: V) returns (s : Option<Pivots.PivotTable>)
  requires Marshalling.valToStrictlySortedPivots.requires(v)
  ensures s == Marshalling.valToStrictlySortedPivots(v)
  {
    var okeys := KeyValSeqToPivots(v.a);
    if okeys.Some? {
      var is_sorted := IsStrictlySortedPivots(okeys.value);
      if is_sorted {
        return okeys;
      }
    }
    return None;
  }

  method ValToPivots(v: V) returns (s : Option<Pivots.PivotTable>)
  requires Marshalling.valToPivots.requires(v)
  ensures s == Marshalling.valToPivots(v)
  {
    if |v.a| >= 2 {
      s := valToStrictlySortedPivots(v);
    } else {
      s := None;
    }
  }

  method ValToBucket(v: V) returns (linear s : lOption<BucketImpl.MutBucket>)
    requires Marshalling.valToBucket.requires(v)
    ensures s.lSome? <==> Marshalling.valToBucket(v).Some?
    ensures s.lSome? ==> s.value.Inv()
    ensures s.lSome? ==> WFBucket(s.value.I())
    ensures s.lSome? ==> Some(s.value.I()) == Marshalling.valToBucket(v)
  { 
    var pkv := PackedKVMarshalling.FromVal(v);
    if pkv.Some? && PackedKV.WeightPkv(pkv.value) < 0x1_0000_0000 {
      linear var b := BucketImpl.MutBucket.AllocPkv(pkv.value, false);
      s := lSome(b);
    } else {
      s := lNone;
    }
  }

  method ValToBuckets(a: seq<V>) returns (linear s : lOption<lseq<BucketImpl.MutBucket>>)
  requires Marshalling.valToBuckets.requires(a)
  requires |a| < 0x1_0000_0000_0000_0000
  requires forall i | 0 <= i < |a| :: SizeOfV(a[i]) < 0x1_0000_0000_0000_0000
  ensures s.lSome? ==> lseq_has_all(s.value)
  ensures s.lSome? ==> forall i | 0 <= i < |s.value| :: s.value[i].Inv()
  ensures s.lSome? ==> Some(BucketImpl.MutBucket.ILseq(s.value)) == Marshalling.valToBuckets(a)
  ensures s == lNone <==> Marshalling.valToBuckets(a) == None
  {
    linear var buckets : lseq<BucketImpl.MutBucket> := lseq_alloc(|a| as uint64);

    var error := false;
    var i: uint64 := 0;
    while i < |a| as uint64
    invariant 0 <= i as nat <= |a|
    invariant |a| == |buckets|
    invariant !error ==> forall k: nat | k < i as nat :: lseq_has(buckets)[k]
    invariant !error ==> forall k: nat | i as nat <= k < |a| :: !lseq_has(buckets)[k]
    invariant !error ==> forall k: nat | k < i as nat :: buckets[k].Inv()
    invariant !error ==> forall k: nat | k < i as nat :: WFBucket(buckets[k].bucket)
    invariant !error ==> Some(BucketImpl.MutBucket.ISeq(lseqs(buckets)[..i])) 
      == Marshalling.valToBuckets(a[..i])
    invariant error ==> forall k: nat | k < |a| :: !lseq_has(buckets)[k]
    invariant error ==>  Marshalling.valToBuckets(a) == None
    invariant error ==> i as nat == |a|
    {
      assert error == false;
      linear var obucket := ValToBucket(a[i]);
      linear match obucket {
        case lSome(bucket) =>
          lseq_give_inout(inout buckets, i, bucket);
          assert buckets[i as int].Inv();
          assert forall k: nat | k < i as nat + 1 :: buckets[k].Inv();          
          assert DropLast(a[..i+1]) == a[..i];
          assert lseqs(buckets)[..i+1] == lseqs(buckets)[..i] + [bucket];

          i := i + 1;
          assert BucketImpl.MutBucket.ISeq(lseqs(buckets)[..i]) 
            == Marshalling.valToBuckets(a[..i]).value;
        case lNone =>
          assert Marshalling.valToBuckets(a) == None;
          var j: uint64 := 0;
          while j < i as uint64
          invariant 0 <= j as int <= i as int < |a|
          invariant |a| == |buckets|
          invariant forall k: nat | i as nat <= k < |a| :: !lseq_has(buckets)[k]
          invariant forall k: nat | k < j as int :: !lseq_has(buckets)[k]
          invariant forall k: nat | j as int <= k < i as int :: lseq_has(buckets)[k]
          invariant forall k: nat | j as int <= k < i as int :: buckets[k].Inv()
          invariant forall k: nat | j as int <= k < i as int :: WFBucket(buckets[k].bucket)
          {
            assert forall k: nat | j as int <= k < i as int :: buckets[k].Inv();
            ghost var bucketsSeq := lseqs(buckets);
            ghost var takenB := bucketsSeq[j as nat];
            linear var b := lseq_take_inout(inout buckets, j);
            assert b == takenB;
            var _ := BucketImpl.FreeMutBucket(b);
            j := j + 1;
          }
          error := true;
          i := |a| as uint64;
      }
    }

    if error {
      lseq_free(buckets);
      s := lNone;
    } else {
      assert i as nat == |a|;
      assert a[..|a|] == a;
      assert lseqs(buckets)[..|a|] == lseqs(buckets)[..];
      s := lSome(buckets);
    }
  }

  method ValToNode(v: V) returns (linear s : lOption<Node>)
  requires IMM.valToNode.requires(v)
  requires SizeOfV(v) < 0x1_0000_0000_0000_0000
  ensures s.lSome? ==> s.value.Inv()
  ensures INodeOpt(s.Option()) == IMM.valToNode(v)
  {
    assert ValidVal(v.t[0]);
    assert ValidVal(v.t[1]);
    assert ValidVal(v.t[2]);

    var pivots_len := |v.t[0 as uint64].a| as uint64;
    var children_len := |v.t[1 as uint64].ua| as uint64;
    var buckets_len := |v.t[2 as uint64].a| as uint64;

    if (
       && 2 <= pivots_len <= MaxNumChildrenUint64() + 1
       && (children_len == 0 || children_len == pivots_len - 1)
       && buckets_len == pivots_len - 1
    ) {
      var pivotsOpt := ValToPivots(v.t[0 as uint64]);
      if (pivotsOpt.Some?) {
        var pivots := pivotsOpt.value;
        var childrenOpt := Marshalling.valToChildren(v.t[1 as uint64]);
        if (childrenOpt.Some?) {
          var children := childrenOpt.value;
          assert ValidVal(v.t[2]);

          IMM.SizeOfVTupleElem_le_SizeOfV(v, 2);
          IMM.SizeOfVArrayElem_le_SizeOfV_forall(v.t[2]);

          if |v.t[2 as uint64].a| as uint64 <= MaxNumChildrenUint64() {
            linear var obuckets := ValToBuckets(v.t[2 as uint64].a);
            linear match obuckets {
              case lSome(buckets) =>
                assert |buckets| as uint64 <= MaxNumChildrenUint64();
                IMM.WeightBucketListLteSize(v.t[2 as uint64], 
                  BucketImpl.MutBucket.ILseq(buckets));
                assert WeightBucketList(BucketImpl.MutBucket.ILseq(buckets)) 
                  < 0x1_0000_0000_0000_0000;

                var w: uint64 := BucketImpl.MutBucket.computeWeightOfSeq(buckets);
                if (w > MaxTotalBucketWeightUint64()) {
                  var _ := BucketImpl.FreeMutBucketSeq(buckets);
                  s := lNone;
                } else {
                  linear var node := Node(
                    pivots,
                    if |children| as uint64 == 0 then None else childrenOpt,
                    buckets);
                  s := lSome(node);
                }
              case lNone => 
                s := lNone;
            }      
          } else {
            s := lNone;
          }
        } else {
          s := lNone;
        }
      } else {
        s := lNone;
      }
    } else {
      s := lNone;
    }
  }

  function ISectorOpt(s : Option<Sector>): Option<IMM.Sector>
  requires s.Some? ==> SSI.WFSector(s.value)
  requires s.Some? ==> SSM.WFSector(SSI.ISector(s.value))
  {
    if s.Some? then
      Some(SSI.ISector(s.value))
    else
      None
  }

  method ValToSector(v: V) returns (linear s : lOption<SSI.Sector>)
  requires IMM.valToSector.requires(v)
  requires SizeOfV(v) < 0x1_0000_0000_0000_0000
  ensures s.lSome? ==> SSI.WFSector(s.value)
  ensures s.lSome? ==> SSM.WFSector(SSI.ISector(s.value))
  ensures MapOption(s.Option(), SSI.ISector) == IMM.valToSector(v)
  {
    if v.c == 0 {
      var sb := Marshalling.valToSuperblock(v.val);
      if sb.Some? {
        s := lSome(SSI.SectorSuperblock(sb.value));
      } else {
        s := lNone;
      }
    } else if v.c == 1 {
      linear var tableOpt := IndirectionTable.IndirectionTable.ValToIndirectionTable(v.val);
      if tableOpt.lSome? {
        s := lSome(SSI.SectorIndirectionTable(unwrap_value(tableOpt)));
      } else {
        dispose_lnone(tableOpt);
        s := lNone;
      }
    } else {
      linear var nodeopt := ValToNode(v.val);
      linear match nodeopt {
        case lSome(node) => s := lSome(SSI.SectorNode(node));
        case lNone => s := lNone;
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

  function method pivotToKey(pivots: Pivots.PivotTable, i: uint64) : (k: Key)
  requires 0 <= i as int < |pivots|
  requires Pivots.WFPivots(pivots)
  {
    if pivots[i].Element? then
      pivots[i].e 
    else
      []
  }

  lemma pivotToKeyEqualskeyToPivot(pivots: Pivots.PivotTable, i: int)
  requires 0 <= i < |pivots|
  requires |pivots| < 0x4000_0000_0000_0000
  requires Pivots.WFPivots(pivots)
  ensures var k := pivotToKey(pivots, i as uint64);
    && Marshalling.keyToPivot(k, i >= 1) == pivots[i]
  {
    var k := pivotToKey(pivots, i as uint64);
    var pivot := Marshalling.keyToPivot(k, i >= 1);

    if pivots[i].Element? && pivots[i].e == [] {
      if i >= 1 {
        var b := Pivots.Keyspace.SmallestElement();
        assert b == pivots[i];
        Pivots.Keyspace.reveal_IsStrictlySorted();
        assert Pivots.Keyspace.lt(pivots[i-1], pivots[i]);
        Pivots.Keyspace.IsNotMinimum(pivots[i-1], pivots[i]);
        Pivots.Keyspace.reveal_NotMinimum();
        assert false;
      }
    }
  }

  method strictlySortedPivotsToVal(pivots: Pivots.PivotTable)
  returns (v : V, size: uint64)
  requires Pivots.WFPivots(pivots)
  requires |pivots| < (Uint64UpperBound() - 8) / (8 + KeyType.MaxLen() as nat)
  ensures ValidVal(v)
  ensures ValInGrammar(v, Marshalling.PivotTableGrammar())
  ensures |v.a| == |pivots|
  ensures Marshalling.valToStrictlySortedPivots(v) == Some(pivots)
  ensures SizeOfV(v) <= 8 + |pivots| * (8 + KeyType.MaxLen() as int)
  ensures SizeOfV(v) == 8 + Marshalling.pivotTableWeight(pivots)
  ensures size as nat == SizeOfV(v)
  {
    var vs: array<V> := new V[|pivots| as uint64];
    assert SeqSum(vs[..0]) == 0 by {
      reveal_SeqSum();
    }

    size := 0;
    var i: uint64 := 0;
    while i < |pivots| as uint64
    invariant i as nat <= |pivots|
    invariant forall j | 0 <= j < i :: ValidVal(vs[j])
    invariant forall j | 0 <= j < i :: vs[j] == VByteArray(pivotToKey(pivots, j))
    invariant Marshalling.keyValSeqToPivots(vs[..i]).value == pivots[..i]
    invariant SeqSum(vs[..i]) == Marshalling.pivotTableWeight(pivots[..i])
    invariant size as nat == SeqSum(vs[..i])
    {
      vs[i] := VByteArray(pivotToKey(pivots, i));
      assert vs[..i+1] == vs[..i] + [ vs[i] ];
      lemma_SeqSum_prefix(vs[..i], vs[i]);
      Marshalling.pivotTableWeightUpperBound(pivots[..i]);
      pivotToKeyEqualskeyToPivot(pivots, i as int);
      size := size + 8 + Pivots.PivotSize(pivots[i]);
      i := i + 1;
    }

    assert pivots[..i] == pivots;
    Marshalling.pivotTableWeightUpperBound(pivots);
    v := VArray(vs[..i]);
    size := size + 8;

    assert Marshalling.valToStrictlySortedPivots(v) == Some(pivots); // observe
    assert SizeOfV(v) <= 8 + |pivots| * (8 + KeyType.MaxLen() as int); // observe
  }

  method pivotsToVal(pivots: Pivots.PivotTable)
  returns (v : V, size: uint64)
  requires Pivots.WFPivots(pivots)
  requires |pivots| <= MaxNumChildren() as int + 1
  ensures ValidVal(v)
  ensures ValInGrammar(v, Marshalling.PivotTableGrammar())
  ensures |v.a| == |pivots|
  ensures Marshalling.valToPivots(v) == Some(pivots)
  ensures SizeOfV(v) <= 8 + |pivots| * (8 + KeyType.MaxLen() as int)
  ensures SizeOfV(v) == size as int
  {
    v, size := strictlySortedPivotsToVal(pivots);
  }

  method {:fuel SizeOfV,3}
  bucketToVal(shared bucket: BucketImpl.MutBucket)
  returns (v: V, size: uint64)
  requires bucket.Inv()
  requires BucketWellMarshalled(bucket.I())
  requires WeightBucket(bucket.bucket) <= MaxTotalBucketWeight()
  ensures ValInGrammar(v, Marshalling.BucketGrammar())
  ensures ValidVal(v)
  ensures Marshalling.valToBucket(v) == Some(bucket.bucket)
  ensures SizeOfV(v) == WeightBucket(bucket.bucket) + 32
  ensures SizeOfV(v) == size as int
  {
    var pkv := bucket.GetPkv();
    v := PackedKVMarshalling.ToVal(pkv);
    PackedKVMarshalling.parseMarshalledCorrect(pkv);
    assert PackedKVMarshalling.fromVal(v) == Some(pkv);
    DPKV.WeightBucketPkv_eq_WeightPkv(pkv);
    assert PackedKV.WeightPkv(pkv) < Uint32UpperBound() as uint64;
    size := bucket.weight + 32;
    PackedKVMarshalling.SizeOfVPackedKVIsBucketWeight(pkv);
  }

  method bucketsToVal(shared buckets: lseq<BucketImpl.MutBucket>, end: uint64)
  returns (v: V, size: uint64)
  requires 0 <= end as int <= |buckets|
  requires BucketImpl.MutBucket.InvLseq(buckets)
  requires forall i | 0 <= i < |buckets| :: WFBucket(buckets[i].bucket)
  requires BucketsLib.BucketListWellMarshalled(BucketImpl.MutBucket.ILseq(buckets))
  requires |buckets| <= MaxNumChildren() as int
  requires WeightBucketList(BucketImpl.MutBucket.ILseq(buckets)) <= MaxTotalBucketWeight()
  ensures ValidVal(v)
  ensures ValInGrammar(v, GArray(Marshalling.BucketGrammar()))
  ensures |v.a| == end as int
  ensures Marshalling.valToBuckets(v.a) == Some(BucketImpl.MutBucket.ILseq(buckets)[..end])
  ensures SizeOfV(v) <= 8 + WeightBucketList(BucketImpl.MutBucket.ILseq(buckets)[..end]) + end as int * 32
  ensures SizeOfV(v) == size as int
  {
    if end == 0 {
      v := VArray([]);
      size := 8;
    } else {
      WeightBucketListSlice(BucketImpl.MutBucket.ILseq(buckets), 0, end as int - 1);
      WeightBucketLeBucketList(BucketImpl.MutBucket.ILseq(buckets), end as int - 1);
      BucketImpl.MutBucket.Islice(buckets, 0, end as int - 1);

      var pref, pref_size := bucketsToVal(buckets, end-1);
      shared var bucket := lseq_peek(buckets, end-1);

      var bucketVal, bucket_size := bucketToVal(bucket);
      
      lemma_SeqSum_prefix(pref.a, bucketVal);
      ghost var ibuckets := BucketImpl.MutBucket.ILseq(buckets)[..end];
      assert ibuckets == DropLast(ibuckets) + [ Last(ibuckets) ];
      assert Marshalling.valToBuckets(pref.a).value == DropLast(ibuckets);

      assert Marshalling.valToBuckets(VArray(pref.a + [bucketVal]).a) 
        == Some(BucketImpl.MutBucket.ILseq(buckets)[..end]); // observe

      reveal_WeightBucketList();
      BucketImpl.MutBucket.ISeqInduction(lseqs(buckets)[..end]);
      assert WeightBucketList(BucketImpl.MutBucket.ILseq(buckets)[..end])
          == WeightBucketList(BucketImpl.MutBucket.ILseq(buckets)[..end-1]) + WeightBucket(bucket.I());

      v := VArray(pref.a + [bucketVal]);
      size := pref_size + bucket_size;
    }
  }

  function INodeOpt(s : Option<Node>): Option<IMM.Node>
  requires s.Some? ==> s.value.Inv()
  {
    if s.Some? then
      Some(s.value.I())
    else
      None
  }

  method {:fuel SizeOfV,4} nodeToVal(shared node: Node)
  returns (v : V, size: uint64)
  requires node.Inv()
  requires SSM.WFNode(node.I())
  requires BT.WFNode(SSM.INode(node.I()))
  requires BucketsLib.BucketListWellMarshalled(BucketImpl.MutBucket.ILseq(node.buckets))
  ensures ValidVal(v)
  ensures ValInGrammar(v, Marshalling.PivotNodeGrammar())
  ensures IMM.valToNode(v) == INodeOpt(Some(node))
  ensures SizeOfV(v) <= NodeBlockSize() - 32 - 8
  ensures SizeOfV(v) == size as int
  {
    var end := lseq_length_as_uint64(node.buckets);
    var buckets, size_buckets := bucketsToVal(node.buckets, end);
    assert BucketImpl.MutBucket.ILseq(node.buckets)[..end] == BucketImpl.MutBucket.ILseq(node.buckets);

    var pivots, size_pivots := pivotsToVal(node.pivotTable);

    var children, size_children;
    if node.children.Some? {
      children := childrenToVal(node.children.value);
      size_children := 8 + 8 * |node.children.value| as uint64;
    } else {
      children := VUint64Array([]);
      size_children := 8;
    }
    assert SizeOfV(children) == size_children as int;

    v := VTuple([pivots, children, buckets]);

    assert SizeOfV(pivots) <= (8 + (MaxNumChildren()+1)*(8 + KeyType.MaxLen() as int));
    assert SizeOfV(children) <= (8 + MaxNumChildren() * 8);
    assert SizeOfV(buckets) <= 8 + MaxNumChildren() * (32) + MaxTotalBucketWeight();

    assert SizeOfV(v) == SizeOfV(pivots) + SizeOfV(children) + SizeOfV(buckets);

    lemma_node_fits_in_block();

    size := size_buckets + size_pivots + size_children;
  }

  method {:fuel SizeOfV,7}
  superblockToVal(superblock: SectorType.Superblock)
  returns (v : V)
  requires JC.WFSuperblock(superblock)
  ensures ValidVal(v)
  ensures ValInGrammar(v, Marshalling.SuperblockGrammar())
  ensures SizeOfV(v) <= 4000
  ensures Marshalling.valToSuperblock(v) == Some(superblock)
  {
    v := VTuple([
      VUint64(superblock.counter),
      VUint64(superblock.journalStart),
      VUint64(superblock.journalLen),
      VUint64(superblock.indirectionTableLoc.addr),
      VUint64(superblock.indirectionTableLoc.len)
    ]);
  }

  method sectorToVal(shared sector: SSI.Sector)
  returns (v : V, size: uint64)
  requires SSI.WFSector(sector)
  requires SSM.WFSector(SSI.ISector(sector))
  requires sector.SectorNode?
  requires sector.SectorNode? ==> SSM.WFNode(sector.node.I())
  requires sector.SectorNode? ==> BT.WFNode(SSM.INode(sector.node.I()))
  requires sector.SectorNode? ==> 
    BucketsLib.BucketListWellMarshalled(BucketImpl.MutBucket.ILseq(sector.node.buckets))
  ensures ValidVal(v)
  ensures ValInGrammar(v, Marshalling.SectorGrammar());
  ensures Marshalling.valToSector(v) == Some(SSM.ISector(SSI.ISector(sector)))
  ensures sector.SectorNode? ==> SizeOfV(v) <= NodeBlockSize() as int - 32
  ensures SizeOfV(v) < 0x1_0000_0000_0000_0000 - 32
  ensures SizeOfV(v) == size as int
  {
    var w, s := nodeToVal(sector.node);
    v := VCase(2, w);
    size := s + 8;
  }

  method indirectionTableSectorToVal(shared sector: SSI.Sector)
  returns (v : V, size: uint64)
  requires SSI.WFSector(sector)
  requires SSM.WFSector(SSI.ISector(sector))
  requires sector.SectorIndirectionTable?
  requires sector.indirectionTable.Inv()
  requires BC.WFCompleteIndirectionTable(sector.indirectionTable.I())
  // TODO(andreal) I believe this is unnecessary: modifies sector.indirectionTable.Repr
  ensures sector.indirectionTable.Inv() 
  && sector.indirectionTable.I() == old(sector.indirectionTable.I())
  ensures ValidVal(v)
  ensures ValInGrammar(v, Marshalling.SectorGrammar());
  ensures Marshalling.valToSector(v) == Some(SSM.ISector(SSI.ISector(sector)))
  ensures SizeOfV(v) < 0x1_0000_0000_0000_0000 - 32
  ensures SizeOfV(v) == size as int
  {
    var w, s := sector.indirectionTable.IndirectionTableToVal();
    v := VCase(1, w);
    size := s + 8;
  }

  /////// Marshalling and de-marshalling

  method ParseSector(data: seq<byte>, start: uint64) returns (linear s : lOption<Sector>)
  requires start as int <= |data| < 0x1_0000_0000_0000_0000;
  ensures s.lSome? ==> SSI.WFSector(s.value)
  ensures s.lSome? ==> SSM.WFSector(SSI.ISector(s.value))
  ensures ISectorOpt(s.Option()) == IMM.parseSector(data[start..])
  ensures s.lSome? && s.value.SectorNode? ==> SSM.WFNode(s.value.node.I())
  ensures s.lSome? && s.value.SectorNode? ==> BT.WFNode(SSM.INode(s.value.node.I()))
  {
    IMM.reveal_parseSector();
    var success, v, rest_index := ParseVal(data, start, Marshalling.SectorGrammar());

    if success {
      lemma_SizeOfV_parse_Val(data[start..], Marshalling.SectorGrammar());
      assert SizeOfV(v) < 0x1_0000_0000_0000_0000;
      s := ValToSector(v);
    } else {
      s := lNone;
    }
  }

  method MarshallIntoFixedSize(val:V, ghost grammar:G, start: uint64, n: uint64) returns (data:array<byte>)
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

  method ParseCheckedSector(data: seq<byte>) returns (linear s : lOption<Sector>)
  requires |data| < 0x1_0000_0000
  ensures s.lSome? ==> SSI.WFSector(s.value)
  ensures s.lSome? ==> SSM.WFSector(SSI.ISector(s.value))
  ensures ISectorOpt(s.Option()) == IMM.parseCheckedSector(data)
  ensures s.lSome? && s.value.SectorNode? ==> SSM.WFNode(s.value.node.I())
  ensures s.lSome? && s.value.SectorNode? ==> BT.WFNode(SSM.INode(s.value.node.I()))
  {
    if |data| as uint64 >= 32 {
      // TODO unnecessary copy here
      var hash := CRC32_C_Impl.compute_crc32c_padded(data[32 as uint64..]);
      if hash == data[..32 as uint64] {
        s := ParseSector(data, 32);
      } else {
        s := lNone;
      }
    } else {
      s := lNone;
    }

    IMM.reveal_parseCheckedSector();
  }

  method MarshallCheckedSectorIndirectionTable(shared table: IndirectionTable.IndirectionTable, ghost sector: Sector) returns (data : array?<byte>)
  requires sector == SSI.SectorIndirectionTable(table);
  requires SSI.WFSector(sector)
  requires SSM.WFSector(SSI.ISector(sector))
  // ensures sector.indirectionTable.Inv()
  //   && sector.indirectionTable.I() == old(sector.indirectionTable.I())
  ensures data != null ==> IMM.parseCheckedSector(data[..]).Some?
  ensures data != null ==>
      && SSM.ISector(IMM.parseCheckedSector(data[..]).value)
      == SSM.ISector(SSI.ISector(sector))
  ensures data != null ==> 32 <= data.Length
  ensures data != null && sector.SectorIndirectionTable? ==> data.Length <= IndirectionTableBlockSize() as int
  ensures sector.SectorIndirectionTable? && Marshalling.IsInitIndirectionTable(sector.indirectionTable.I()) ==> data != null;
  {
    var w, s := table.IndirectionTableToVal();
    var v := VCase(1, w);
    var computedSize := s + 8;

    // var v, computedSize := indirectionTableSectorToVal(sector);
    var size: uint64 := computedSize + 32;

    ghost var ghosty := true;
    if ghosty {
      if Marshalling.IsInitIndirectionTable(sector.indirectionTable.I())
      {
        Marshalling.InitIndirectionTableSizeOfV(sector.indirectionTable.I(), v);
      }
    }

    if size > IndirectionTableBlockSizeUint64() {
      data := null;
    } else {
      data := MarshallIntoFixedSize(v, Marshalling.SectorGrammar(), 32, size);

      IMM.reveal_parseSector();
      IMM.reveal_parseCheckedSector();

      var hash := CRC32_C_Array_Impl.compute_crc32c_padded(data, 32, data.Length as uint32 - 32);

      assert data[32..] == data[32..data.Length];
      assert hash == CRC32_C.crc32_c_padded(data[32..]);
      ghost var data_suffix := data[32..];
      NativeArrays.CopySeqIntoArray(hash, 0, data, 0, 32);
      assert data_suffix == data[32..];
    }
    /*
    if end == 0 {
      return null;
    }

    // case 1 indicates indirection table
    Pack_LittleEndian_Uint64_into_Array(1, data, 32);

    //NativeBenchmarking.start("crc32");
    var hash := CRC32_C_Array_Impl.compute_crc32c_padded(data, 32, data.Length as uint64 - 32);
    NativeArrays.CopySeqIntoArray(hash, 0, data, 0, 32);
    //NativeBenchmarking.end("crc32");

    //NativeBenchmarking.end("MarshallCheckedSector");

    return data;
    */
  }

  method MarshallCheckedSector(shared sector: Sector) returns (data : array?<byte>)
  requires SSI.WFSector(sector)
  requires SSM.WFSector(SSI.ISector(sector))
  requires sector.SectorNode? ==> SSM.WFNode(sector.node.I())
  requires sector.SectorNode? ==> BT.WFNode(SSM.INode(sector.node.I()))
  requires sector.SectorSuperblock? ==> JC.WFSuperblock(sector.superblock)
  ensures sector.SectorIndirectionTable? ==> 
    sector.indirectionTable.Inv()
    && sector.indirectionTable.I() == old(sector.indirectionTable.I())
  ensures data != null ==> IMM.parseCheckedSector(data[..]).Some?
  ensures data != null ==>
      && SSM.ISector(IMM.parseCheckedSector(data[..]).value)
      == SSM.ISector(SSI.ISector(sector))
  ensures data != null ==> 32 <= data.Length
  ensures data != null && sector.SectorNode? ==> data.Length <= NodeBlockSize() as int
  ensures data != null && sector.SectorIndirectionTable? ==> data.Length <= IndirectionTableBlockSize() as int
  ensures sector.SectorSuperblock? ==> data != null && data.Length == 4096;
  ensures sector.SectorIndirectionTable? && Marshalling.IsInitIndirectionTable(sector.indirectionTable.I()) ==> data != null;
  ensures sector.SectorNode? && BucketListWellMarshalled(BucketImpl.MutBucket.ILseq(sector.node.buckets)) ==> data != null
  {
    if sector.SectorSuperblock? {
      var v0 := superblockToVal(sector.superblock);
      var v := VCase(0, v0);
      data := MarshallIntoFixedSize(
          v, Marshalling.SectorGrammar(), 32, 4096);

      IMM.reveal_parseSector();
      IMM.reveal_parseCheckedSector();

      var hash := CRC32_C_Array_Impl.compute_crc32c_padded(data, 32, data.Length as uint32 - 32);

      assert data[32..] == data[32..data.Length];
      assert hash == CRC32_C.crc32_c_padded(data[32..]);
      ghost var data_suffix := data[32..];
      NativeArrays.CopySeqIntoArray(hash, 0, data, 0, 32);
      assert data_suffix == data[32..];
    } else if sector.SectorIndirectionTable? {
      //NativeBenchmarking.start("MarshallCheckedSector");

      //var data := new byte[IndirectionTableBlockSizeUint64()];

      //NativeBenchmarking.start("marshallIndirectionTable");
      //NativeBenchmarking.end("marshallIndirectionTable");

      var v, computedSize := indirectionTableSectorToVal(sector);
      var size: uint64 := computedSize + 32;

      ghost var ghosty := true;
      if ghosty {
        if Marshalling.IsInitIndirectionTable(sector.indirectionTable.I())
        {
          Marshalling.InitIndirectionTableSizeOfV(sector.indirectionTable.I(), v);
        }
      }

      if size > IndirectionTableBlockSizeUint64() {
        data := null;
      } else {
        data := MarshallIntoFixedSize(v, Marshalling.SectorGrammar(), 32, size);

        IMM.reveal_parseSector();
        IMM.reveal_parseCheckedSector();

        var hash := CRC32_C_Array_Impl.compute_crc32c_padded(data, 32, data.Length as uint32 - 32);

        assert data[32..] == data[32..data.Length];
        assert hash == CRC32_C.crc32_c_padded(data[32..]);
        ghost var data_suffix := data[32..];
        NativeArrays.CopySeqIntoArray(hash, 0, data, 0, 32);
        assert data_suffix == data[32..];
      }
      /*
      if end == 0 {
        return null;
      }

      // case 1 indicates indirection table
      Pack_LittleEndian_Uint64_into_Array(1, data, 32);

      //NativeBenchmarking.start("crc32");
      var hash := CRC32_C_Array_Impl.compute_crc32c_padded(data, 32, data.Length as uint64 - 32);
      NativeArrays.CopySeqIntoArray(hash, 0, data, 0, 32);
      //NativeBenchmarking.end("crc32");

      //NativeBenchmarking.end("MarshallCheckedSector");

      return data;
      */
    } else {
      var wellmarshalled := sector.node.BucketsWellMarshalled();
      assert wellmarshalled == BucketsLib.BucketListWellMarshalled(BucketImpl.MutBucket.ILseq(sector.node.buckets));
      if wellmarshalled {
        var v, computedSize := sectorToVal(sector);
        var size := computedSize + 32;

        data := MarshallIntoFixedSize(v, Marshalling.SectorGrammar(), 32, size);

        IMM.reveal_parseSector();
        IMM.reveal_parseCheckedSector();

        var hash := CRC32_C_Array_Impl.compute_crc32c_padded(data, 32, data.Length as uint32 - 32);

        assert data[32..] == data[32..data.Length];
        assert hash == CRC32_C.crc32_c_padded(data[32..]);
        ghost var data_suffix := data[32..];
        NativeArrays.CopySeqIntoArray(hash, 0, data, 0, 32);
        assert data_suffix == data[32..];
      } else {
        data := null;
      }
    }
  }
}
