include "../lib/Marshalling/GenericMarshalling.i.dfy"
include "StateImpl.i.dfy"
include "StateModel.i.dfy"
include "../lib/Buckets/BucketImpl.i.dfy"
include "../lib/Base/Option.s.dfy"
include "../lib/Lang/System/NativeArrays.s.dfy"
include "../lib/Base/NativeBenchmarking.s.dfy"
include "../lib/Base/LinearOption.i.dfy"
include "../lib/Crypto/CRC32CArrayImpl.i.dfy"
include "../lib/Crypto/CRC32CImpl.i.dfy"

include "../ByteBlockCacheSystem/Marshalling.i.dfy"
include "MarshallingModel.i.dfy"

module MarshallingImpl {
  import IM = StateModel
  import SI = StateImpl
  import opened BoxNodeImpl
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
  import StateImpl
  import CRC32_C
  import CRC32_C_Impl
  import CRC32_C_Array_Impl
  import NativeArrays
  import MutableMapModel
  import IndirectionTableImpl
  import IndirectionTableModel
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

  import Pivots = PivotsLib
  import MS = MapSpec
  import KeyspaceImpl = Lexicographic_Byte_Order_Impl
  import Keyspace = KeyspaceImpl.Ord
  import PackedKVMarshalling
  import PackedKV
  import DPKV = DynamicPkv
  import PSA = PackedStringArray
  import PSAM = PackedStringArrayMarshalling

  type Key = KeyType.Key
  type Reference = IMM.Reference
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
      var c := KeyspaceImpl.cmp(a[i-1], a[i]);
      if c >= 0 {
        return false;
      }
      i := i + 1;
    }

    return true;
  }

  method KeyValSeqToKeySeq(vs: seq<V>) returns (result: Option<seq<Key>>)
    requires |vs| < Uint64UpperBound()
    requires forall i | 0 <= i < |vs| :: ValidVal(vs[i])
    requires forall i | 0 <= i < |vs| :: ValInGrammar(vs[i], GByteArray)
    ensures result == Marshalling.keyValSeqToKeySeq(vs)
  {
    var aresult: array<Key> := new Key[|vs| as uint64];

    var i: uint64 := 0;
    while i < |vs| as uint64
      invariant i as nat <= |vs|
      invariant Marshalling.keyValSeqToKeySeq(vs[..i]).Some?
      invariant aresult[..i] == Marshalling.keyValSeqToKeySeq(vs[..i]).value
    {
      if KeyType.MaxLen() < |vs[i].b| as uint64 {
        return None;
      }
      aresult[i] := vs[i].b;
      i := i + 1;
    }
    assert vs[..i] == vs;
    return Some(aresult[..i]);
  }
  
  method ValToStrictlySortedKeySeq(v: V) returns (s : Option<seq<Key>>)
  requires Marshalling.valToStrictlySortedKeySeq.requires(v)
  ensures s == Marshalling.valToStrictlySortedKeySeq(v)
  {
    var okeys := KeyValSeqToKeySeq(v.a);
    if okeys == None {
      return None;
    }
    
    var is_sorted := IsStrictlySortedKeySeq(okeys.value);
    if is_sorted {
      return okeys;
    } else {
      return None;
    }
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
    invariant !error ==> Some(BucketImpl.MutBucket.ISeq(lseqs(buckets)[..i])) == Marshalling.valToBuckets(a[..i])
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
          assert BucketImpl.MutBucket.ISeq(lseqs(buckets)[..i]) == Marshalling.valToBuckets(a[..i]).value;
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
            linear var b := lseq_take_inout(inout buckets, j);
            b.Free();
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

  method ValToNode(v: V) returns (s : Option<Node>)
  requires IMM.valToNode.requires(v)
  requires SizeOfV(v) < 0x1_0000_0000_0000_0000
  ensures s.Some? ==> s.value.Inv()
  ensures INodeOpt(s) == IMM.valToNode(v)
  ensures s.Some? ==> fresh(s.value.Repr)
  {
    assert ValidVal(v.t[0]);
    assert ValidVal(v.t[1]);
    assert ValidVal(v.t[2]);

    var pivots_len := |v.t[0 as uint64].a| as uint64;
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

    if |v.t[2 as uint64].a| as uint64 > MaxNumChildrenUint64() {
      return None;
    }

    linear var obuckets := ValToBuckets(v.t[2 as uint64].a);
    linear match obuckets {
      case lSome(buckets) =>
        assert |buckets| as uint64 <= MaxNumChildrenUint64();
        IMM.WeightBucketListLteSize(v.t[2 as uint64], BucketImpl.MutBucket.ILseq(buckets));
        assert WeightBucketList(BucketImpl.MutBucket.ILseq(buckets)) < 0x1_0000_0000_0000_0000;

        var w: uint64 := BucketImpl.MutBucket.computeWeightOfSeq(buckets);
        if (w > MaxTotalBucketWeightUint64()) {
          BucketImpl.MutBucket.FreeSeq(buckets);
          s := None;
        } else {
          var node := new Node(pivots, if |children| as uint64 == 0 then None else childrenOpt, buckets);
          s := Some(node);
        }
      case lNone => 
        s := None;
    }
  }

  function ISectorOpt(s : Option<Sector>): Option<IMM.Sector>
  requires s.Some? ==> StateImpl.WFSector(s.value)
  requires s.Some? ==> IM.WFSector(StateImpl.ISector(s.value))
  reads if s.Some? then StateImpl.SectorObjectSet(s.value) else {}
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
  ensures s.Some? ==> IM.WFSector(StateImpl.ISector(s.value))
  ensures MapOption(s, SI.ISector) == IMM.valToSector(v)
  ensures s.Some? ==> fresh(SI.SectorRepr(s.value));
  {
    if v.c == 0 {
      var s := Marshalling.valToSuperblock(v.val);
      if s.Some? {
        return Some(StateImpl.SectorSuperblock(s.value));
      } else {
        return None;
      }
    } else if v.c == 1 {
      var mutMap := IndirectionTableImpl.IndirectionTable.ValToIndirectionTable(v.val);
      if mutMap != null {
        return Some(StateImpl.SectorIndirectionTable(mutMap));
      } else {
        return None;
      }
    } else {
      var node := ValToNode(v.val);
      match node {
        case Some(s) => return Some(StateImpl.SectorNode(s));
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

  lemma WeightKeySeqLe(keys: seq<Key>)
  ensures WeightKeyList(keys) <= |keys| * (8 + KeyType.MaxLen() as int)
  {
    WeightKeyMultisetUpperBound(multiset(keys));
  }

  method strictlySortedKeySeqToVal(keys: seq<Key>)
  returns (v : V, size: uint64)
  requires Keyspace.IsStrictlySorted(keys)
  requires |keys| < (Uint64UpperBound() - 8) / (8 + KeyType.MaxLen() as nat)
  ensures ValidVal(v)
  ensures ValInGrammar(v, Marshalling.PivotTableGrammar())
  ensures |v.a| == |keys|
  ensures Marshalling.valToStrictlySortedKeySeq(v) == Some(keys)
  ensures SizeOfV(v) <= 8 + |keys| * (8 + KeyType.MaxLen() as int)
  ensures SizeOfV(v) == 8 + Marshalling.pivotTableWeight(keys)
  ensures size as nat == SizeOfV(v)
  {
    WeightKeySeqLe(keys);

    var vs: array<V> := new V[|keys| as uint64];

    assert SeqSum(vs[..0]) == 0 by {
      reveal_SeqSum();
    }

    size := 0;
    var i: uint64 := 0;
    while i < |keys| as uint64
      invariant i as nat <= |keys|
      invariant forall j | 0 <= j < i :: ValidVal(vs[j])
      invariant forall j | 0 <= j < i :: vs[j] == VByteArray(keys[j])
      invariant Marshalling.keyValSeqToKeySeq(vs[..i]).value == keys[..i]
      invariant SeqSum(vs[..i]) == Marshalling.pivotTableWeight(keys[..i])
      invariant size as nat == SeqSum(vs[..i])
    {
      vs[i] := VByteArray(keys[i]);
      assert vs[..i+1] == vs[..i] + [ vs[i] ];
      lemma_SeqSum_prefix(vs[..i], vs[i]);
      Marshalling.pivotTableWeightUpperBound(keys[..i]);
      calc <= {
        size as nat + 8 + |keys[i]|;
        SeqSum(vs[..i+1]);
        |keys| * (8 + KeyType.MaxLen() as int);
        (Uint64UpperBound() - 8) / (8 + KeyType.MaxLen() as nat) * (8 + KeyType.MaxLen() as int);
        Uint64UpperBound() - 8;
      }
      size := size + 8 + |keys[i]| as uint64;
      i := i + 1;
    }

    assert keys[..i] == keys;
    Marshalling.pivotTableWeightUpperBound(keys);
    v := VArray(vs[..i]);
    size := size + 8;
  }

  lemma KeyInPivotsIsNonempty(pivots: seq<Key>)
  requires Pivots.WFPivots(pivots)
  requires |pivots| > 0
  ensures |pivots[0]| != 0;
  {
    var e := Keyspace.SmallerElement(pivots[0]);
    SeqComparison.reveal_lte();
  }

  method pivotsToVal(pivots: seq<Key>)
  returns (v : V, size: uint64)
  requires Pivots.WFPivots(pivots)
  requires |pivots| <= MaxNumChildren() as int - 1
  ensures ValidVal(v)
  ensures ValInGrammar(v, Marshalling.PivotTableGrammar())
  ensures |v.a| == |pivots|
  ensures Marshalling.valToPivots(v) == Some(pivots)
  ensures SizeOfV(v) <= 8 + |pivots| * (8 + KeyType.MaxLen() as int)
  ensures SizeOfV(v) == size as int
  {
    v, size := strictlySortedKeySeqToVal(pivots);

    ghost var ghosty := true;
    if ghosty && |pivots| > 0 {
      KeyInPivotsIsNonempty(pivots);
    }
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

      assert Marshalling.valToBuckets(VArray(pref.a + [bucketVal]).a) == Some(BucketImpl.MutBucket.ILseq(buckets)[..end]); // observe (reduces verification time)

      reveal_WeightBucketList();
      BucketImpl.MutBucket.ISeqInduction(lseqs(buckets)[..end]);
      assert WeightBucketList(BucketImpl.MutBucket.ILseq(buckets)[..end])
          == WeightBucketList(BucketImpl.MutBucket.ILseq(buckets)[..end-1]) + WeightBucket(bucket.I());

      v := VArray(pref.a + [bucketVal]);
      size := pref_size + bucket_size;
    }
  }

  function INodeOpt(s : Option<Node>): Option<IMM.Node>
  reads if s.Some? then {s.value} else {}
  reads if s.Some? then s.value.Repr else {}
  reads if s.Some? then {s.value.box} else {}
  reads if s.Some? then s.value.box.Repr else {}
  requires s.Some? ==> s.value.Inv()
  {
    if s.Some? then
      Some(s.value.I())
    else
      None
  }

  method {:fuel SizeOfV,4} nodeToVal(node: Node)
  returns (v : V, size: uint64)
  requires node.Inv()
  requires IM.WFNode(node.I())
  requires BT.WFNode(IM.INode(node.I()))
  requires BucketsLib.BucketListWellMarshalled(BucketImpl.MutBucket.ILseq(node.Read().buckets))
  ensures ValidVal(v)
  ensures ValInGrammar(v, Marshalling.PivotNodeGrammar())
  ensures IMM.valToNode(v) == INodeOpt(Some(node))
  ensures SizeOfV(v) <= NodeBlockSize() - 32 - 8
  ensures SizeOfV(v) == size as int
  {
    var end := node.GetBucketsLen();
    var buckets, size_buckets := bucketsToVal(node.box.Borrow().buckets, end);
    assert BucketImpl.MutBucket.ILseq(node.Read().buckets)[..end] == BucketImpl.MutBucket.ILseq(node.Read().buckets);

    var pivots, size_pivots := pivotsToVal(node.box.Borrow().pivotTable);

    var nodechildren := node.GetChildren();
    var children, size_children;
    if nodechildren.Some? {
      children := childrenToVal(nodechildren.value);
      size_children := 8 + 8 * |nodechildren.value| as uint64;
    } else {
      children := VUint64Array([]);
      size_children := 8;
    }
    assert SizeOfV(children) == size_children as int;

    v := VTuple([pivots, children, buckets]);

    assert SizeOfV(pivots) <= (8 + (MaxNumChildren()-1)*(8 + KeyType.MaxLen() as int));
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

  method sectorToVal(sector: StateImpl.Sector)
  returns (v : V, size: uint64)
  requires StateImpl.WFSector(sector)
  requires IM.WFSector(StateImpl.ISector(sector))
  requires sector.SectorNode?
  requires sector.SectorNode? ==> IM.WFNode(sector.node.I())
  requires sector.SectorNode? ==> BT.WFNode(IM.INode(sector.node.I()))
  requires sector.SectorNode? ==> BucketsLib.BucketListWellMarshalled(BucketImpl.MutBucket.ILseq(sector.node.Read().buckets))
  ensures ValidVal(v)
  ensures ValInGrammar(v, Marshalling.SectorGrammar());
  ensures Marshalling.valToSector(v) == Some(IM.ISector(StateImpl.ISector(sector)))
  ensures sector.SectorNode? ==> SizeOfV(v) <= NodeBlockSize() as int - 32
  ensures SizeOfV(v) < 0x1_0000_0000_0000_0000 - 32
  ensures SizeOfV(v) == size as int
  {
    match sector {
      case SectorNode(node) => {
        var w, s := nodeToVal(node);
        v := VCase(2, w);
        size := s + 8;
      }
    }
  }

  method indirectionTableSectorToVal(sector: StateImpl.Sector)
  returns (v : V, size: uint64)
  requires StateImpl.WFSector(sector)
  requires IM.WFSector(StateImpl.ISector(sector))
  requires sector.SectorIndirectionTable?
  requires sector.indirectionTable.Inv()
  requires BC.WFCompleteIndirectionTable(IM.IIndirectionTable(sector.indirectionTable.I()))
  modifies sector.indirectionTable.Repr
  ensures sector.indirectionTable.Inv() && sector.indirectionTable.I() == old(sector.indirectionTable.I()) && sector.indirectionTable.Repr == old(sector.indirectionTable.Repr)
  ensures ValidVal(v)
  ensures ValInGrammar(v, Marshalling.SectorGrammar());
  ensures Marshalling.valToSector(v) == Some(IM.ISector(StateImpl.ISector(sector)))
  ensures SizeOfV(v) < 0x1_0000_0000_0000_0000 - 32
  ensures SizeOfV(v) == size as int
  {
    var w, s := sector.indirectionTable.indirectionTableToVal();
    v := VCase(1, w);
    size := s + 8;
  }

  /////// Marshalling and de-marshalling

  method ParseSector(data: seq<byte>, start: uint64) returns (s : Option<Sector>)
  requires start as int <= |data| < 0x1_0000_0000_0000_0000;
  ensures s.Some? ==> StateImpl.WFSector(s.value)
  ensures s.Some? ==> IM.WFSector(StateImpl.ISector(s.value))
  ensures ISectorOpt(s) == IMM.parseSector(data[start..])
  ensures s.Some? && s.value.SectorNode? ==> IM.WFNode(s.value.node.I())
  ensures s.Some? && s.value.SectorNode? ==> BT.WFNode(IM.INode(s.value.node.I()))
  ensures s.Some? ==> fresh(SI.SectorRepr(s.value));
  {
    IMM.reveal_parseSector();
    var success, v, rest_index := ParseVal(data, start, Marshalling.SectorGrammar());

    if success {
      lemma_SizeOfV_parse_Val(data[start..], Marshalling.SectorGrammar());
      assert SizeOfV(v) < 0x1_0000_0000_0000_0000;

      var s := ValToSector(v);
      return s;
    } else {
      return None;
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

  method ParseCheckedSector(data: seq<byte>) returns (s : Option<Sector>)
  requires |data| < 0x1_0000_0000;
  ensures s.Some? ==> StateImpl.WFSector(s.value)
  ensures s.Some? ==> IM.WFSector(StateImpl.ISector(s.value))
  ensures ISectorOpt(s) == IMM.parseCheckedSector(data)
  ensures s.Some? && s.value.SectorNode? ==> IM.WFNode(s.value.node.I())
  ensures s.Some? && s.value.SectorNode? ==> BT.WFNode(IM.INode(s.value.node.I()))
  ensures s.Some? ==> fresh(SI.SectorRepr(s.value))
  {
    s := None;

    if |data| as uint64 >= 32 {
      // TODO unnecessary copy here
      var hash := CRC32_C_Impl.compute_crc32c_padded(data[32 as uint64..]);
      if hash == data[..32 as uint64] {
        s := ParseSector(data, 32);
      }
    }

    IMM.reveal_parseCheckedSector();
  }

  method MarshallCheckedSector(sector: Sector) returns (data : array?<byte>)
  requires StateImpl.WFSector(sector)
  requires IM.WFSector(StateImpl.ISector(sector))
  requires sector.SectorNode? ==> IM.WFNode(sector.node.I())
  requires sector.SectorNode? ==> BT.WFNode(IM.INode(sector.node.I()))
  requires sector.SectorSuperblock? ==> JC.WFSuperblock(sector.superblock)
  modifies if sector.SectorIndirectionTable? then sector.indirectionTable.Repr else {}
  ensures sector.SectorIndirectionTable? ==> (sector.indirectionTable.Inv() && sector.indirectionTable.I() == old(sector.indirectionTable.I()) && sector.indirectionTable.Repr == old(sector.indirectionTable.Repr))
  ensures data != null ==> IMM.parseCheckedSector(data[..]).Some?
  ensures data != null ==>
      && IM.ISector(IMM.parseCheckedSector(data[..]).value)
      == IM.ISector(StateImpl.ISector(sector))
  ensures data != null ==> 32 <= data.Length
  ensures data != null && sector.SectorNode? ==> data.Length <= NodeBlockSize() as int
  ensures data != null && sector.SectorIndirectionTable? ==> data.Length <= IndirectionTableBlockSize() as int
  ensures sector.SectorSuperblock? ==> data != null && data.Length == 4096;
  ensures sector.SectorIndirectionTable? && Marshalling.IsInitIndirectionTable(IndirectionTableModel.I(sector.indirectionTable.I())) ==> data != null;
  ensures sector.SectorNode? && BucketListWellMarshalled(BucketImpl.MutBucket.ILseq(sector.node.Read().buckets)) ==> data != null
  {
    if sector.SectorSuperblock? {
      var v0 := superblockToVal(sector.superblock);
      var v := VCase(0, v0);
      var data := MarshallIntoFixedSize(
          v, Marshalling.SectorGrammar(), 32, 4096);

      IMM.reveal_parseSector();
      IMM.reveal_parseCheckedSector();

      var hash := CRC32_C_Array_Impl.compute_crc32c_padded(data, 32, data.Length as uint32 - 32);

      assert data[32..] == data[32..data.Length];
      assert hash == CRC32_C.crc32_c_padded(data[32..]);
      ghost var data_suffix := data[32..];
      NativeArrays.CopySeqIntoArray(hash, 0, data, 0, 32);
      assert data_suffix == data[32..];

      return data;
    } else if sector.SectorIndirectionTable? {
      //NativeBenchmarking.start("MarshallCheckedSector");

      //var data := new byte[IndirectionTableBlockSizeUint64()];

      //NativeBenchmarking.start("marshallIndirectionTable");
      //NativeBenchmarking.end("marshallIndirectionTable");

      var v, computedSize := indirectionTableSectorToVal(sector);
      var size: uint64 := computedSize + 32;

      ghost var ghosty := true;
      if ghosty {
        if Marshalling.IsInitIndirectionTable(IndirectionTableModel.I(sector.indirectionTable.I()))
        {
          Marshalling.InitIndirectionTableSizeOfV(IndirectionTableModel.I(sector.indirectionTable.I()), v);
        }
      }

      if size > IndirectionTableBlockSizeUint64() {
        return null;
      }

      var data := MarshallIntoFixedSize(v, Marshalling.SectorGrammar(), 32, size);

      IMM.reveal_parseSector();
      IMM.reveal_parseCheckedSector();

      var hash := CRC32_C_Array_Impl.compute_crc32c_padded(data, 32, data.Length as uint32 - 32);

      assert data[32..] == data[32..data.Length];
      assert hash == CRC32_C.crc32_c_padded(data[32..]);
      ghost var data_suffix := data[32..];
      NativeArrays.CopySeqIntoArray(hash, 0, data, 0, 32);
      assert data_suffix == data[32..];

      return data;

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
      assert wellmarshalled == BucketsLib.BucketListWellMarshalled(BucketImpl.MutBucket.ILseq(sector.node.Read().buckets));
      if !wellmarshalled {
        return null;
      }
      
      var v, computedSize := sectorToVal(sector);
      var size := computedSize + 32;

      var data := MarshallIntoFixedSize(v, Marshalling.SectorGrammar(), 32, size);

      IMM.reveal_parseSector();
      IMM.reveal_parseCheckedSector();

      var hash := CRC32_C_Array_Impl.compute_crc32c_padded(data, 32, data.Length as uint32 - 32);

      assert data[32..] == data[32..data.Length];
      assert hash == CRC32_C.crc32_c_padded(data[32..]);
      ghost var data_suffix := data[32..];
      NativeArrays.CopySeqIntoArray(hash, 0, data, 0, 32);
      assert data_suffix == data[32..];

      return data;
    }
  }
}
