include "../lib/Marshalling/GenericMarshalling.i.dfy"
include "ImplState.i.dfy"
include "ImplModel.i.dfy"
include "MutableBucket.i.dfy"
include "../lib/Option.s.dfy"

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
  import Native

  import BT = PivotBetreeSpec`Internal

  import ValueWithDefault`Internal
  import M = ValueMessage`Internal
  import LBAType

  import Pivots = PivotsLib
  import MS = MapSpec
  import Keyspace = MS.Keyspace

  import MM = MutableMap

  type Reference = IMM.Reference
  type LBA = IMM.LBA
  type Location = IMM.Location
  type Sector = IS.Sector
  type Message = IMM.Message
  type Key = IMM.Key

  /////// Conversion to PivotNode

  method {:fuel ValInGrammar,3} ValToLocsAndSuccs(a: seq<V>) returns (s : Option<ImplState.MutIndirectionTable>)
  requires IMM.valToLocsAndSuccs.requires(a)
  ensures MapOption(s, (x: ImplState.MutIndirectionTable) reads x => x.Contents) == IMM.valToLocsAndSuccs(a)
  ensures s.Some? ==> s.value.Inv()
  ensures s.Some? ==> s.value.Count as nat == |a|
  ensures s.Some? ==> s.value.Count as nat < 0x10000000000000000 / 8
  ensures s.Some? ==> fresh(s.value) && fresh(s.value.Repr)
  {
    if |a| == 0 {
      var newHashMap := new MM.ResizingHashMap<(Option<Location>, seq<Reference>)>(1024); // TODO(alattuada) magic numbers
      s := Some(newHashMap);
      assume s.value.Count as nat == |a|;
    } else {
      var res := ValToLocsAndSuccs(DropLast(a));
      match res {
        case Some(mutMap) => {
          var tuple := Last(a);
          var ref := IMM.valToReference(tuple.t[0]);
          var lba := IMM.valToLBA(tuple.t[1]);
          var len := tuple.t[2].u;
          var succs := IMM.valToChildren(tuple.t[3]);
          match succs {
            case None => {
              s := None;
            }
            case Some(succs) => {
              var graphRef := mutMap.Get(ref);
              var loc := LBAType.Location(lba, len);
              if graphRef.Some? || lba == 0 || !LBAType.ValidLocation(loc) {
                s := None;
              } else {
                var _ := mutMap.Insert(ref, (Some(loc), succs));
                s := Some(mutMap);
                assume s.Some? ==> s.value.Count as nat < 0x10000000000000000 / 8; // TODO(alattuada) removing this results in trigger loop
                assume s.value.Count as nat == |a|;
              }
            }
          }
        }
        case None => {
          s := None;
        }
      }
    }
  }

  method GraphClosed(table: ImplState.MutIndirectionTable) returns (result: bool)
    requires table.Inv()
    requires BC.GraphClosed.requires(IM.IIndirectionTable(table.Contents).graph)
    ensures BC.GraphClosed(IM.IIndirectionTable(table.Contents).graph) == result
  {
    var m := table.ToMap();
    var m' := map ref | ref in m :: m[ref].1;
    result := BC.GraphClosed(m');
  }

  method ValToIndirectionTable(v: V) returns (s : Option<ImplState.MutIndirectionTable>)
  requires IMM.valToIndirectionTable.requires(v)
  ensures MapOption(s, (x: ImplState.MutIndirectionTable) reads x => x.Contents) == IMM.valToIndirectionTable(v)
  ensures s.Some? ==> s.value.Inv()
  {
    var res := ValToLocsAndSuccs(v.a);
    match res {
      case Some(res) => {
        var rootRef := res.Get(BT.G.Root());
        var isGraphClosed := GraphClosed(res);
        if rootRef.Some? && isGraphClosed {
          s := Some(res);
        } else {
          s := None;
        }
      }
      case None => {
        s := None;
      }
    }
  }

  lemma valToStrictlySortedKeySeqPrefixNone(v: V, i: int)
  requires IMM.valToStrictlySortedKeySeq.requires(v)
  requires 0 <= i <= |v.a|
  ensures IMM.valToStrictlySortedKeySeq(VArray(v.a[..i])) == None
      ==> IMM.valToStrictlySortedKeySeq(v) == None
  decreases |v.a| - i
  {
    if (i < |v.a|) {
      valToStrictlySortedKeySeqPrefixNone(v, i+1);
      assert DropLast(v.a[..i+1]) == v.a[..i];
    } else {
      assert v.a[..i] == v.a;
    }
  }

  method ValToStrictlySortedKeySeq(v: V) returns (s : Option<seq<Key>>)
  requires IMM.valToStrictlySortedKeySeq.requires(v)
  ensures s == IMM.valToStrictlySortedKeySeq(v)
  {
    var ar := new Key[|v.a| as uint64];

    var i: uint64 := 0;
    while i < |v.a| as uint64
    invariant 0 <= i as int <= |v.a|
    invariant IMM.valToStrictlySortedKeySeq(VArray(v.a[..i])) == Some(ar[..i])
    {
      assert ValInGrammar(v.a[i], GByteArray);
      assert ValidVal(v.a[i]);

      valToStrictlySortedKeySeqPrefixNone(v, i as int + 1);

      if |v.a[i].b| as uint64 > Keyspace.MaxLen() {
        return None;
      }

      ar[i] := v.a[i].b;

      assert DropLast(v.a[..i+1]) == v.a[..i];
      assert ar[..i+1] == ar[..i] + [ar[i]];

      if (i > 0) {
        var c := Keyspace.cmp(ar[i-1], ar[i]);
        if (c >= 0) {
          assert Last(ar[..i]) == ar[i-1];
          assert IMM.valToStrictlySortedKeySeq(VArray(v.a[..i+1])) == None;

          return None;
        }
      }

      i := i + 1;
    }

    assert v.a[..i] == v.a;
    assert ar[..i] == ar[..];
    s := Some(ar[..]);
  }

  lemma valToMessageSeqPrefixNone(v: V, i: int)
  requires IMM.valToMessageSeq.requires(v)
  requires 0 <= i <= |v.a|
  ensures IMM.valToMessageSeq(VArray(v.a[..i])) == None
      ==> IMM.valToMessageSeq(v) == None
  decreases |v.a| - i
  {
    if (i < |v.a|) {
      valToMessageSeqPrefixNone(v, i+1);
      assert DropLast(v.a[..i+1]) == v.a[..i];
    } else {
      assert v.a[..i] == v.a;
    }
  }

  method ValToMessageSeq(v: V) returns (s : Option<seq<Message>>)
  requires IMM.valToMessageSeq.requires(v)
  ensures s == IMM.valToMessageSeq(v)
  {
    var ar := new Message[|v.a| as uint64];

    var i: uint64 := 0;
    while i < |v.a| as uint64
    invariant 0 <= i as int <= |v.a|
    invariant IMM.valToMessageSeq(VArray(v.a[..i])) == Some(ar[..i])
    {
      assert ValInGrammar(v.a[i], GByteArray);
      assert ValidVal(v.a[i]);

      valToMessageSeqPrefixNone(v, i as int + 1);

      if |v.a[i].b| as uint64 > ValueWithDefault.MaxLen() {
        return None;
      }

      ar[i] := M.Define(v.a[i].b);

      assert DropLast(v.a[..i+1]) == v.a[..i];
      assert ar[..i+1] == ar[..i] + [ar[i]];

      i := i + 1;
    }

    assert v.a[..i] == v.a;
    assert ar[..i] == ar[..];
    s := Some(ar[..]);
  }


  method ValToPivots(v: V) returns (s : Option<seq<Key>>)
  requires IMM.valToPivots.requires(v)
  ensures s == IMM.valToPivots(v)
  {
    s := ValToStrictlySortedKeySeq(v);
    if (s.Some? && |s.value| as uint64 > 0 && |s.value[0]| as uint64 == 0) {
      s := None;
    }
  }

  method ValToBucket(v: V, pivotTable: seq<Key>, i: int) returns (s : Option<KVList.Kvl>)
  requires IMM.valToBucket.requires(v, pivotTable, i)
  ensures s.Some? ==> KVList.WF(s.value)
  ensures s.Some? ==> WFBucketAt(KVList.I(s.value), pivotTable, i)
  ensures s == IMM.valToBucket(v, pivotTable, i)
  {
    assert ValidVal(v.t[0]);

    var keys := ValToStrictlySortedKeySeq(v.t[0]);

    if keys.None? {
      return None;
    }

    var values := ValToMessageSeq(v.t[1]);

    if values.None? {
      return None;
    }

    var kvl := KVList.Kvl(keys.value, values.value);

    var wf := KVList.IsWF(kvl);
    if !wf {
      return None;
    }

    // Check that the keys fit in the desired bucket
    if |kvl.keys| > 0 {
      if i > 0 {
        var c := Keyspace.cmp(pivotTable[i-1], kvl.keys[0]);
        if (c > 0) {
          KVList.Imaps(kvl, 0);
          return None;
        }
      }

      if i < |pivotTable| {
        var c := Keyspace.cmp(pivotTable[i], kvl.keys[|kvl.keys| - 1]);
        if (c <= 0) {
          KVList.Imaps(kvl, |kvl.keys| - 1);
          return None;
        }
      }
    }

    forall key | key in KVList.I(kvl)
    ensures Pivots.Route(pivotTable, key) == i
    ensures KVList.I(kvl)[key] != M.IdentityMessage()
    {
      var j := KVList.IndexOfKey(kvl, key);
      KVList  .Imaps(kvl, j);
      if |kvl.keys| > 0 {
        Keyspace.IsStrictlySortedImpliesLte(kvl.keys, 0, j);
        Keyspace.IsStrictlySortedImpliesLte(kvl.keys, j, |kvl.keys| - 1);
      }
      Pivots.RouteIs(pivotTable, key, i);
    }

    assert WFBucketAt(KVList.I(kvl), pivotTable, i);

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
    var ar := new MutableBucket.MutBucket?[|a|];

    var i := 0;
    while i < |a|
    invariant 0 <= i <= |a|
    invariant forall k: nat | k < i :: ar[k] != null;
    invariant forall k: nat | k < i :: ar[k].Inv()
    invariant forall k: nat | k < i :: ar !in ar[k].Repr
    invariant forall j, k | 0 <= j < i && 0 <= k < i && j != k :: ar[j].Repr !! ar[k].Repr
    invariant forall k: nat | k < i :: fresh(ar[k].Repr)
    invariant forall k: nat | k < i :: WFBucketAt(ar[k].Bucket, pivotTable, k)
    invariant IMM.valToBuckets(a[..i], pivotTable).Some?
    invariant MutableBucket.MutBucket.ISeq(ar[..i]) == IMM.valToBuckets(a[..i], pivotTable).value
    {
      var b := ValToBucket(a[i], pivotTable, i);
      if (b.None?) {
        s := None;

        LemmaValToBucketNone(a, pivotTable, i);
        return;
      }

      assume WeightBucket(KVList.I(b.value)) < 0x1_0000_0000_0000_0000;
      var bucket := new MutableBucket.MutBucket(b.value);
      assert forall k: nat | k < i :: ar[k].Inv();
      ar[i] := bucket;
      assert forall k: nat | k < i :: ar[k].Inv();
      assert ar[i].Inv();
      assert forall k: nat | k < i+1 :: ar[k].Inv();

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
    var pivotsOpt := ValToPivots(v.t[0]);
    if (pivotsOpt.None?) {
      return None;
    }
    var pivots := pivotsOpt.value;

    var childrenOpt := IMM.valToChildren(v.t[1]);
    if (childrenOpt.None?) {
      return None;
    }
    var children := childrenOpt.value;

    if (!((|children| == 0 || |children| == |pivots| + 1) && |v.t[2].a| == |pivots| + 1)) {
      return None;
    }

    assert ValidVal(v.t[2]);
    var bucketsOpt := ValToBuckets(v.t[2].a, pivots);
    if (bucketsOpt.None?) {
      return None;
    }
    var buckets := bucketsOpt.value;

    if |buckets| as uint64 > MaxNumChildren() as uint64 {
      return None;
    }

    assume WeightBucketList(MutableBucket.MutBucket.ISeq(buckets)) < 0x1_0000_0000_0000_0000; // TODO we should be able to prove this using the fact that it was deserialized:
    var w: uint64 := MutableBucket.MutBucket.computeWeightOfSeq(buckets);
    if (w > MaxTotalBucketWeight() as uint64) {
      return None;
    }

    var node := new Node(pivots, if |children| == 0 then None else childrenOpt, buckets);

    return Some(node);
  }


  function ISectorOpt(s : Option<Sector>): Option<IMM.Sector>
  requires s.Some? ==> ImplState.WFSector(s.value)
  requires s.Some? ==> IM.WFSector(ImplState.ISector(s.value))
  reads if s.Some? && s.value.SectorIndirectionTable? then s.value.indirectionTable.Repr else {}
  reads if s.Some? && s.value.SectorBlock?
      then set i | 0 <= i < |s.value.block.buckets| :: s.value.block.buckets[i]
      else {}
  reads if s.Some? && s.value.SectorBlock?
      then set i, o | 0 <= i < |s.value.block.buckets| && o in s.value.block.buckets[i].Repr :: o
      else {}
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
      var mutMap := ValToIndirectionTable(v.val);
      match mutMap {
        case Some(s) => return Some(ImplState.SectorIndirectionTable(s));
        case None => return None;
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

  // TODO(alattuada) remove?
  method {:fuel ValInGrammar,2} lbasSuccsToVal(indirectionTable: map<Reference, (Option<Location>, seq<Reference>)>) returns (v: Option<V>)
  requires forall ref | ref in indirectionTable :: indirectionTable[ref].0.Some?
  requires forall ref | ref in indirectionTable :: BC.ValidLocationForNode(indirectionTable[ref].0.value)
  requires |indirectionTable| < 0x1_0000_0000_0000_0000 / 8
  ensures v.Some? ==> ValidVal(v.value)
  ensures v.Some? ==> ValInGrammar(v.value, IMM.IndirectionTableGrammar());
  ensures v.Some? ==> |v.value.a| == |indirectionTable|
  ensures v.Some? ==> IMM.valToLocsAndSuccs(v.value.a) == Some(indirectionTable)
  {
    if (|indirectionTable| == 0) {
      return Some(VArray([]));
    } else {
      var ref :| ref in indirectionTable.Keys;
      var vpref := lbasSuccsToVal(MapRemove(indirectionTable, {ref}));
      match vpref {
        case None => return None;
        case Some(vpref) => {
          var loc := indirectionTable[ref].0.value;
          if (|indirectionTable[ref].1| >= 0x1_0000_0000_0000_0000) {
            return None;
          }
          var succs := indirectionTable[ref].1;
          var succsV := childrenToVal(indirectionTable[ref].1);
          var tuple := VTuple([IMM.refToVal(ref), IMM.lbaToVal(loc.addr), VUint64(loc.len), succsV]);

          assert MapRemove(indirectionTable, {ref})[ref := (Some(loc), succs)] == indirectionTable;

          //assert ref == valToReference(tuple.t[0]);
          //assert lba == valToReference(tuple.t[1]);
          //assert !(ref in MapRemove(graph, {ref}));
          assert BC.ValidLocationForNode(loc);
          //assert !(lba == 0);
          //assert valToLocssAndSuccs(vpref.a + [tuple]) == Some((lbas, graph));
          assert ValidVal(tuple);

          return Some(VArray(vpref.a + [tuple]));
        }
      }
    }
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

  method strictlySortedKeySeqToVal(keys: seq<Key>) returns (v : V)
  requires Keyspace.IsStrictlySorted(keys)
  requires |keys| < 0x1_0000_0000_0000_0000
  ensures ValidVal(v)
  ensures ValInGrammar(v, GArray(GByteArray))
  ensures |v.a| == |keys|
  ensures IMM.valToStrictlySortedKeySeq(v) == Some(keys)
  ensures SizeOfV(v) <= 8 + |keys| * (8 + Keyspace.MaxLen() as int)
  ensures SizeOfV(v) == 8 + WeightKeySeq(keys)
  {
    var ar := new V[|keys| as uint64];
    var i: uint64 := 0;
    while i < |keys| as uint64
    invariant i as int <= |keys|
    invariant ValidVal(VArray(ar[..i]))
    invariant ValInGrammar(VArray(ar[..i]), GArray(GByteArray))
    invariant IMM.valToStrictlySortedKeySeq(VArray(ar[..i])) == Some(keys[..i])
    invariant SizeOfV(VArray(ar[..i])) <= 8 + i as int * (8 + Keyspace.MaxLen() as int)
    invariant SizeOfV(VArray(ar[..i])) == 8 + WeightKeySeq(keys[..i])
    {
      ar[i] := VByteArray(keys[i]);

      lemma_SeqSum_prefix(ar[..i], VByteArray(keys[i]));
      assert keys[..i+1][..i] == keys[..i];
      assert ar[..i+1][..i] == ar[..i];
      assert ar[..i+1] == ar[..i] + [ar[i]];
      assert keys[..i] + [keys[i]] == keys[..i+1];

      if i > 0 {
        Keyspace.IsStrictlySortedImpliesLt(keys, i as int - 1, i as int);
      }

      assert i > 0 ==> keys[i-1] == Last(DropLast(keys[..i as int + 1]));
      assert keys[i] == Last(keys[..i as int + 1]);

      i := i + 1;
    }
    v := VArray(ar[..]);

    assert ar[..i] == ar[..];
    assert keys[..i] == keys;
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
  ensures ValInGrammar(v, GArray(GByteArray))
  ensures |v.a| == |pivots|
  ensures IMM.valToPivots(v) == Some(pivots)
  ensures SizeOfV(v) <= 8 + |pivots| * (8 + Keyspace.MaxLen() as int)
  {
    v := strictlySortedKeySeqToVal(pivots);

    if |pivots| as uint64 > 0 {
      KeyInPivotsIsNonempty(pivots);
    }
  }

  method messageSeqToVal(s: seq<Message>) returns (v : V)
  requires forall i | 0 <= i < |s| :: s[i] != M.IdentityMessage()
  requires |s| < 0x1_0000_0000_0000_0000
  ensures ValidVal(v)
  ensures ValInGrammar(v, GArray(GByteArray))
  ensures |v.a| == |s|
  ensures IMM.valToMessageSeq(v) == Some(s)
  ensures SizeOfV(v) == 8 + WeightMessageSeq(s)
  {
    var ar := new V[|s| as uint64];
    var i: uint64 := 0;
    while i < |s| as uint64
    invariant 0 <= i <= |s| as uint64
    invariant ValidVal(VArray(ar[..i]))
    invariant ValInGrammar(VArray(ar[..i]), GArray(GByteArray))
    invariant IMM.valToMessageSeq(VArray(ar[..i])) == Some(s[..i])
    invariant SizeOfV(VArray(ar[..i])) == 8 + WeightMessageSeq(s[..i])
    {
      ar[i] := VByteArray(s[i].value);

      lemma_SeqSum_prefix(ar[..i], VByteArray(s[i].value));
      assert s[..i+1][..i] == s[..i];
      assert ar[..i+1][..i] == ar[..i];
      assert ar[..i+1] == ar[..i] + [ar[i]];
      assert s[..i] + [s[i]] == s[..i+1];

      assert WeightMessage(s[i])
          == SizeOfV(ar[i]);

      i := i + 1;
    }
    v := VArray(ar[..]);

    assert ar[..i] == ar[..];
    assert s[..i] == s;
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
    if |buckets| == 0 {
      v := VArray([]);
    } else {
      WeightBucketListSlice(MutableBucket.MutBucket.ISeq(buckets), 0, |buckets| - 1);
      WeightBucketLeBucketList(MutableBucket.MutBucket.ISeq(buckets), |buckets| - 1);
      MutableBucket.MutBucket.Islice(buckets, 0, |buckets| - 1);

      var pref := bucketsToVal(DropLast(buckets), pivotTable);
      var bucket := Last(buckets);

      var bucketVal := bucketToVal(bucket, pivotTable, |buckets| - 1);
      assert buckets == DropLast(buckets) + [Last(buckets)]; // observe
      lemma_SeqSum_prefix(pref.a, bucketVal);
      assert IMM.valToBuckets(VArray(pref.a + [bucketVal]).a, pivotTable).Some?; // observe
      assert IMM.valToBuckets(VArray(pref.a + [bucketVal]).a, pivotTable).value == MutableBucket.MutBucket.ISeq(buckets); // observe
      assert IMM.valToBuckets(VArray(pref.a + [bucketVal]).a, pivotTable) == Some(MutableBucket.MutBucket.ISeq(buckets)); // observe (reduces verification time)

      assert buckets == DropLast(buckets) + [Last(buckets)];

      reveal_WeightBucketList();
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
      BC.WFCompleteIndirectionTable(IM.IIndirectionTable(sector.indirectionTable.Contents))
  ensures v.Some? ==> ValidVal(v.value)
  ensures v.Some? ==> ValInGrammar(v.value, IMM.SectorGrammar());
  ensures v.Some? ==> IMM.valToSector(v.value) == Some(ImplState.ISector(sector))
  ensures sector.SectorBlock? ==> v.Some?
  ensures sector.SectorBlock? ==> SizeOfV(v.value) <= BlockSize() as int - 32
  {
    match sector {
      case SectorIndirectionTable(mutMap) => {
        assert forall r | r in mutMap.Contents :: r in IM.IIndirectionTable(sector.indirectionTable.Contents).locs
            ==> mutMap.Contents[r].0.Some? && BC.ValidLocationForNode(mutMap.Contents[r].0.value);
        var table := mutMap.ToArray();
        ghost var tableSeq := table[..];
        /* (doc) assert mutMap.Contents.Values == set i | 0 <= i < |tableSeq| :: tableSeq[i].1; */
        assert forall i: nat | i < |tableSeq| :: tableSeq[i].1 == mutMap.Contents[tableSeq[i].0];
        assert forall i: nat, j: nat | i <= j < |tableSeq| :: tableSeq[i].0 == tableSeq[j].0 ==> i == j;
        if table.Length < 0x1_0000_0000_0000_0000 / 8 {
          assert forall i: nat | i < |tableSeq| :: tableSeq[i].1.0.Some?;
          // TODO this probably warrants a new invariant, or may leverage the weights branch, see TODO in BlockCache
          assume forall i: nat | i < |tableSeq| :: |tableSeq[i].1.1| < |tableSeq|;
          /* (doc) assert table.Length == |mutMap.Contents.Keys| == |mutMap.Contents|; */
          var a: array<V> := new [table.Length] (_ => VUint64(0)); // temporary placeholder
          var i: uint64 := 0;
          ghost var partial := map[];
          while i < table.Length as uint64
          invariant i <= table.Length as uint64
          invariant forall j | j < i :: ValidVal(a[j])
          invariant forall j | j < i :: ValInGrammar(a[j], GTuple([GUint64, GUint64, GUint64, GUint64Array]))
          // NOALIAS/CONST table doesn't need to be mutable, if we could say so we wouldn't need this
          invariant table[..] == tableSeq
          invariant IMM.valToLocsAndSuccs(a[..i]).Some?
          invariant IMM.valToLocsAndSuccs(a[..i]).value == partial
          invariant |partial.Keys| == i as nat
          invariant partial.Keys <= mutMap.Contents.Keys
          invariant forall r | r in partial :: r in mutMap.Contents && partial[r] == mutMap.Contents[r]
          // NOALIAS/CONST mutMap doesn't need to be mutable, if we could say so we wouldn't need this
          invariant mutMap.Contents == old(mutMap.Contents)
          invariant forall r | r in partial :: exists j: nat | j < i as nat :: table[j].0 == r
          {
            // TODO I'd use a seq comprehension, but I don't know how to extract properties of the elements

            var (ref, locOptGraph: (Option<LBAType.Location>, seq<Reference>)) := table[i];
            // NOTE: deconstructing in two steps to work around c# translation bug
            var (locOpt, graph) := locOptGraph;
            var loc := locOpt.value;
            var childrenVal := VUint64Array(graph);

            // == mutation ==
            partial := partial[ref := (locOpt, graph)];
            a[i] := VTuple([IMM.refToVal(ref), IMM.lbaToVal(loc.addr), VUint64(loc.len), childrenVal]);
            i := i + 1;
            // ==============

            assert a[..i-1] == DropLast(a[..i]); // observe
          }
          /* (doc) assert |partial.Keys| == |mutMap.Contents.Keys|; */
          SetInclusionAndEqualCardinalityImpliesSetEquality(partial.Keys, mutMap.Contents.Keys);

          assert partial == ImplState.IIndirectionTable(mutMap); // observe
          assert a[..i] == a[..]; // observe
          v := Some(VCase(0, VArray(a[..])));
          return;
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
  ensures s.Some? && fresh(IS.SectorRepr(s.value))
  {
    s := None;

    if |data| as uint64 >= 32 {
      var hash := Crypto.Crc32(data[32..]);
      if hash == data[..32] {
        s := ParseSector(data, 32);
      }
    }

    IMM.reveal_parseCheckedSector();
  }

  method MarshallCheckedSector(sector: Sector) returns (data : array?<byte>)
  requires ImplState.WFSector(sector)
  requires IM.WFSector(ImplState.ISector(sector))
  requires sector.SectorBlock? ==> IM.WFNode(sector.block.I())
  requires sector.SectorBlock? ==> BT.WFNode(IM.INode(sector.block.I()))
  ensures data != null ==> IMM.parseCheckedSector(data[..]) == ISectorOpt(Some(sector))
  ensures data != null ==> data.Length <= BlockSize() as int
  ensures data != null ==> 32 <= data.Length
  ensures data != null && sector.SectorIndirectionTable? ==> data.Length == BlockSize() as int
  ensures sector.SectorBlock? ==> data != null;
  {
    var v := sectorToVal(sector);
    match v {
      case None => return null;
      case Some(v) => {
        if (sector.SectorBlock? || SizeOfV(v) <= BlockSize() as int - 32) {
          //Native.BenchmarkingUtil.start();
          var size: uint64;
          if (sector.SectorIndirectionTable?) {
            size := BlockSize() as uint64;
          } else {
            var computedSize := GenericMarshalling.ComputeSizeOf(v);
            size := 32 + computedSize;
          }

          var data := MarshallIntoFixedSize(v, IMM.SectorGrammar(), 32, size);
          //Native.BenchmarkingUtil.end();

          IMM.reveal_parseSector();
          IMM.reveal_parseCheckedSector();

          var hash := Crypto.Crc32Array(data, 32, data.Length as uint64 - 32);
          assert data[32..] == data[32..data.Length];
          assert hash == Crypto.Crc32(data[32..]);
          ghost var data_suffix := data[32..];
          Native.Arrays.CopySeqIntoArray(hash, 0, data, 0, 32);
          assert data_suffix == data[32..];

          /*ghost var data_seq := data[..];
          assert |data_seq| >= 32;
          assert Crypto.Crc32(data_seq[32..])
              == Crypto.Crc32(data[32..])
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
