include "../lib/Marshalling/GenericMarshalling.i.dfy"
include "ImplState.i.dfy"
include "ImplModel.i.dfy"
include "KMTable.i.dfy"
include "../lib/Option.s.dfy"

include "Marshalling.i.dfy"
include "ImplMarshallingModel.i.dfy"

module ImplMarshalling {
  import IM = ImplModel
  import IS = ImplState
  import Marshalling
  import IMM = ImplMarshallingModel
  import opened GenericMarshalling
  import opened Options
  import opened NativeTypes
  import opened Sequences
  import opened Maps
  import opened BucketsLib
  import BC = BetreeGraphBlockCache
  import ImplState
  import KMTable
  import Crypto
  import Native

  import BT = PivotBetreeSpec`Internal

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
  type Node = IMM.Node

  /////// Conversion to PivotNode

  method {:fuel ValInGrammar,3} ValToLBAsAndSuccs(a: seq<V>) returns (s : Option<ImplState.MutIndirectionTable>)
  requires IMM.valToLocsAndSuccs.requires(a)
  ensures MapOption(s, (x: ImplState.MutIndirectionTable) => x.Contents) == IMM.valToLocsAndSuccs(a)
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
      var res := ValToLBAsAndSuccs(DropLast(a));
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
  ensures MapOption(s, (x: ImplState.MutIndirectionTable) => x.Contents) == IMM.valToIndirectionTable(v)
  ensures s.Some? ==> s.value.Inv()
  {
    var res := ValToLBAsAndSuccs(v.a);
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

      if (i > 0) {
        var c := Keyspace.cmp(ar[i-1], ar[i]);
        if (c >= 0) {
          assert Last(ar[..i]) == ar[i-1];
          assert IMM.valToStrictlySortedKeySeq(VArray(v.a[..i+1])) == None;

          return None;
        }
      }

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

  method ValToBucket(v: V, pivotTable: seq<Key>, i: int) returns (s : Option<KMTable.KMTable>)
  requires IMM.valToBucket.requires(v, pivotTable, i)
  ensures s.Some? ==> KMTable.WF(s.value)
  ensures s.Some? ==> KMTable.Bounded(s.value)
  ensures s.Some? ==> WFBucketAt(KMTable.I(s.value), pivotTable, i)
  ensures s == IMM.valToBucket(v, pivotTable, i)
  {
    assert ValidVal(v.t[0]);
    if (|v.t[0].a| as uint64 >= KMTable.MaxNumKeys()) {
      return None;
    }

    var keys := ValToStrictlySortedKeySeq(v.t[0]);

    if keys.None? {
      return None;
    }

    var values := IMM.valToMessageSeq(v.t[1]);

    if values.None? {
      return None;
    }

    var kmt := KMTable.KMTable(keys.value, values.value);

    var wf := KMTable.IsWF(kmt);
    if !wf {
      return None;
    }

    // Check that it fits in the desired bucket
    if |kmt.keys| > 0 {
      if i > 0 {
        var c := Keyspace.cmp(pivotTable[i-1], kmt.keys[0]);
        if (c > 0) {
          KMTable.Imaps(kmt, 0);
          return None;
        }
      }

      if i < |pivotTable| {
        var c := Keyspace.cmp(pivotTable[i], kmt.keys[|kmt.keys| - 1]);
        if (c <= 0) {
          KMTable.Imaps(kmt, |kmt.keys| - 1);
          return None;
        }
      }
    }

    forall key | key in KMTable.I(kmt)
    ensures Pivots.Route(pivotTable, key) == i
    ensures KMTable.I(kmt)[key] != M.IdentityMessage()
    {
      var j := KMTable.IndexOfKey(kmt, key);
      KMTable.Imaps(kmt, j);
      if |kmt.keys| > 0 {
        Keyspace.IsStrictlySortedImpliesLte(kmt.keys, 0, j);
        Keyspace.IsStrictlySortedImpliesLte(kmt.keys, j, |kmt.keys| - 1);
      }
      Pivots.RouteIs(pivotTable, key, i);
    }

    assert WFBucketAt(KMTable.I(kmt), pivotTable, i);
    s := Some(kmt);
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

  method ValToBuckets(a: seq<V>, pivotTable: seq<Key>) returns (s : Option<seq<KMTable.KMTable>>)
  requires IMM.valToBuckets.requires(a, pivotTable)
  ensures s.Some? ==> IM.WFBuckets(s.value)
  ensures s == IMM.valToBuckets(a, pivotTable)
  {
    var ar := new KMTable.KMTable[|a|];

    var i := 0;
    while i < |a|
    invariant 0 <= i <= |a|
    invariant forall k: nat | k < i :: KMTable.WF(ar[k])
    invariant forall k: nat | k < i :: KMTable.Bounded(ar[k])
    invariant forall k: nat | k < i :: WFBucketAt(KMTable.I(ar[k]), pivotTable, k)
    invariant IMM.valToBuckets(a[..i], pivotTable).Some?
    // TODO invariant Apply(KMTable.I, ar[..i]) == IMM.valToBuckets(a[..i], pivotTable).value
    {
      var b := ValToBucket(a[i], pivotTable, i);
      if (b.None?) {
        s := None;

        LemmaValToBucketNone(a, pivotTable, i);
        return;
      }

      ar[i] := b.value;

      assert DropLast(a[..i+1]) == a[..i];
      assert ar[..i+1] == ar[..i] + [b.value];

      i := i + 1;
    }

    assert a[..|a|] == a;
    assert ar[..|a|] == ar[..];

    assert IMM.valToBuckets(a[..], pivotTable).Some?;
    // TODO assert Apply(KMTable.I, ar[..]) == IMM.valToBuckets(a, pivotTable).value;

    s := Some(ar[..]);
  }

  method ValToNode(v: V) returns (s : Option<ImplState.Node>)
  requires IMM.valToNode.requires(v)
  ensures s.Some? ==> IM.WFNode(s.value)
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

    var node := IM.Node(pivots, if |children| == 0 then None else childrenOpt, buckets);

    assert IMM.valToNode(v).Some?;
    assert IM.WFBuckets(node.buckets);
    assert node == IMM.valToNode(v).value;
    return Some(node);
  }


  function ISectorOpt(s : Option<Sector>): Option<IMM.Sector>
  requires s.Some? ==> ImplState.WFSector(s.value)
  requires s.Some? ==> IM.WFSector(ImplState.ISector(s.value))
  reads if s.Some? && s.value.SectorIndirectionTable? then s.value.indirectionTable.Repr else {}
  {
    if s.Some? then
      Some(ImplState.ISector(s.value))
    else
      None
  }

  method ValToSector(v: V) returns (s : Option<ImplState.Sector>)
  requires IMM.valToSector.requires(v)
  ensures s.Some? ==> ImplState.WFSector(s.value)
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
  {
    return VUint64Array(children);
  }

  method {:fuel ValInGrammar,2} lbasSuccsToVal(indirectionTable: map<Reference, (Option<Location>, seq<Reference>)>) returns (v: Option<V>)
  requires forall ref | ref in indirectionTable :: indirectionTable[ref].0.Some?
  requires forall ref | ref in indirectionTable :: BC.ValidLocationForNode(indirectionTable[ref].0.value)
  requires |indirectionTable| < 0x1_0000_0000_0000_0000 / 8
  ensures v.Some? ==> ValidVal(v.value)
  ensures v.Some? ==> ValInGrammar(v.value, IMM.IndirectionTableGrammar());
  ensures v.Some? ==> |v.value.a| == |indirectionTable|
  ensures v.Some? ==> IMM.valToLocsAndSuccs(v.value.a) == Some(indirectionTable)
  /*{
    if (|locs| == 0) {
      assert locs == map[];
      assert graph == map[];
      return Some(VArray([]));
    } else {
      var ref :| ref in locs.Keys;
      var vpref := lbasSuccsToVal(MapRemove(locs, {ref}), MapRemove(graph, {ref}));
      match vpref {
        case None => return None;
        case Some(vpref) => {
          var loc := locs[ref];
          if (|graph[ref]| >= 0x1_0000_0000_0000_0000) {
            return None;
          }
          var succs := childrenToVal(graph[ref]);
          var tuple := VTuple([IMM.refToVal(ref), IMM.lbaToVal(loc.addr), VUint64(loc.len), succs]);

          assert MapRemove(locs, {ref})[ref := loc] == locs;
          assert MapRemove(graph, {ref})[ref := graph[ref]] == graph;

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
  }*/

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
  ensures SizeOfV(v) <= 8 + |keys| * (8 + IMM.CapKeySize() as int)
  ensures ValInGrammar(v, GArray(GByteArray))
  ensures |v.a| == |keys|
  ensures IMM.valToStrictlySortedKeySeq(v) == Some(keys)
  {
    var ar := new V[|keys| as uint64];
    var i: uint64 := 0;
    while i < |keys| as uint64
    invariant i as int <= |keys|
    invariant ValidVal(VArray(ar[..i]))
    invariant SizeOfV(VArray(ar[..i])) as int <= 8 + i as int * (8 + IMM.CapKeySize() as int)
    invariant ValInGrammar(VArray(ar[..i]), GArray(GByteArray))
    invariant IMM.valToStrictlySortedKeySeq(VArray(ar[..i])) == Some(keys[..i])
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
  requires |pivots| <= IMM.CapNumBuckets() as int - 1
  ensures ValidVal(v)
  ensures SizeOfV(v) <= 8 + |pivots| * (8 + IMM.CapKeySize() as int)
  ensures ValInGrammar(v, GArray(GByteArray))
  ensures |v.a| == |pivots|
  ensures IMM.valToPivots(v) == Some(pivots)
  {
    v := strictlySortedKeySeqToVal(pivots);

    if |pivots| > 0 {
      KeyInPivotsIsNonempty(pivots);
    }
  }

  method messageSeqToVal(s: seq<Message>) returns (v : V)
  requires |s| <= IMM.CapBucketNumEntries() as int
  requires forall i | 0 <= i < |s| :: s[i] != M.IdentityMessage()
  requires forall i | 0 <= i < |s| :: IMM.MessageSize(s[i]) <= IMM.CapValueSize() as int
  ensures ValidVal(v)
  ensures ValInGrammar(v, GArray(GByteArray))
  ensures SizeOfV(v) <= 8 + (8 + IMM.CapValueSize()) as int * IMM.CapBucketNumEntries() as int
  ensures |v.a| == |s|
  ensures IMM.valToMessageSeq(v) == Some(s)
  {
    var ar := new V[|s| as uint64];
    var i: uint64 := 0;
    while i < |s| as uint64
    invariant 0 <= i <= |s| as uint64
    invariant ValidVal(VArray(ar[..i]))
    invariant ValInGrammar(VArray(ar[..i]), GArray(GByteArray))
    invariant IMM.valToMessageSeq(VArray(ar[..i])) == Some(s[..i])
    invariant SizeOfV(VArray(ar[..i])) <= 8 + (8 + IMM.CapValueSize()) as int * i as int
    {
      ar[i] := VByteArray(s[i].value);

      lemma_SeqSum_prefix(ar[..i], VByteArray(s[i].value));
      assert s[..i+1][..i] == s[..i];
      assert ar[..i+1][..i] == ar[..i];
      assert ar[..i+1] == ar[..i] + [ar[i]];
      assert s[..i] + [s[i]] == s[..i+1];

      i := i + 1;
    }
    v := VArray(ar[..]);

    assert ar[..i] == ar[..];
    assert s[..i] == s;
  }

  // We pass in pivotTable and i so we can state the pre- and post-conditions.
  method {:fuel SizeOfV,3}
  bucketToVal(bucket: KMTable.KMTable, ghost pivotTable: Pivots.PivotTable, ghost i: int) returns (v: V)
  requires Pivots.WFPivots(pivotTable)
  requires KMTable.WF(bucket)
  requires WFBucketAt(KMTable.I(bucket), pivotTable, i)
  requires IMM.CappedBucket(bucket)
  requires 0 <= i <= |pivotTable|
  ensures ValInGrammar(v, IMM.BucketGrammar())
  ensures SizeOfV(v) <= (8 + (8+IMM.CapKeySize() as int) * IMM.CapBucketNumEntries() as int) + (8 + (8+IMM.CapValueSize() as int) * IMM.CapBucketNumEntries() as int)
  ensures ValidVal(v)
  ensures IMM.valToBucket(v, pivotTable, i) == Some(bucket)
  {
    var keys := strictlySortedKeySeqToVal(bucket.keys);
    var values := messageSeqToVal(bucket.values);
    v := VTuple([keys, values]);

    // FIXME dafny goes nuts with trigger loops here some unknown reason
    // without these obvious asserts.
    assert ValInGrammar(v.t[0], IMM.BucketGrammar().t[0]);
    assert ValInGrammar(v.t[1], IMM.BucketGrammar().t[1]);
    assert ValInGrammar(v, IMM.BucketGrammar());
  }

  method bucketsToVal(buckets: seq<KMTable.KMTable>, ghost pivotTable: Pivots.PivotTable) returns (v: V)
  requires Pivots.WFPivots(pivotTable)
  requires forall i | 0 <= i < |buckets| :: KMTable.WF(buckets[i])
  requires forall i | 0 <= i < |buckets| :: WFBucketAt(KMTable.I(buckets[i]), pivotTable, i)
  requires IMM.CappedBuckets(buckets)
  requires |buckets| <= IMM.CapNumBuckets() as int
  requires |buckets| <= |pivotTable| + 1
  ensures ValidVal(v)
  ensures SizeOfV(v) <= 8 + |buckets| * ((8 + (8+IMM.CapKeySize()) as int * IMM.CapBucketNumEntries() as int) + (8 + (8+IMM.CapValueSize()) as int * IMM.CapBucketNumEntries() as int))
  ensures ValInGrammar(v, GArray(IMM.BucketGrammar()))
  ensures |v.a| == |buckets|
  ensures IMM.valToBuckets(v.a, pivotTable) == Some(buckets)
  {
    if |buckets| == 0 {
      return VArray([]);
    } else {
      var pref := bucketsToVal(DropLast(buckets), pivotTable);
      var bucket := Last(buckets);
      var bucketVal := bucketToVal(bucket, pivotTable, |buckets| - 1);
      assert buckets == DropLast(buckets) + [Last(buckets)]; // observe
      lemma_SeqSum_prefix(pref.a, bucketVal);
      assert IMM.valToBuckets(VArray(pref.a + [bucketVal]).a, pivotTable).Some?; // observe
      assert IMM.valToBuckets(VArray(pref.a + [bucketVal]).a, pivotTable).value == buckets; // observe
      assert IMM.valToBuckets(VArray(pref.a + [bucketVal]).a, pivotTable) == Some(buckets); // observe (reduces verification time)
      return VArray(pref.a + [bucketVal]);
    }
  }

  function INodeOpt(s : Option<Node>): Option<IMM.Node>
  requires s.Some? ==> IM.WFNode(s.value)
  {
    if s.Some? then
      Some(s.value)
    else
      None
  }

  method {:fuel SizeOfV,4} nodeToVal(node: ImplState.Node) returns (v : V)
  requires IM.WFNode(node)
  requires BT.WFNode(IM.INode(node))
  requires IMM.CappedNode(node)
  ensures ValidVal(v)
  ensures SizeOfV(v) <= 
      8 + IMM.CapNumBuckets() as int * ((8 + (8+IMM.CapKeySize()) as int * IMM.CapBucketNumEntries() as int) + (8 + (8+IMM.CapValueSize()) as int * IMM.CapBucketNumEntries() as int)) +
      8 + (IMM.CapNumBuckets() as int - 1) * (8 + IMM.CapKeySize() as int) +
      8 + IMM.CapNumBuckets() as int * 8
  ensures ValInGrammar(v, IMM.PivotNodeGrammar())
  ensures IMM.valToNode(v) == INodeOpt(Some(node))
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

    assert SizeOfV(v) == SizeOfV(pivots) + SizeOfV(children) + SizeOfV(buckets);
    assert IMM.valToNode(v).Some?;
    assert IMM.valToNode(v).value == node;
  }

  method sectorToVal(sector: ImplState.Sector) returns (v : Option<V>)
  requires ImplState.WFSector(sector)
  requires IM.WFSector(ImplState.ISector(sector))
  requires sector.SectorBlock? ==> BT.WFNode(IM.INode(sector.block))
  requires sector.SectorBlock? ==> IMM.CappedNode(sector.block);
  requires sector.SectorIndirectionTable? ==>
      BC.WFCompleteIndirectionTable(IM.IIndirectionTable(sector.indirectionTable.Contents))
  ensures v.Some? ==> ValidVal(v.value)
  ensures v.Some? ==> ValInGrammar(v.value, IMM.SectorGrammar());
  ensures v.Some? ==> IMM.valToSector(v.value) == ISectorOpt(Some(sector))
  ensures sector.SectorBlock? ==> v.Some?
  ensures sector.SectorBlock? ==> SizeOfV(v.value) <= IMM.BlockSize() as int - 32
  {
    match sector {
      case SectorIndirectionTable(mutMap) => {
        var table := mutMap.ToMap();
        // TODO(alattuada) extract to method
        var lbas := map k | k in table && table[k].0.Some? :: table[k].0.value;
        var graph := map k | k in table :: table[k].1;
        assert table == mutMap.Contents;
        ghost var indirectionTable := IM.IIndirectionTable(mutMap.Contents);
        assert lbas == indirectionTable.locs;
        assert graph == indirectionTable.graph;
        assert lbas.Keys == graph.Keys;
        if |lbas| < 0x1_0000_0000_0000_0000 / 8 {
          var w := lbasSuccsToVal(table);
          match w {
            case Some(v) => return Some(VCase(0, v));
            case None => return None;
          }
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
  ensures ISectorOpt(s) == IMM.parseSector(data[start..])
  ensures s.Some? && s.value.SectorBlock? ==> BT.WFNode(IM.INode(s.value.block))
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
  ensures s.Some? && s.value.SectorBlock? ==> BT.WFNode(IM.INode(s.value.block))
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
  requires sector.SectorBlock? ==> BT.WFNode(IM.INode(sector.block))
  requires sector.SectorBlock? ==> IMM.CappedNode(sector.block);
  ensures data != null ==> IMM.parseCheckedSector(data[..]) == ISectorOpt(Some(sector))
  ensures data != null ==> data.Length <= IMM.BlockSize() as int
  ensures data != null ==> 32 <= data.Length
  ensures data != null && sector.SectorIndirectionTable? ==> data.Length == IMM.BlockSize() as int
  ensures sector.SectorBlock? ==> data != null;
  {
    var v := sectorToVal(sector);
    match v {
      case None => return null;
      case Some(v) => {
        if (SizeOfV(v) <= IMM.BlockSize() as int - 32) {
          //Native.BenchmarkingUtil.start();
          var size: uint64;
          if (sector.SectorIndirectionTable?) {
            size := IMM.BlockSize();
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
