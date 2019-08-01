include "../lib/Marshalling/GenericMarshalling.i.dfy"
include "PivotBetreeSpec.dfy"
include "Message.dfy"
include "ImplState.dfy"
include "SSTable.dfy"
include "../lib/Option.dfy"

module Marshalling {
  import opened GenericMarshalling
  import opened Options
  import opened NativeTypes
  import opened Sequences
  import opened Maps
  import opened BucketsLib
  import BC = BetreeGraphBlockCache
  import ImplState
  import SSTable

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
  type Sector = ImplState.Sector
  type Message = M.Message
  type Key = BT.G.Key
  type Node = ImplState.Node

  /////// Grammar

  function method IndirectionTableGrammar() : G
  ensures ValidGrammar(IndirectionTableGrammar())
  {
    // (Reference, LBA, successor-list) triples
    GArray(GTuple([GUint64, GUint64, GUint64Array]))
  }

  function method BucketGrammar() : G
  ensures ValidGrammar(BucketGrammar())
  {
    GTuple([
      GUint64Array,
      GByteArray
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

  // Disk block size
  function method BlockSize() : uint64 { 8 * 1024 * 1024 }

  // Limit on stuff for a node to be marshallable to disk.
  // (These are set so that when marshalled, the result
  // will fit on a disk block).
  function method CapNumBuckets() : uint64 { 8 }
  function method CapBucketSize() : uint64 { 1_000_000 }
  function method CapBucketNumEntries() : uint64 { 4000 }
  function method CapKeySize() : uint64 { 1024 }
  function method CapValueSize() : uint64 { 1024 }

  predicate method CappedKey(key: Key) {
    |key| <= CapKeySize() as int
  }

  predicate method CappedMessage(msg: Message)
  requires msg != M.IdentityMessage()
  {
    |msg.value| <= CapValueSize() as int
  }

  predicate method CappedPivotTable(pivots: seq<Key>)
  {
    forall i | 0 <= i < |pivots| :: CappedKey(pivots[i])
  }

  predicate method CappedBucket(sst: SSTable.SSTable)
  {
    && |sst.starts| <= CapBucketNumEntries() as int
    && |sst.strings| <= CapBucketSize() as int
  }

  predicate method CappedBuckets(buckets: seq<SSTable.SSTable>)
  {
    forall i | 0 <= i < |buckets| :: CappedBucket(buckets[i])
  }

  predicate method CappedNode(node: Node)
  requires ImplState.WFNode(node)
  {
    && |node.buckets| <= CapNumBuckets() as int
    && CappedPivotTable(node.pivotTable)
    && CappedBuckets(node.buckets)
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

  function method {:fuel ValInGrammar,3} valToLBAsAndSuccs(a: seq<V>) : (s : Option<(map<Reference, LBA>, map<Reference, seq<Reference>>)>)
  requires forall i | 0 <= i < |a| :: ValInGrammar(a[i], GTuple([GUint64, GUint64, GUint64Array]))
  ensures s.Some? ==> forall lba | lba in s.value.0.Values :: BC.ValidLBAForNode(lba)
  ensures s.Some? ==> s.value.0.Keys == s.value.1.Keys
  {
    if |a| == 0 then
      Some((map[], map[]))
    else (
      var res := valToLBAsAndSuccs(DropLast(a));
      match res {
        case Some((lbas, graph)) => (
          var tuple := Last(a);
          var ref := valToReference(tuple.t[0]);
          var lba := valToLBA(tuple.t[1]);
          var succs := valToChildren(tuple.t[2]);
          match succs {
            case None => None
            case Some(succs) => (
              if ref in graph || lba == 0 || !LBAType.ValidAddr(lba) then (
                None
              ) else (
                Some((lbas[ref := lba], graph[ref := succs]))
              )
            )
          }
        )
        case None => None
      }
    )
  }

  function method valToIndirectionTable(v: V) : (s : Option<BC.IndirectionTable>)
  requires ValInGrammar(v, IndirectionTableGrammar())
  ensures s.Some? ==> BC.WFCompleteIndirectionTable(s.value)
  {
    var res := valToLBAsAndSuccs(v.a);
    match res {
      case Some(res) => (
        if BT.G.Root() in res.1 && BC.GraphClosed(res.1) then (
          Some(BC.IndirectionTable(res.0, res.1))
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

  function {:fuel ValInGrammar,2} valToBucket(v: V, pivotTable: seq<Key>, i: int) : (s : Option<SSTable.SSTable>)
  requires ValInGrammar(v, BucketGrammar())
  requires Pivots.WFPivots(pivotTable)
  requires 0 <= i <= |pivotTable|
  ensures s.Some? ==> SSTable.WFSSTableMap(s.value)
  ensures s.Some? ==> WFBucketAt(SSTable.I(s.value), pivotTable, i)
  {
    var starts := valToUint64Seq(v.t[0]);

    var strings := v.t[1].b;
    var sst := SSTable.SSTable(starts, strings);

    if SSTable.WFSSTableMap(sst) && WFBucketAt(SSTable.I(sst), pivotTable, i) then
      Some(sst)
    else
      None
  }

  method ValToBucket(v: V, pivotTable: seq<Key>, i: int) returns (s : Option<SSTable.SSTable>)
  requires valToBucket.requires(v, pivotTable, i)
  ensures s == valToBucket(v, pivotTable, i)
  {
    var starts := v.t[0].ua;

    var strings := v.t[1].b;
    var sst := SSTable.SSTable(starts, strings);

    var wf := SSTable.IsWFSSTableMap(sst);
    if !wf {
      return None;
    }

    // Check that it fits in the desired bucket
    if |sst.starts| > 0 {
      if i > 0 {
        var c := SSTable.Cmp(pivotTable[i-1], sst, 0);
        if (c == 1) {
          assert SSTable.SSTKeyMapsToValueAt(SSTable.I(sst), sst, 0);
          //assert !WFBucketAt(SSTable.I(sst), pivotTable, i);

          return None;
        }
      }

      if i < |pivotTable| {
        var c := SSTable.Cmp(pivotTable[i], sst, |sst.starts| as uint64 - 2);
        if (c != 1) {
          assert SSTable.SSTKeyMapsToValueAt(SSTable.I(sst), sst, |sst.starts| / 2 - 1);
          //assert !WFBucketAt(SSTable.I(sst), pivotTable, i);

          return None;
        }
      }
    }

    forall key | key in SSTable.I(sst)
    ensures Pivots.Route(pivotTable, key) == i
    ensures SSTable.I(sst)[key] != M.IdentityMessage()
    {
      var j :| 0 <= 2*j < |sst.starts| && SSTable.Entry(sst, 2*j) == key;
      assert SSTable.SSTKeyMapsToValueAt(SSTable.I(sst), sst, j);
      if |sst.starts| > 0 {
        SSTable.KeysStrictlySortedImpliesLte(sst, 0, j);
        SSTable.KeysStrictlySortedImpliesLte(sst, j, |sst.starts| / 2 - 1);
      }
      Pivots.RouteIs(pivotTable, key, i);
    }

    assert WFBucketAt(SSTable.I(sst), pivotTable, i);
    s := Some(sst);
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

  function valToBuckets(a: seq<V>, pivotTable: seq<Key>) : (s : Option<seq<SSTable.SSTable>>)
  requires Pivots.WFPivots(pivotTable)
  requires forall i | 0 <= i < |a| :: ValInGrammar(a[i], BucketGrammar())
  requires |a| <= |pivotTable| + 1
  ensures s.Some? ==> |s.value| == |a|
  ensures s.Some? ==> forall i | 0 <= i < |s.value| :: SSTable.WFSSTableMap(s.value[i])
  ensures s.Some? ==> forall i | 0 <= i < |s.value| :: WFBucketAt(SSTable.I(s.value[i]), pivotTable, i)
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

  lemma LemmaValToBucketNone(a: seq<V>, pivotTable: seq<Key>, i: int)
  requires Pivots.WFPivots(pivotTable)
  requires forall i | 0 <= i < |a| :: ValInGrammar(a[i], BucketGrammar())
  requires |a| <= |pivotTable| + 1
  requires 0 <= i < |a|
  requires valToBucket(a[i], pivotTable, i) == None
  ensures valToBuckets(a, pivotTable) == None
  {
    if (|a| == i + 1) {
    } else {
      LemmaValToBucketNone(DropLast(a), pivotTable, i);
    }
  }

  method ValToBuckets(a: seq<V>, pivotTable: seq<Key>) returns (s : Option<seq<SSTable.SSTable>>)
  requires valToBuckets.requires(a, pivotTable)
  ensures s == valToBuckets(a, pivotTable)
  {
    var ar := new SSTable.SSTable[|a|];

    var i := 0;
    while i < |a|
    invariant 0 <= i <= |a|
    invariant Some(ar[..i]) == valToBuckets(a[..i], pivotTable)
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
    s := Some(ar[..]);
  }

  function {:fuel ValInGrammar,2} valToNode(v: V) : (s : Option<Node>)
  requires ValInGrammar(v, PivotNodeGrammar())
  ensures s.Some? ==> ImplState.WFNode(s.value)
  ensures s.Some? ==> BT.WFNode(ImplState.INode(s.value))
  {
    match valToPivots(v.t[0].a) {
      case None => None
      case Some(pivots) => (
        match valToChildren(v.t[1]) {
          case None => None
          case Some(children) => (
            if ((|children| == 0 || |children| == |pivots| + 1) && |v.t[2].a| == |pivots| + 1) then (
              match valToBuckets(v.t[2].a, pivots) {
                case None => None
                case Some(buckets) => (
                  var node := ImplState.Node(pivots, if |children| == 0 then None else Some(children), buckets);
                  Some(node)
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

  method ValToNode(v: V) returns (s : Option<Node>)
  requires valToNode.requires(v)
  ensures s == valToNode(v)
  {
    var pivotsOpt := valToPivots(v.t[0].a);
    if (pivotsOpt.None?) {
      return None;
    }
    var pivots := pivotsOpt.value;

    var childrenOpt := valToChildren(v.t[1]);
    if (childrenOpt.None?) {
      return None;
    }
    var children := childrenOpt.value;

    if (!((|children| == 0 || |children| == |pivots| + 1) && |v.t[2].a| == |pivots| + 1)) {
      return None;
    }

    var bucketsOpt := ValToBuckets(v.t[2].a, pivots);
    if (bucketsOpt.None?) {
      return None;
    }
    var buckets := bucketsOpt.value;

    var node := ImplState.Node(pivots, if |children| == 0 then None else childrenOpt, buckets);
    return Some(node);
  }

  function valToSector(v: V) : (s : Option<Sector>)
  requires ValInGrammar(v, SectorGrammar())
  ensures s.Some? ==> ImplState.WFSector(s.value)
  {
    if v.c == 0 then (
      match valToIndirectionTable(v.val) {
        case Some(s) => Some(ImplState.SectorIndirectionTable(s))
        case None => None
      }
    ) else (
      match valToNode(v.val) {
        case Some(s) => Some(ImplState.SectorBlock(s))
        case None => None
      }
    )
  }

  method ValToSector(v: V) returns (s : Option<Sector>)
  requires valToSector.requires(v)
  ensures s == valToSector(v)
  {
    if v.c == 0 {
      match valToIndirectionTable(v.val) {
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

  method childrenToVal(children: seq<Reference>) returns (v : V)
  requires |children| < 0x1_0000_0000_0000_0000
  ensures ValidVal(v)
  ensures SizeOfV(v) <= 8 + |children| * 8
  ensures ValInGrammar(v, GUint64Array)
  ensures valToChildren(v) == Some(children)
  ensures |v.ua| == |children|
  {
    return VUint64Array(children);
  }

  method {:fuel ValInGrammar,2} lbasSuccsToVal(lbas: map<Reference, LBA>, graph: map<Reference, seq<Reference>>) returns (v: Option<V>)
  requires lbas.Keys == graph.Keys
  requires forall lba | lba in lbas.Values :: BC.ValidLBAForNode(lba)
  requires |lbas| < 0x1_0000_0000_0000_0000
  ensures v.Some? ==> ValidVal(v.value)
  ensures v.Some? ==> ValInGrammar(v.value, IndirectionTableGrammar());
  ensures v.Some? ==> |v.value.a| == |lbas|
  ensures v.Some? ==> valToLBAsAndSuccs(v.value.a) == Some((lbas, graph));
  {
    if (|lbas| == 0) {
      assert lbas == map[];
      assert graph == map[];
      return Some(VArray([]));
    } else {
      var ref :| ref in lbas.Keys;
      var vpref := lbasSuccsToVal(MapRemove(lbas, {ref}), MapRemove(graph, {ref}));
      match vpref {
        case None => return None;
        case Some(vpref) => {
          var lba := lbas[ref];
          if (|graph[ref]| >= 0x1_0000_0000_0000_0000) {
            return None;
          }
          var succs := childrenToVal(graph[ref]);
          var tuple := VTuple([refToVal(ref), lbaToVal(lba), succs]);

          assert MapRemove(lbas, {ref})[ref := lba] == lbas;
          assert MapRemove(graph, {ref})[ref := graph[ref]] == graph;

          //assert ref == valToReference(tuple.t[0]);
          //assert lba == valToReference(tuple.t[1]);
          //assert !(ref in MapRemove(graph, {ref}));
          assert BC.ValidLBAForNode(lba);
          //assert !(lba == 0);
          //assert valToLBAsAndSuccs(vpref.a + [tuple]) == Some((lbas, graph));

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
  ensures valToUint64Seq(v) == a
  {
    return VUint64Array(a);
  }

  // We pass in pivotTable and i so we can state the pre- and post-conditions.
  method {:fuel ValInGrammar,2} {:fuel SizeOfV,3} bucketToVal(bucket: SSTable.SSTable, ghost pivotTable: Pivots.PivotTable, ghost i: int) returns (v: V)
  requires Pivots.WFPivots(pivotTable)
  requires SSTable.WFSSTableMap(bucket)
  requires WFBucketAt(SSTable.I(bucket), pivotTable, i)
  requires CappedBucket(bucket)
  requires 0 <= i <= |pivotTable|
  ensures ValInGrammar(v, BucketGrammar())
  ensures SizeOfV(v) <= 8 + CapBucketNumEntries() as int * 8 + 8 + CapBucketSize() as int
  ensures ValidVal(v)
  ensures valToBucket(v, pivotTable, i) == Some(bucket)
  {
    var vstarts := uint64ArrayToVal(bucket.starts);
    return VTuple([
      vstarts,
      VByteArray(bucket.strings)
    ]);
  }

  method bucketsToVal(buckets: seq<SSTable.SSTable>, ghost pivotTable: Pivots.PivotTable) returns (v: V)
  requires Pivots.WFPivots(pivotTable)
  requires forall i | 0 <= i < |buckets| :: SSTable.WFSSTableMap(buckets[i])
  requires forall i | 0 <= i < |buckets| :: WFBucketAt(SSTable.I(buckets[i]), pivotTable, i)
  requires CappedBuckets(buckets)
  requires |buckets| <= CapNumBuckets() as int
  requires |buckets| <= |pivotTable| + 1
  ensures ValidVal(v)
  ensures SizeOfV(v) <= 8 + |buckets| * (8 + CapBucketNumEntries() as int * 8 + 8 + CapBucketSize() as int)
  ensures ValInGrammar(v, GArray(BucketGrammar()))
  ensures |v.a| == |buckets|
  ensures valToBuckets(v.a, pivotTable) == Some(buckets)
  {
    if |buckets| == 0 {
      return VArray([]);
    } else {
      var pref := bucketsToVal(DropLast(buckets), pivotTable);
      var bucket := Last(buckets);
      var bucketVal := bucketToVal(bucket, pivotTable, |buckets| - 1);
      assert buckets == DropLast(buckets) + [Last(buckets)]; // observe
      lemma_SeqSum_prefix(pref.a, bucketVal);
      return VArray(pref.a + [bucketVal]);
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

  lemma lastPivotWf(pivots': seq<Key>, key: Key)
  requires Pivots.WFPivots(pivots' + [key])
  ensures |key| != 0
  ensures |pivots'| > 0 ==> Keyspace.lt(Last(pivots'), key)
  {
    var pivots := pivots' + [key];
    KeyInPivotsIsNonempty(pivots, key);
    assert |key| != 0;
    if |pivots'| > 0 {
      Keyspace.IsStrictlySortedImpliesLt(pivots, |pivots| - 2, |pivots| - 1);
      assert Keyspace.lt(Last(pivots'), key);
    }
  }

  method pivotsToVal(pivots: seq<Key>) returns (v : V)
  requires Pivots.WFPivots(pivots)
  requires CappedPivotTable(pivots)
  requires |pivots| <= CapNumBuckets() as int - 1
  ensures ValidVal(v)
  ensures SizeOfV(v) <= 8 + |pivots| * (8 + CapKeySize() as int)
  ensures ValInGrammar(v, GArray(GByteArray))
  ensures |v.a| == |pivots|
  ensures valToPivots(v.a) == Some(pivots)
  {
    if |pivots| == 0 {
      return VArray([]);
    } else {
      var pivots' := DropLast(pivots);
      Keyspace.StrictlySortedPop(pivots);
      var pref := pivotsToVal(pivots');

      var key := Last(pivots);

      var last := VByteArray(key);
      assert ValidVal(last); // observe

      assert pivots == DropLast(pivots) + [key];
      lastPivotWf(pivots', key);

      lemma_SeqSum_prefix(pref.a, last);
      return VArray(pref.a + [last]);
    }
  }

  method {:fuel SizeOfV,4} nodeToVal(node: Node) returns (v : V)
  requires ImplState.WFNode(node)
  requires BT.WFNode(ImplState.INode(node))
  requires CappedNode(node)
  ensures ValidVal(v)
  ensures SizeOfV(v) <= 
      8 + CapNumBuckets() as int * (8 + CapBucketNumEntries() as int * 8 + 8 + CapBucketSize() as int) +
      8 + (CapNumBuckets() as int - 1) * (8 + CapKeySize() as int) +
      8 + CapNumBuckets() as int * 8
  ensures ValInGrammar(v, PivotNodeGrammar())
  ensures valToNode(v) == Some(node)
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
  }

  method sectorToVal(sector: Sector) returns (v : Option<V>)
  requires ImplState.WFSector(sector)
  requires sector.SectorBlock? ==> BT.WFNode(ImplState.INode(sector.block))
  requires sector.SectorBlock? ==> CappedNode(sector.block);
  ensures v.Some? ==> ValidVal(v.value)
  ensures v.Some? ==> ValInGrammar(v.value, SectorGrammar());
  ensures v.Some? ==> valToSector(v.value) == Some(sector)
  ensures sector.SectorBlock? ==> v.Some?
  ensures sector.SectorBlock? ==> SizeOfV(v.value) <= BlockSize() as int
  {
    match sector {
      case SectorIndirectionTable(IndirectionTable(lbas, succs)) => {
        if |lbas| < 0x1_0000_0000_0000_0000 {
          var w := lbasSuccsToVal(lbas, succs);
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

  function {:opaque} parseSector(data: seq<byte>) : (s : Option<Sector>)
  ensures s.Some? ==> ImplState.WFSector(s.value)
  ensures s.Some? && s.value.SectorBlock? ==> BT.WFNode(ImplState.INode(s.value.block))
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
  ensures s == parseSector(data[..])
  ensures s.Some? ==> ImplState.WFSector(s.value)
  ensures s.Some? && s.value.SectorBlock? ==> BT.WFNode(ImplState.INode(s.value.block))
  {
    reveal_parseSector();
    var success, v, rest_index := ParseVal(data, 0, SectorGrammar());
    if success {
      var s := ValToSector(v);
      return s;
    } else {
      return None;
    }
  }

  method MarshallIntoFixedSize(val:V, grammar:G, n: uint64) returns (data:array<byte>)
    requires ValidGrammar(grammar);
    requires ValInGrammar(val, grammar);
    requires ValidVal(val);
    requires 0 <= SizeOfV(val) <= n as int
    ensures fresh(data);
    ensures |data[..]| == n as int
    ensures parse_Val(data[..], grammar).0.Some? && parse_Val(data[..], grammar).0.value == val;
  {
    data := new byte[n];
    var computed_size := GenericMarshalling.MarshallVal(val, grammar, data, 0);
    GenericMarshalling.lemma_parse_Val_view_specific(data[..], val, grammar, 0, (n as int));
    assert data[..] == data[0..n];
  }

  method MarshallSector(sector: Sector) returns (data : array?<byte>)
  requires ImplState.WFSector(sector)
  requires sector.SectorBlock? ==> BT.WFNode(ImplState.INode(sector.block))
  requires sector.SectorBlock? ==> CappedNode(sector.block);
  ensures data != null ==> parseSector(data[..]) == Some(sector)
  ensures data != null ==> data.Length == BlockSize() as int
  ensures sector.SectorBlock? ==> data != null;
  {
    var v := sectorToVal(sector);
    match v {
      case None => return null;
      case Some(v) => {
        if (SizeOfV(v) <= BlockSize() as int) {
          var data := MarshallIntoFixedSize(v, SectorGrammar(), BlockSize());
          reveal_parseSector();
          return data;
        } else {
          return null;
        }
      }
    }
  }

}
