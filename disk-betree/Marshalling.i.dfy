include "../lib/Marshalling/GenericMarshalling.i.dfy"
include "PivotBetreeSpec.i.dfy"
include "Message.i.dfy"
include "ImplState.i.dfy"
include "KMTable.i.dfy"
include "../lib/Crypto.s.dfy"
include "../lib/Option.s.dfy"
include "../lib/MutableMap.i.dfy"

module Marshalling {
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

  import MM = MutableMap

  type Reference = BC.Reference
  type LBA = BC.LBA
  type Sector = ImplState.Sector
  type Message = M.Message
  type Key = BT.G.Key
  type Node = BT.G.Node

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

  // Disk block size
  function method BlockSize() : uint64 { 8 * 1024 * 1024 }

  // Limit on stuff for a node to be marshallable to disk.
  // (These are set so that when marshalled, the result
  // will fit on a disk block).
  function method CapNumBuckets() : uint64 { 8 }
  function method CapBucketNumEntries() : uint64 { 500 }
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

  function method MessageSize(msg: Message) : int
  {
    if msg.Define? then |msg.value| else 0
  }

  predicate method CappedBucket(kmt: KMTable.KMTable)
  {
    && |kmt.keys| <= CapBucketNumEntries() as int
    && (forall i | 0 <= i < |kmt.keys| :: |kmt.keys[i]| <= CapKeySize() as int)
    && (forall i | 0 <= i < |kmt.values| :: MessageSize(kmt.values[i]) <= CapValueSize() as int)
  }

  predicate method CappedBuckets(buckets: seq<KMTable.KMTable>)
  {
    forall i | 0 <= i < |buckets| :: CappedBucket(buckets[i])
  }

  predicate method CappedNode(node: ImplState.Node)
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

  method {:fuel ValInGrammar,3} ValToLBAsAndSuccs(a: seq<V>) returns (s : Option<ImplState.MutIndirectionTable>)
  requires valToLBAsAndSuccs.requires(a)
  ensures (
      && var table := ImplState.IIndirectionTableOpt(s);
      && var inter := valToLBAsAndSuccs(a);
      && if table.Some?
         then (inter.Some? && table.value.lbas == inter.value.0 && table.value.graph == inter.value.1)
         else inter.None?)
  ensures s.Some? ==> s.value.Inv()
  ensures s.Some? ==> s.value.Count as nat == |a|
  ensures s.Some? ==> s.value.Count as nat < 0x10000000000000000 / 8
  ensures s.Some? ==> fresh(s.value) && fresh(s.value.Repr)
  {
    if |a| == 0 {
      var newHashMap := new MM.ResizingHashMap<(Option<LBA>, seq<Reference>)>(1024); // TODO(alattuada) magic numbers
      s := Some(newHashMap);
      assume s.value.Count as nat == |a|;
    } else {
      var res := ValToLBAsAndSuccs(DropLast(a));
      match res {
        case Some(mutMap) => {
          var tuple := Last(a);
          var ref := valToReference(tuple.t[0]);
          var lba := valToLBA(tuple.t[1]);
          var succs := valToChildren(tuple.t[2]);
          match succs {
            case None => {
              s := None;
            }
            case Some(succs) => {
              var graphRef := mutMap.Get(ref);
              if graphRef.Some? || lba == 0 || !LBAType.ValidAddr(lba) {
                s := None;
              } else {
                var _ := mutMap.Insert(ref, (Some(lba), succs));
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

  function valToIndirectionTable(v: V) : (s : Option<BC.IndirectionTable>)
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

  method GraphClosed(table: ImplState.MutIndirectionTable) returns (result: bool)
    requires table.Inv()
    requires BC.GraphClosed.requires(ImplState.IIndirectionTable(table).graph)
    ensures BC.GraphClosed(ImplState.IIndirectionTable(table).graph) == result
  {
    var m := table.ToMap();
    var m' := map ref | ref in m :: m[ref].1;
    result := BC.GraphClosed(m');
  }

  method ValToIndirectionTable(v: V) returns (s : Option<ImplState.MutIndirectionTable>)
  requires valToIndirectionTable.requires(v)
  ensures ImplState.IIndirectionTableOpt(s) == valToIndirectionTable(v)
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

  function valToUint64Seq(v: V) : (s : seq<uint64>)
  requires ValInGrammar(v, GUint64Array)
  {
    v.ua
  }

  function method valToKeySeq(v: V) : (s : seq<Key>)
  requires ValidVal(v)
  requires ValInGrammar(v, GArray(GByteArray))
  ensures |s| == |v.a|
  decreases |v.a|
  {
    if |v.a| == 0 then [] else (
      assert ValInGrammar(Last(v.a), GByteArray);
      valToKeySeq(VArray(DropLast(v.a))) + [Last(v.a).b]
    )
  }

  function method {:fuel ValInGrammar,2} valToMessageSeq(v: V) : (s : seq<Message>)
  requires ValidVal(v)
  requires ValInGrammar(v, GArray(GByteArray))
  ensures forall i | 0 <= i < |s| :: s[i] != M.IdentityMessage()
  ensures |s| == |v.a|
  decreases |v.a|
  {
    if |v.a| == 0 then [] else (
      assert ValInGrammar(Last(v.a), GByteArray);
      valToMessageSeq(VArray(DropLast(v.a))) + [M.Define(Last(v.a).b)]
    )
  }

  function {:fuel ValInGrammar,2} valToBucket(v: V, pivotTable: seq<Key>, i: int) : (s : Option<map<Key, Message>>)
  requires ValidVal(v)
  requires ValInGrammar(v, BucketGrammar())
  requires Pivots.WFPivots(pivotTable)
  requires 0 <= i <= |pivotTable|
  {
    var keys := valToKeySeq(v.t[0]);
    var values := valToMessageSeq(v.t[1]);

    var kmt := KMTable.KMTable(keys, values);

    if KMTable.WF(kmt) && WFBucketAt(KMTable.I(kmt), pivotTable, i) && |keys| < KMTable.MaxNumKeys() as int then
      Some(KMTable.I(kmt))
    else
      None
  }

  function IKMTableOpt(table : Option<KMTable.KMTable>): Option<map<Key, Message>>
  requires table.Some? ==> KMTable.WF(table.value)
  {
    if table.Some? then
      Some(KMTable.I(table.value))
    else
      None
  }

  method ValToBucket(v: V, pivotTable: seq<Key>, i: int) returns (s : Option<KMTable.KMTable>)
  requires valToBucket.requires(v, pivotTable, i)
  ensures s.Some? ==> KMTable.WF(s.value)
  ensures s.Some? ==> KMTable.Bounded(s.value)
  ensures s.Some? ==> WFBucketAt(KMTable.I(s.value), pivotTable, i)
  ensures IKMTableOpt(s) == valToBucket(v, pivotTable, i)
  {
    assert ValidVal(v.t[0]);
    if (|v.t[0].a| as uint64 >= KMTable.MaxNumKeys()) {
      return None;
    }

    var keys := valToKeySeq(v.t[0]);
    var values := valToMessageSeq(v.t[1]);
    var kmt := KMTable.KMTable(keys, values);

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

  function valToBuckets(a: seq<V>, pivotTable: seq<Key>) : (s : Option<seq<map<Key, Message>>>)
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
            case Some(bucket) => Some(pref + [bucket])
            case None => None
          }
        )
      }
    )
  }

  lemma LemmaValToBucketNone(a: seq<V>, pivotTable: seq<Key>, i: int)
  requires Pivots.WFPivots(pivotTable)
  requires forall i | 0 <= i < |a| :: ValidVal(a[i])
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


  function ISeqKMTableOpt(s : Option<seq<KMTable.KMTable>>): Option<seq<map<Key, Message>>>
  requires s.Some? ==> forall i: nat :: i < |s.value| ==> KMTable.WF(s.value[i])
  {
    if s.Some? then
      Some(Apply(KMTable.I, s.value))
    else
      None
  }

  method ValToBuckets(a: seq<V>, pivotTable: seq<Key>) returns (s : Option<seq<KMTable.KMTable>>)
  requires valToBuckets.requires(a, pivotTable)
  ensures s.Some? ==> ImplState.WFBuckets(s.value)
  ensures ISeqKMTableOpt(s) == valToBuckets(a, pivotTable)
  {
    var ar := new KMTable.KMTable[|a|];

    var i := 0;
    while i < |a|
    invariant 0 <= i <= |a|
    invariant forall k: nat | k < i :: KMTable.WF(ar[k])
    invariant forall k: nat | k < i :: KMTable.Bounded(ar[k])
    invariant forall k: nat | k < i :: WFBucketAt(KMTable.I(ar[k]), pivotTable, k)
    invariant valToBuckets(a[..i], pivotTable).Some?
    invariant Apply(KMTable.I, ar[..i]) == valToBuckets(a[..i], pivotTable).value
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

    assert valToBuckets(a[..], pivotTable).Some?;
    assert Apply(KMTable.I, ar[..]) == valToBuckets(a, pivotTable).value;

    s := Some(ar[..]);
  }

  function {:fuel ValInGrammar,2} valToNode(v: V) : (s : Option<Node>)
  requires ValidVal(v)
  requires ValInGrammar(v, PivotNodeGrammar())
  ensures s.Some? ==> BT.WFNode(s.value)
  {
    match valToPivots(v.t[0].a) {
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
                  var node := BT.G.Node(pivots, if |children| == 0 then None else Some(children), buckets);
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

  function INodeOpt(s : Option<ImplState.Node>): Option<Node>
  requires s.Some? ==> ImplState.WFNode(s.value)
  {
    if s.Some? then
      Some(ImplState.INode(s.value))
    else
      None
  }

  method ValToNode(v: V) returns (s : Option<ImplState.Node>)
  requires valToNode.requires(v)
  ensures s.Some? ==> ImplState.WFNode(s.value)
  ensures INodeOpt(s) == valToNode(v)
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

    assert ValidVal(v.t[2]);
    var bucketsOpt := ValToBuckets(v.t[2].a, pivots);
    if (bucketsOpt.None?) {
      return None;
    }
    var buckets := bucketsOpt.value;

    var node := ImplState.Node(pivots, if |children| == 0 then None else childrenOpt, buckets);

    assert valToNode(v).Some?;
    assert ImplState.WFBuckets(node.buckets);
    assert ImplState.INode(node) == valToNode(v).value;
    return Some(node);
  }

  function valToSector(v: V) : (s : Option<BC.Sector>)
  requires ValidVal(v)
  requires ValInGrammar(v, SectorGrammar())
  {
    if v.c == 0 then (
      match valToIndirectionTable(v.val) {
        case Some(s) => Some(BC.SectorIndirectionTable(s))
        case None => None
      }
    ) else (
      match valToNode(v.val) {
        case Some(s) => Some(BC.SectorBlock(s))
        case None => None
      }
    )
  }

  function ISectorOpt(s : Option<ImplState.Sector>): Option<BC.Sector>
  requires s.Some? ==> ImplState.WFSector(s.value)
  reads if s.Some? && s.value.SectorIndirectionTable? then s.value.indirectionTable.Repr else {}
  {
    if s.Some? then
      Some(ImplState.ISector(s.value))
    else
      None
  }

  method ValToSector(v: V) returns (s : Option<ImplState.Sector>)
  requires valToSector.requires(v)
  ensures s.Some? ==> ImplState.WFSector(s.value)
  ensures ISectorOpt(s) == valToSector(v)
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
  requires |lbas| < 0x1_0000_0000_0000_0000 / 8
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

  method keySeqToVal(s: seq<Key>) returns (v : V)
  requires |s| <= CapBucketNumEntries() as int
  requires forall i | 0 <= i < |s| :: |s[i]| <= CapKeySize() as int
  ensures ValidVal(v)
  ensures ValInGrammar(v, GArray(GByteArray))
  ensures SizeOfV(v) <= 8 + (8 + CapKeySize()) as int * CapBucketNumEntries() as int
  ensures |v.a| == |s|
  ensures valToKeySeq(v) == s
  {
    var ar := new V[|s| as uint64];
    var i: uint64 := 0;
    while i < |s| as uint64
    invariant 0 <= i <= |s| as uint64
    invariant ValidVal(VArray(ar[..i]))
    invariant ValInGrammar(VArray(ar[..i]), GArray(GByteArray))
    invariant valToKeySeq(VArray(ar[..i])) == s[..i]
    invariant SizeOfV(VArray(ar[..i])) <= 8 + (8 + CapKeySize()) as int * i as int
    {
      ar[i] := VByteArray(s[i]);

      lemma_SeqSum_prefix(ar[..i], VByteArray(s[i]));
      assert s[..i+1][..i] == s[..i];
      assert ar[..i+1][..i] == ar[..i];
      assert ar[..i+1] == ar[..i] + [ar[i]];

      i := i + 1;
    }
    v := VArray(ar[..]);

    assert ar[..i] == ar[..];
  }

  method messageSeqToVal(s: seq<Message>) returns (v : V)
  requires |s| <= CapBucketNumEntries() as int
  requires forall i | 0 <= i < |s| :: s[i] != M.IdentityMessage()
  requires forall i | 0 <= i < |s| :: MessageSize(s[i]) <= CapValueSize() as int
  ensures ValidVal(v)
  ensures ValInGrammar(v, GArray(GByteArray))
  ensures SizeOfV(v) <= 8 + (8 + CapValueSize()) as int * CapBucketNumEntries() as int
  ensures |v.a| == |s|
  ensures valToMessageSeq(v) == s
  {
    var ar := new V[|s| as uint64];
    var i: uint64 := 0;
    while i < |s| as uint64
    invariant 0 <= i <= |s| as uint64
    invariant ValidVal(VArray(ar[..i]))
    invariant ValInGrammar(VArray(ar[..i]), GArray(GByteArray))
    invariant valToMessageSeq(VArray(ar[..i])) == s[..i]
    invariant SizeOfV(VArray(ar[..i])) <= 8 + (8 + CapValueSize()) as int * i as int
    {
      ar[i] := VByteArray(s[i].value);

      lemma_SeqSum_prefix(ar[..i], VByteArray(s[i].value));
      assert s[..i+1][..i] == s[..i];
      assert ar[..i+1][..i] == ar[..i];
      assert ar[..i+1] == ar[..i] + [ar[i]];

      i := i + 1;
    }
    v := VArray(ar[..]);

    assert ar[..i] == ar[..];
  }

  // We pass in pivotTable and i so we can state the pre- and post-conditions.
  method {:fuel SizeOfV,3}
  bucketToVal(bucket: KMTable.KMTable, ghost pivotTable: Pivots.PivotTable, ghost i: int) returns (v: V)
  requires Pivots.WFPivots(pivotTable)
  requires KMTable.WF(bucket)
  requires WFBucketAt(KMTable.I(bucket), pivotTable, i)
  requires CappedBucket(bucket)
  requires 0 <= i <= |pivotTable|
  ensures ValInGrammar(v, BucketGrammar())
  ensures SizeOfV(v) <= (8 + (8+CapKeySize() as int) * CapBucketNumEntries() as int) + (8 + (8+CapValueSize() as int) * CapBucketNumEntries() as int)
  ensures ValidVal(v)
  ensures valToBucket(v, pivotTable, i) == IKMTableOpt(Some(bucket))
  {
    var keys := keySeqToVal(bucket.keys);
    var values := messageSeqToVal(bucket.values);
    v := VTuple([keys, values]);

    // FIXME dafny goes nuts with trigger loops here some unknown reason
    // without these obvious asserts.
    assert ValInGrammar(v.t[0], BucketGrammar().t[0]);
    assert ValInGrammar(v.t[1], BucketGrammar().t[1]);
    assert ValInGrammar(v, BucketGrammar());
  }

  method bucketsToVal(buckets: seq<KMTable.KMTable>, ghost pivotTable: Pivots.PivotTable) returns (v: V)
  requires Pivots.WFPivots(pivotTable)
  requires forall i | 0 <= i < |buckets| :: KMTable.WF(buckets[i])
  requires forall i | 0 <= i < |buckets| :: WFBucketAt(KMTable.I(buckets[i]), pivotTable, i)
  requires CappedBuckets(buckets)
  requires |buckets| <= CapNumBuckets() as int
  requires |buckets| <= |pivotTable| + 1
  ensures ValidVal(v)
  ensures SizeOfV(v) <= 8 + |buckets| * ((8 + (8+CapKeySize()) as int * CapBucketNumEntries() as int) + (8 + (8+CapValueSize()) as int * CapBucketNumEntries() as int))
  ensures ValInGrammar(v, GArray(BucketGrammar()))
  ensures |v.a| == |buckets|
  ensures valToBuckets(v.a, pivotTable) == ISeqKMTableOpt(Some(buckets))
  {
    if |buckets| == 0 {
      return VArray([]);
    } else {
      var pref := bucketsToVal(DropLast(buckets), pivotTable);
      var bucket := Last(buckets);
      var bucketVal := bucketToVal(bucket, pivotTable, |buckets| - 1);
      assert buckets == DropLast(buckets) + [Last(buckets)]; // observe
      lemma_SeqSum_prefix(pref.a, bucketVal);
      assert valToBuckets(VArray(pref.a + [bucketVal]).a, pivotTable).Some?; // observe
      assert valToBuckets(VArray(pref.a + [bucketVal]).a, pivotTable).value == Apply(KMTable.I, buckets); // observe
      assert valToBuckets(VArray(pref.a + [bucketVal]).a, pivotTable) == ISeqKMTableOpt(Some(buckets)); // observe (reduces verification time)
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

  method {:fuel SizeOfV,4} nodeToVal(node: ImplState.Node) returns (v : V)
  requires ImplState.WFNode(node)
  requires BT.WFNode(ImplState.INode(node))
  requires CappedNode(node)
  ensures ValidVal(v)
  ensures SizeOfV(v) <= 
      8 + CapNumBuckets() as int * ((8 + (8+CapKeySize()) as int * CapBucketNumEntries() as int) + (8 + (8+CapValueSize()) as int * CapBucketNumEntries() as int)) +
      8 + (CapNumBuckets() as int - 1) * (8 + CapKeySize() as int) +
      8 + CapNumBuckets() as int * 8
  ensures ValInGrammar(v, PivotNodeGrammar())
  ensures valToNode(v) == INodeOpt(Some(node))
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
    assert valToNode(v).Some?;
    assert valToNode(v).value == ImplState.INode(node);
  }

  method sectorToVal(sector: ImplState.Sector) returns (v : Option<V>)
  requires ImplState.WFSector(sector)
  requires sector.SectorBlock? ==> BT.WFNode(ImplState.INode(sector.block))
  requires sector.SectorBlock? ==> CappedNode(sector.block);
  requires sector.SectorIndirectionTable? ==>
      BC.WFCompleteIndirectionTable(ImplState.IIndirectionTable(sector.indirectionTable))
  ensures v.Some? ==> ValidVal(v.value)
  ensures v.Some? ==> ValInGrammar(v.value, SectorGrammar());
  ensures v.Some? ==> valToSector(v.value) == ISectorOpt(Some(sector))
  ensures sector.SectorBlock? ==> v.Some?
  ensures sector.SectorBlock? ==> SizeOfV(v.value) <= BlockSize() as int - 32
  {
    match sector {
      case SectorIndirectionTable(mutMap) => {
        var table := mutMap.ToMap();
        // TODO(alattuada) extract to method
        var lbas := map k | k in table && table[k].0.Some? :: table[k].0.value;
        var graph := map k | k in table :: table[k].1;
        assert table == mutMap.Contents;
        ghost var indirectionTable := ImplState.IIndirectionTable(mutMap);
        assert lbas == indirectionTable.lbas;
        assert graph == indirectionTable.graph;
        assert lbas.Keys == graph.Keys;
        if |lbas| < 0x1_0000_0000_0000_0000 / 8 {
          var w := lbasSuccsToVal(lbas, graph);
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

  function {:opaque} parseSector(data: seq<byte>) : (s : Option<BC.Sector>)
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

  method ParseSector(data: array<byte>, start: uint64) returns (s : Option<Sector>)
  requires start as int <= data.Length < 0x1_0000_0000_0000_0000;
  ensures s.Some? ==> ImplState.WFSector(s.value)
  ensures ISectorOpt(s) == parseSector(data[start..])
  ensures s.Some? && s.value.SectorBlock? ==> BT.WFNode(ImplState.INode(s.value.block))
  {
    reveal_parseSector();
    var success, v, rest_index := ParseVal(data, start, SectorGrammar());
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
    GenericMarshalling.lemma_parse_Val_view_specific(data[..], val, grammar, start as int, (n as int));
    assert data[start..] == data[start..n];
  }

  /////// Marshalling and de-marshalling with checksums

  function {:opaque} parseCheckedSector(data: seq<byte>) : (s : Option<BC.Sector>)
  {
    if |data| >= 32 && Crypto.Sha256(data[32..]) == data[..32] then
      parseSector(data[32..])
    else
      None
  }

  method ParseCheckedSector(data: array<byte>) returns (s : Option<Sector>)
  requires data.Length < 0x1_0000_0000_0000_0000;
  ensures s.Some? ==> ImplState.WFSector(s.value)
  ensures ISectorOpt(s) == parseCheckedSector(data[..])
  ensures s.Some? && s.value.SectorBlock? ==> BT.WFNode(ImplState.INode(s.value.block))
  {
    s := None;

    if data.Length >= 32 {
      var hash := Crypto.Sha256(data[32..]);
      if hash == data[..32] {
        s := ParseSector(data, 32);
      }
    }

    reveal_parseCheckedSector();
  }

  method MarshallCheckedSector(sector: Sector) returns (data : array?<byte>)
  requires ImplState.WFSector(sector)
  requires sector.SectorBlock? ==> BT.WFNode(ImplState.INode(sector.block))
  requires sector.SectorBlock? ==> CappedNode(sector.block);
  ensures data != null ==> parseCheckedSector(data[..]) == ISectorOpt(Some(sector))
  ensures data != null ==> data.Length == BlockSize() as int
  ensures sector.SectorBlock? ==> data != null;
  {
    var v := sectorToVal(sector);
    match v {
      case None => return null;
      case Some(v) => {
        if (SizeOfV(v) <= BlockSize() as int - 32) {
          var data := MarshallIntoFixedSize(v, SectorGrammar(), 32, BlockSize());
          reveal_parseSector();
          reveal_parseCheckedSector();

          var hash := Crypto.Sha256(data[32..]);
          ghost var data_suffix := data[32..];
          Native.Arrays.CopySeqIntoArray(hash, 0, data, 0, 32);
          assert data_suffix == data[32..];

          /*ghost var data_seq := data[..];
          assert |data_seq| >= 32;
          assert Crypto.Sha256(data_seq[32..])
              == Crypto.Sha256(data[32..])
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
