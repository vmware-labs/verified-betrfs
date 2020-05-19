include "../lib/Marshalling/GenericMarshalling.i.dfy"
include "../PivotBetree/PivotBetreeSpec.i.dfy"
include "../lib/Base/Message.i.dfy"
include "../lib/Base/Crypto.s.dfy"
include "../lib/Base/Option.s.dfy"
include "../BlockCacheSystem/BlockCache.i.dfy"
include "../BlockCacheSystem/JournalCache.i.dfy"
include "../lib/Buckets/PackedKVMarshalling.i.dfy"

//
// Defines the interpretation of a sector of bytes as
// an abstract PivotBetree Node or a BlockCache IndirectionTable
//

module Marshalling {
  import opened GenericMarshalling
  import opened Options
  import opened NativeTypes
  import opened Sequences
  import opened BucketsLib
  import opened BucketWeights
  import BC = BlockCache
  import JC = JournalCache
  import BT = PivotBetreeSpec`Internal
  import M = ValueMessage`Internal
  import Pivots = PivotsLib
  import Keyspace = Lexicographic_Byte_Order
  import SeqComparison
  import opened Bounds
  import DiskLayout
  import ReferenceType`Internal
  import Crypto
  import PackedKV
  import opened SectorType
  import PackedKVMarshalling

  type Key = KeyType.Key
  type Reference = BC.Reference
  type Node = BT.G.Node

  /////// Grammar

  function method BucketGrammar() : G
  ensures ValidGrammar(BucketGrammar())
  {
    PackedKVMarshalling.grammar()
  }

  function method PivotTableGrammar() : G
    ensures ValidGrammar(PivotTableGrammar())
  {
    GArray(GByteArray)
  }
    
  function method PivotNodeGrammar() : G
  ensures ValidGrammar(PivotNodeGrammar())
  {
    GTuple([
        PivotTableGrammar(),
        GUint64Array, // children
        GArray(BucketGrammar()) 
    ])
  }

  function method IndirectionTableRowGrammar() : G
  {
    GTuple([GUint64, GUint64, GUint64, GUint64Array])
  }

  function method IndirectionTableGrammar() : G
  ensures ValidGrammar(IndirectionTableGrammar())
  {
    // (Reference, address, len, successor-list) triples
    GArray(IndirectionTableRowGrammar())
  }

  function method SuperblockGrammar() : G
  ensures ValidGrammar(SuperblockGrammar())
  {
    // counter
    // journalStart
    // journalLen,
    // indirectionTableLoc.addr
    // indirectionTableLoc.len
    GTuple([GUint64, GUint64, GUint64, GUint64, GUint64])
  }

  function method SectorGrammar() : G
  ensures ValidGrammar(SectorGrammar())
  {
    GTaggedUnion([
      SuperblockGrammar(),
      IndirectionTableGrammar(),
      PivotNodeGrammar()])    
  }

  /////// Conversion to PivotNode

  function pivotTableWeight(keys: seq<Key>) : nat
  {
    if |keys| == 0 then
      0
    else
      pivotTableWeight(DropLast(keys)) + SizeOfV(VUint64(0)) + |Last(keys)|
  }

  lemma pivotTableWeightUpperBound(keys: seq<Key>)
    ensures pivotTableWeight(keys) <= |keys| * (SizeOfV(VUint64(0)) + KeyType.MaxLen() as int)
  {
    // if |keys| == 0 {
    // } else {
    //   pivotTableWeightUpperBound(DropLast(keys));
    //   calc <= {
    //     pivotTableWeight(keys);
    //     pivotTableWeight(DropLast(keys)) + SizeOfV(VUint64(0)) + |Last(keys)|;
    //     (|keys| - 1) * (SizeOfV(VUint64(0)) + KeyType.MaxLen() as int) + SizeOfV(VUint64(0)) + |Last(keys)|;
    //     (|keys| - 1) * (SizeOfV(VUint64(0)) + KeyType.MaxLen() as int) + SizeOfV(VUint64(0)) + KeyType.MaxLen() as nat;
    //     |keys| * (SizeOfV(VUint64(0)) + KeyType.MaxLen() as int) - (SizeOfV(VUint64(0)) + KeyType.MaxLen() as int) + SizeOfV(VUint64(0)) + KeyType.MaxLen() as nat;
    //     |keys| * (SizeOfV(VUint64(0)) + KeyType.MaxLen() as int);
    //   }
    // }
      
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

  function keyValSeqToKeySeq(vs: seq<V>) : (result: Option<seq<Key>>)
    requires forall i | 0 <= i < |vs| :: ValidVal(vs[i])
    requires forall i | 0 <= i < |vs| :: ValInGrammar(vs[i], GByteArray)
    ensures result.Some? <==> (forall i | 0 <= i < |vs| :: |vs[i].b| <= KeyType.MaxLen() as int)
    ensures result.Some? ==> |result.value| == |vs|
    ensures result.Some? ==> (forall i | 0 <= i < |vs| :: result.value[i] == vs[i].b)
  {
    if |vs| == 0 then
      Some([])
    else (
      var prefix := keyValSeqToKeySeq(DropLast(vs));
      var last := Last(vs).b;
      if prefix.Some? && |last| <= KeyType.MaxLen() as int then (
        var klast: Key := last;
        Some(prefix.value + [ klast ])
      ) else
        None
    )
  }
  
  function valToStrictlySortedKeySeq(v: V) : (s : Option<seq<Key>>)
  requires ValidVal(v)
  requires ValInGrammar(v, PivotTableGrammar())
  ensures s.Some? ==> Keyspace.IsStrictlySorted(s.value)
  ensures s.Some? ==> |s.value| == |v.a|
  decreases |v.a|
  {
    var keys := keyValSeqToKeySeq(v.a);
    
    if keys.Some? && isStrictlySortedKeySeq(keys.value) then
      keys
    else
      None
  }

  function valToPivots(v: V) : (s : Option<seq<Key>>)
  requires ValidVal(v)
  requires ValInGrammar(v, PivotTableGrammar())
  ensures s.Some? ==> Pivots.WFPivots(s.value)
  ensures s.Some? ==> |s.value| == |v.a|
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

  function {:fuel ValInGrammar,2} valToBucket(v: V) : (s : Option<Bucket>)
  requires ValidVal(v)
  requires ValInGrammar(v, BucketGrammar())
  {
    var pkv := PackedKVMarshalling.fromVal(v);
    if pkv.Some? && PackedKV.WeightPkv(pkv.value) < Uint32UpperBound() as uint64 then
      Some(PackedKV.I(pkv.value))
    else
      None
  }

  function valToBuckets(a: seq<V>) : (s : Option<seq<Bucket>>)
  requires forall i | 0 <= i < |a| :: ValidVal(a[i])
  requires forall i | 0 <= i < |a| :: ValInGrammar(a[i], BucketGrammar())
  ensures s.Some? <==> (forall i | 0 <= i < |a| :: valToBucket(a[i]).Some?)
  ensures s.Some? ==> |s.value| == |a|
  ensures s.Some? ==> forall i | 0 <= i < |s.value| :: WFBucket(s.value[i])
  {
    if |a| == 0 then
      Some([])
    else (
      var pref := valToBuckets(DropLast(a));
      var bucket := valToBucket(Last(a));
      if pref.Some? && bucket.Some? then
        Some(pref.value + [bucket.value])
      else
        None
    )
  }

  function method valToChildren(v: V) : Option<seq<Reference>>
  requires ValInGrammar(v, GUint64Array)
  {
    Some(v.ua)
  }

  function {:fuel ValInGrammar,2} valToNode(v: V) : (s : Option<Node>)
  requires ValidVal(v)
  requires ValInGrammar(v, PivotNodeGrammar())
  // Pivots.NumBuckets(node.pivotTable) == |node.buckets|
  ensures s.Some? ==> BT.WFNode(s.value)
  {
    assert ValidVal(v.t[0]);
    assert ValidVal(v.t[1]);
    assert ValidVal(v.t[2]);
    var pivots_len := |v.t[0].a| as uint64;
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
              var buckets := valToBuckets(v.t[2].a);
              if buckets.Some? && WeightBucketList(buckets.value) <= MaxTotalBucketWeight() then (
                var node := BT.G.Node(
                  pivots,
                  if |children| == 0 then None else Some(children),
                  buckets.value);
                Some(node)
              ) else (
                None
              )
            )
          }
        )
      }
    ) else (
      None
    )
  }

  function {:fuel ValInGrammar,3} valToIndirectionTableMaps(a: seq<V>) : (s : Option<IndirectionTable>)
  requires |a| <= IndirectionTableMaxSize()
  requires forall i | 0 <= i < |a| :: ValidVal(a[i])
  requires forall i | 0 <= i < |a| :: ValInGrammar(a[i], GTuple([GUint64, GUint64, GUint64, GUint64Array]))
  ensures s.Some? ==> |s.value.graph| as int == |a|
  ensures s.Some? ==> s.value.graph.Keys == s.value.locs.Keys
  ensures s.Some? ==> forall v | v in s.value.locs.Values :: DiskLayout.ValidNodeLocation(v)
  ensures s.Some? ==> forall ref | ref in s.value.graph :: |s.value.graph[ref]| <= MaxNumChildren()
  {
    if |a| == 0 then
      Some(IndirectionTable(map[], map[]))
    else (
      var res := valToIndirectionTableMaps(DropLast(a));
      match res {
        case Some(table) => (
          var tuple := Last(a);
          var ref := tuple.t[0].u;
          var addr := tuple.t[1].u;
          var len := tuple.t[2].u;
          var succs := tuple.t[3].ua;
          var loc := DiskLayout.Location(addr, len);
          if ref in table.graph || !DiskLayout.ValidNodeLocation(loc) || |succs| as int > MaxNumChildren() then (
            None
          ) else (
            Some(IndirectionTable(table.locs[ref := loc], table.graph[ref := succs]))
          )
        )
        case None => None
      }
    )
  }

  function valToIndirectionTable(v: V) : (s : Option<IndirectionTable>)
  requires ValidVal(v)
  requires ValInGrammar(v, IndirectionTableGrammar())
  ensures s.Some? ==> BC.WFCompleteIndirectionTable(s.value)
  {
    if |v.a| <= IndirectionTableMaxSize() then (
      var t := valToIndirectionTableMaps(v.a);
      match t {
        case Some(res) => (
          if BT.G.Root() in res.graph && BC.GraphClosed(res.graph) then (
            Some(res)
          ) else (
            None
          )
        )
        case None => None
      }
    ) else (
      None
    )
  }

  function method valToSuperblock(v: V) : (s: Option<Superblock>)
  requires ValidVal(v)
  requires ValInGrammar(v, SuperblockGrammar())
  {
    assert ValInGrammar(v.t[0], GUint64);
    assert ValInGrammar(v.t[1], GUint64);
    assert ValInGrammar(v.t[2], GUint64);
    assert ValInGrammar(v.t[3], GUint64);
    assert ValInGrammar(v.t[4], GUint64);

    var counter := v.t[0].u;
    var journalStart := v.t[1].u;
    var journalLen := v.t[2].u;
    var itlocAddr := v.t[3].u;
    var itlocLen := v.t[4].u;
    var sup := Superblock(counter, journalStart, journalLen,
        DiskLayout.Location(itlocAddr, itlocLen));
    if JC.WFSuperblock(sup) then
      Some(sup)
    else
      None
  }

  function valToSector(v: V) : (s : Option<Sector>)
  requires ValidVal(v)
  requires ValInGrammar(v, SectorGrammar())
  {
    if v.c == 0 then (
      match valToSuperblock(v.val) {
        case Some(s) => Some(SectorSuperblock(s))
        case None => None
      }
    ) else if v.c == 1 then (
      match valToIndirectionTable(v.val) {
        case Some(s) => Some(SectorIndirectionTable(s))
        case None => None
      }
    ) else (
      match valToNode(v.val) {
        case Some(s) => Some(SectorNode(s))
        case None => None
      }
    )
  }

  /////// Marshalling and de-marshalling

  function {:opaque} parseSector(data: seq<byte>) : (s : Option<Sector>)
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

  function {:opaque} parseCheckedSector(data: seq<byte>) : (s : Option<Sector>)
  {
    if |data| >= 32 && Crypto.Crc32C(data[32..]) == data[..32] then
      parseSector(data[32..])
    else
      None
  }

  /////// Lemmas

  lemma singleMapRemove1<K,V>(m0: map<K, V>, m: map<K, V>, k: K, v: V)
  requires m == m0[k := v];
  requires k !in m0;
  requires m.Keys == {k};
  ensures m0 == map[];
  {
    assert m0.Keys <= m.Keys;
  }

  predicate IsInitIndirectionTable(table: IndirectionTable)
  {
    && BC.WFCompleteIndirectionTable(table)
    && table.graph.Keys == {BT.G.Root()}
    && table.graph[BT.G.Root()] == []
  }

  lemma
    {:fuel valToIndirectionTableMaps,4}
    {:fuel ValidVal,10}
    {:fuel ValInGrammar,10}
    {:fuel SizeOfV,10}
    {:fuel SeqSum,10}
  InitIndirectionTableSizeOfV(table: IndirectionTable, v: V)
  requires IsInitIndirectionTable(table)
  requires ValidVal(v)
  requires ValInGrammar(v, SectorGrammar())
  requires valToSector(v) == Some(SectorIndirectionTable(table))
  ensures SizeOfV(v) == 48
  {
    var ref := BT.G.Root();
    var loc := table.locs[BT.G.Root()];
    //assert table.locs.Keys == {BT.G.Root()};

    //assert v.c == 0;
    //assert valToIndirectionTable(v.val) == Some(table);

    //assert valToIndirectionTableMaps(v.val.a) == Some(table);

    assert ValInGrammar(Last(v.val.a), GTuple([GUint64, GUint64, GUint64, GUint64Array]));

    assert Last(v.val.a).t[0].u in table.graph;

    assert ref == Last(v.val.a).t[0].u;
    assert loc.addr == Last(v.val.a).t[1].u;
    assert loc.len == Last(v.val.a).t[2].u;
    assert [] == Last(v.val.a).t[3].ua;

    var locs1 := valToIndirectionTableMaps(DropLast(v.val.a)).value.locs;
    singleMapRemove1(locs1, table.locs, ref, loc);

    assert valToIndirectionTableMaps(DropLast(v.val.a)).value.graph == map[];

    //assert valToIndirectionTableMaps(DropLast(v.val.a))
    //    == Some(IndirectionTable(map[], map[]));

    assert DropLast(v.val.a) == [];

    assert v.val.a[0] == VTuple([
        VUint64(BT.G.Root()),
        VUint64(loc.addr),
        VUint64(loc.len),
        VUint64Array([])]);

    assert v == VCase(1, VArray([
      VTuple([
        VUint64(BT.G.Root()),
        VUint64(loc.addr),
        VUint64(loc.len),
        VUint64Array([])])
    ]));

    reveal_SeqSum();
    /*assert SizeOfV(VTuple([
        VUint64(BT.G.Root()),
        VUint64(loc.addr),
        VUint64(loc.len),
        VUint64Array([])])) == 32;*/
  }
}
