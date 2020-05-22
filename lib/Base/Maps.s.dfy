// TODO most of this doesn't need to be .s

// TODO(rob): Split into Maps and IMaps

include "Option.s.dfy"

module {:extern} Maps {
  import opened Options
    
  predicate IMapsTo<K,V>(m: imap<K, V>, k: K, v: V) {
    k in m && m[k] == v
  }
  
  predicate MapsTo<K,V>(m: map<K, V>, k: K, v: V) {
    k in m && m[k] == v
  }

  predicate MapsAgreeOnKey<K,V>(m: map<K,V>, m': map<K,V>, k: K) {
    (k !in m && k !in m') || (k in m && k in m' && m[k] == m'[k])
  }

  predicate IMapsAgreeOnKey<K,V>(m: imap<K,V>, m': imap<K,V>, k: K) {
    (k !in m && k !in m') || (k in m && k in m' && m[k] == m'[k])
  }

  predicate IsSubIMap<K,V>(sub: imap<K,V>, sup: imap<K,V>) {
    && sub.Keys <= sup.Keys
    && (forall key :: key in sub.Keys ==> IMapsAgreeOnKey(sub, sup, key))
  }

  predicate IsSubMap<K,V>(sub: map<K,V>, sup: map<K,V>) {
    && sub.Keys <= sup.Keys
    && (forall key :: key in sub.Keys ==> MapsAgreeOnKey(sub, sup, key))
  }

  function {:opaque} MapRemove<K,V>(m:map<K,V>, ks:set<K>) : (m':map<K,V>)
    ensures forall k :: k in m && k !in ks ==> k in m'
    ensures forall k :: k in m' ==> k in m && k !in ks
    ensures forall j :: j in m' ==> m'[j] == m[j]
    ensures |m'.Keys| <= |m.Keys|
    ensures |m'| <= |m|
  {
    var m':= map j | j in m && j !in ks :: m[j];
    assert m'.Keys == m.Keys - ks;
    m'
  }
  
  function {:opaque} MapRemoveStrong<K,V>(m:map<K,V>, ks:set<K>) : (m':map<K,V>)
    ensures m'.Keys == m.Keys - ks
    ensures forall j :: j in m' ==> m'[j] == m[j]
    ensures |m'.Keys| <= |m.Keys|
    ensures |m'| <= |m|
  {
    reveal_MapRemove();
    MapRemove(m, ks)
  }
 
  function {:opaque} MapRemove1<K,V>(m:map<K,V>, k:K) : (m':map<K,V>)
    ensures forall j :: j in m && j != k ==> j in m'
    ensures forall j :: j in m' ==> j in m && j != k
    ensures forall j :: j in m' ==> m'[j] == m[j]
    ensures |m'.Keys| <= |m.Keys|
    ensures k in m ==> |m'| == |m| - 1
    ensures k !in m ==> |m'| == |m|
  {
    var m' := map j | j in m && j != k :: m[j];
    assert m'.Keys == m.Keys - {k};
    m'
  }

  method {:extern "Maps_Compile", "ComputeMapRemove1"} ComputeMapRemove1<K,V>(m: map<K,V>, k:K) returns (m' : map<K,V>)
  ensures m' == MapRemove1(m, k)

  function {:opaque} MapRemove1Strong<K,V>(m:map<K,V>, k:K) : (m':map<K,V>)
    ensures m'.Keys == m.Keys - {k}
    ensures forall j :: j in m' ==> m'[j] == m[j]
    ensures |m'.Keys| <= |m.Keys|
    ensures |m'| <= |m|
  {
    reveal_MapRemove1();
    MapRemove1(m, k)
  }
  
  function {:opaque} IMapRemove<K,V>(m:imap<K,V>, ks:iset<K>) : (m':imap<K,V>)
    ensures m'.Keys == m.Keys - ks
    ensures forall j :: j in m' ==> m'[j] == m[j]
  {
    imap j | j in m && j !in ks :: m[j]
  }
 
  function {:opaque} IMapRemove1<K,V>(m:imap<K,V>, k:K) : (m':imap<K,V>)
    ensures m'.Keys == m.Keys - iset{k}
    ensures forall j :: j in m' ==> m'[j] == m[j]
  {
    imap j | j in m && j != k :: m[j]
  }

  function MapRestrict<K,V>(m:map<K,V>, ks: set<K>) : (m':map<K,V>) {
    map k | k in ks && k in m :: m[k]
  }
  
  function MapIRestrict<K,V>(m:map<K,V>, ks: iset<K>) : (m':map<K,V>) {
    map k | k in m && k in ks :: m[k]
  }
  
  function IMapRestrict<K,V>(m:imap<K,V>, ks: iset<K>) : (m':imap<K,V>) {
    imap k | k in ks && k in m :: m[k]
  }
  
	// Requires disjoint domains and delivers predictable result.
	function {:opaque} MapDisjointUnion<U,T>(mapa: map<U,T>, mapb: map<U,T>) : (mapc: map<U,T>)
		requires mapa.Keys !! mapb.Keys;
		ensures mapc.Keys == mapa.Keys + mapb.Keys;
		ensures forall k :: k in mapa.Keys ==> mapa[k] == mapc[k];
		ensures forall k :: k in mapb.Keys ==> mapb[k] == mapc[k];
	{
		map x : U | (x in mapa.Keys + mapb.Keys) :: if x in mapa then mapa[x] else mapb[x]
	}

	// Doesn't require disjoint domains, but guarantees to take A's
	// definition.
	function {:opaque} MapUnionPreferA<U,T>(mapa: map<U,T>, mapb: map<U,T>) : (mapc:map<U,T>)
		ensures mapc.Keys == mapa.Keys + mapb.Keys;
    ensures forall k :: k in mapa.Keys ==> mapc[k] == mapa[k];
    ensures forall k :: k in mapb.Keys - mapa.Keys ==> mapc[k] == mapb[k];
    ensures forall k :: k in mapa.Keys && !(k in mapb.Keys) ==> mapc[k] == mapa[k]; // no-set-op translation is easier for Dafny
	{
		map x : U | (x in mapa.Keys + mapb.Keys) :: if x in mapa then mapa[x] else mapb[x]
	}

  function {:opaque} MapUnionPreferB<U,T>(mapa: map<U,T>, mapb: map<U,T>) : (mapc:map<U,T>)
    ensures mapc.Keys == mapa.Keys + mapb.Keys;
    ensures forall k :: k in mapb.Keys ==> mapc[k] == mapb[k];
    ensures forall k :: k in mapa.Keys - mapb.Keys ==> mapc[k] == mapa[k];
    ensures forall k :: k in mapa.Keys && !(k in mapb.Keys) ==> mapc[k] == mapa[k]; // no-set-op translation is easier for Dafny
  {
    map x : U | (x in mapa.Keys + mapb.Keys) :: if x in mapb then mapb[x] else mapa[x]
  }
  
	// Doesn't require disjoint domains, and makes no promises about
	// which it chooses on the intersection.
	function {:opaque} MapUnion<U,T>(mapa: map<U,T>, mapb: map<U,T>) : (mapc: map<U,T>)
		ensures mapc.Keys == mapa.Keys + mapb.Keys;
		ensures forall k :: k in mapa.Keys -mapb.Keys ==> mapa[k] == mapc[k];
		ensures forall k :: k in mapb.Keys - mapa.Keys ==> mapb[k] == mapc[k];
		ensures forall k :: k in mapa.Keys * mapb.Keys ==>	mapb[k] == mapc[k] || mapa[k] == mapc[k];
	{
		MapUnionPreferA(mapa, mapb)
	}

  function {:opaque} IMapUnionPreferA<U,T>(mapa: imap<U,T>, mapb: imap<U,T>) : (mapc:imap<U,T>)
    ensures mapc.Keys == mapa.Keys + mapb.Keys;
    ensures forall k :: k in mapa.Keys ==> mapc[k] == mapa[k];
    ensures forall k :: k in mapb.Keys - mapa.Keys ==> mapc[k] == mapb[k];
    ensures forall k :: k in mapb.Keys && !(k in mapa.Keys) ==> mapc[k] == mapb[k]; // no-set-op translation is easier for Dafny
  {
    imap x : U | (x in mapa.Keys + mapb.Keys) :: if x in mapa then mapa[x] else mapb[x]
  }

  function {:opaque} IMapUnionPreferB<U,T>(mapa: imap<U,T>, mapb: imap<U,T>) : (mapc:imap<U,T>)
    ensures mapc.Keys == mapa.Keys + mapb.Keys;
    ensures forall k :: k in mapb.Keys ==> mapc[k] == mapb[k];
    ensures forall k :: k in mapa.Keys - mapb.Keys ==> mapc[k] == mapa[k];
    ensures forall k :: k in mapa.Keys && !(k in mapb.Keys) ==> mapc[k] == mapa[k]; // no-set-op translation is easier for Dafny
  {
    imap x : U | (x in mapa.Keys + mapb.Keys) :: if x in mapb then mapb[x] else mapa[x]
  }

	// Doesn't require disjoint domains, and makes no promises about
	// which it chooses on the intersection.
	function {:opaque} IMapUnion<U,T>(mapa: imap<U,T>, mapb: imap<U,T>) : (mapc: imap<U,T>)
		ensures mapc.Keys == mapa.Keys + mapb.Keys;
		ensures forall k :: k in mapa.Keys -mapb.Keys ==> mapa[k] == mapc[k];
		ensures forall k :: k in mapb.Keys - mapa.Keys ==> mapb[k] == mapc[k];
		ensures forall k :: k in mapa.Keys * mapb.Keys ==>	mapb[k] == mapc[k] || mapa[k] == mapc[k];
	{
		IMapUnionPreferA(mapa, mapb)
	}

	// Requires disjoint domains and delivers predictable result.
	function {:opaque} MapDisjointUnion3<U,T>(mapa: map<U,T>, mapb: map<U,T>, mapc: map<U,T>) : map<U,T>
		requires mapa.Keys !! mapb.Keys !! mapc.Keys;
		ensures MapDisjointUnion3(mapa, mapb, mapc).Keys == mapa.Keys + mapb.Keys + mapc.Keys;
		ensures mapa.Keys != {} || mapb.Keys != {} || mapc.Keys != {} ==> MapDisjointUnion3(mapa, mapb, mapc).Keys != {};
		ensures forall k :: k in mapa.Keys ==> mapa[k] == MapDisjointUnion3(mapa, mapb, mapc)[k];
		ensures forall k :: k in mapb.Keys ==> mapb[k] == MapDisjointUnion3(mapa, mapb, mapc)[k];
		ensures forall k :: k in mapc.Keys ==> mapc[k] == MapDisjointUnion3(mapa, mapb, mapc)[k];
		ensures MapDisjointUnion3(mapa, mapb, mapc) == MapDisjointUnion(mapa, MapDisjointUnion(mapb, mapc))
			                                        == MapDisjointUnion(MapDisjointUnion(mapa, mapb), mapc);
	{
		map x : U | (x in mapa.Keys + mapb.Keys + mapc.Keys) ::
			if x in mapa then mapa[x]
			else if x in mapb then mapb[x]
			else mapc[x]
	}

	function MapToImap<K,V>(m: map<K,V>) : imap<K,V> {
	  imap k | k in m :: m[k]
	}

	lemma IsMapUnion<K,V>(m1: map<K,V>, m2: map<K,V>, m: map<K,V>)
	requires m1.Keys !! m2.Keys
	requires forall key | key in m1 :: key in m && m[key] == m1[key]
	requires forall key | key in m2 :: key in m && m[key] == m2[key]
	requires forall key | key in m :: (key in m1 || key in m2)
	ensures m == MapUnion(m1, m2)
	{
	}

	function MapLookupOption<K,V>(m: map<K,V>, key: K) : Option<V>
	{
	  if key in m then Some(m[key]) else None
	}

	function ImapLookupOption<K,V>(m: imap<K,V>, key: K) : Option<V>
	{
	  if key in m then Some(m[key]) else None
	}

  lemma MapsEqualExtensionality<A,B>(a: map<A,B>, b: map<A,B>)
    requires forall key | key in a :: MapsTo(b, key, a[key])
    requires forall key | key in b :: MapsTo(a, key, b[key])
  {
  }

  lemma MapDisjointUnionCardinality<A,B>(a: map<A, B>, b: map<A, B>)
    requires a.Keys !! b.Keys
    ensures |MapDisjointUnion(a, b)| == |a| + |b|
  {
    var u := MapDisjointUnion(a, b);
    assert |u.Keys| == |a.Keys| + |b.Keys|;
  }
}
