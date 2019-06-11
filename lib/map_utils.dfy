module Map_Utils {

	// Requires disjoint domains and delivers predictable result.
	function method {:opaque} MapDisjointUnion<U,T>(mapa: map<U,T>, mapb: map<U,T>) : map<U,T>
		requires mapa.Keys !! mapb.Keys;
		ensures MapDisjointUnion(mapa, mapb).Keys == mapa.Keys + mapb.Keys;
		ensures mapa.Keys != {} || mapb.Keys != {} ==> MapDisjointUnion(mapa, mapb).Keys != {};
		ensures forall k :: k in mapa.Keys ==> mapa[k] == MapDisjointUnion(mapa, mapb)[k];
		ensures forall k :: k in mapb.Keys ==> mapb[k] == MapDisjointUnion(mapa, mapb)[k];
	{
		map x : U | (x in mapa.Keys + mapb.Keys) :: if x in mapa then mapa[x] else mapb[x]
	}

	// Requires disjoint domains and delivers predictable result.
	function method {:opaque} MapDisjointUnion3<U,T>(mapa: map<U,T>, mapb: map<U,T>, mapc: map<U,T>) : map<U,T>
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

	// Doesn't require disjoint domains, but guarantees to take A's
	// definition.
	function method {:opaque} MapUnionPreferA<U,T>(mapa: map<U,T>, mapb: map<U,T>) : (mapc:map<U,T>)
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
	function method {:opaque} MapUnion<U,T>(mapa: map<U,T>, mapb: map<U,T>) : map<U,T>
		ensures MapUnion(mapa, mapb).Keys == mapa.Keys + mapb.Keys;
		ensures mapa.Keys != {} || mapb.Keys != {} ==> MapUnion(mapa, mapb).Keys != {};
		ensures forall k :: k in mapa.Keys -mapb.Keys ==> mapa[k] == MapUnion(mapa, mapb)[k];
		ensures forall k :: k in mapb.Keys - mapa.Keys ==> mapb[k] == MapUnion(mapa, mapb)[k];
		ensures forall k :: k in mapa.Keys * mapb.Keys ==>
			mapb[k] == MapUnion(mapa, mapb)[k] || mapa[k] == MapUnion(mapa, mapb)[k];
	{
		MapUnionPreferA(mapa, mapb)
	}

  predicate IMapsTo<K,V>(m: imap<K, V>, k: K, v: V) {
    k in m && m[k] == v
  }
  
  predicate MapsTo<K,V>(m: map<K, V>, k: K, v: V) {
    k in m && m[k] == v
  }

  // Trigger bait
  predicate InEmpty<K>(k: K) {
    false
  }
  
  function {:opaque} EmptyImap<K(!new),V>() : (e:imap<K,V>)
    ensures e.Keys == iset{}
  {
    var v :| true;
    imap k | InEmpty(k)  :: v
  }
  
  function {:opaque} EmptyMap<K(!new),V>() : (e:map<K,V>)
    ensures e.Keys == {}
  {
    var v :| true;
    map k | k in {} && InEmpty(k) :: v
  }
  
  function {:opaque} MapRemove<K,V>(m:map<K,V>, k:K) : (m':map<K,V>)
    ensures m'.Keys == m.Keys - {k}
    ensures forall j :: j in m' ==> m'[j] == m[j]
  {
    map j | j in m && j != k :: m[j]
  }
  
  function {:opaque} ImapUnionPreferB<U,T>(mapa: imap<U,T>, mapb: imap<U,T>) : (mapc:imap<U,T>)
    ensures mapc.Keys == mapa.Keys + mapb.Keys;
    ensures forall k :: k in mapb.Keys ==> mapc[k] == mapb[k];
    ensures forall k :: k in mapb.Keys - mapa.Keys ==> mapc[k] == mapb[k];
    ensures forall k :: k in mapa.Keys && !(k in mapb.Keys) ==> mapc[k] == mapa[k]; // no-set-op translation is easier for Dafny
  {
    imap x : U | (x in mapa.Keys + mapb.Keys) :: if x in mapb then mapb[x] else mapa[x]
  }
}
