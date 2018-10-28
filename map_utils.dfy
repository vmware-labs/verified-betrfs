module Map_Utils {

	// Requires disjoint domains and delivers predictable result.
	function method {:opaque} disjoint_union<U,T>(mapa: map<U,T>, mapb: map<U,T>) : map<U,T>
		requires mapa.Keys !! mapb.Keys;
		ensures disjoint_union(mapa, mapb).Keys == mapa.Keys + mapb.Keys;
		ensures mapa.Keys != {} || mapb.Keys != {} ==> disjoint_union(mapa, mapb).Keys != {};
		ensures forall k :: k in mapa.Keys ==> mapa[k] == disjoint_union(mapa, mapb)[k];
		ensures forall k :: k in mapb.Keys ==> mapb[k] == disjoint_union(mapa, mapb)[k];
	{
		map x : U | (x in mapa.Keys + mapb.Keys) :: if x in mapa then mapa[x] else mapb[x]
	}

	// Doesn't require disjoint domains, but guarantees to take A's
	// definition.
	function method {:opaque} union_preferA<U,T>(mapa: map<U,T>, mapb: map<U,T>) : map<U,T>
		ensures union_preferA(mapa, mapb).Keys == mapa.Keys + mapb.Keys;
		ensures mapa.Keys != {} || mapb.Keys != {} ==> union_preferA(mapa, mapb).Keys != {};
		ensures forall k :: k in mapa.Keys ==> mapa[k] == union_preferA(mapa, mapb)[k];
		ensures forall k :: k in mapb.Keys - mapa.Keys ==> mapb[k] == union_preferA(mapa, mapb)[k];
	{
		map x : U | (x in mapa.Keys + mapb.Keys) :: if x in mapa then mapa[x] else mapb[x]
	}

	// Doesn't require disjoint domains, and makes no promises about
	// which it chooses on the intersection.
	function method {:opaque} union<U,T>(mapa: map<U,T>, mapb: map<U,T>) : map<U,T>
		ensures union(mapa, mapb).Keys == mapa.Keys + mapb.Keys;
		ensures mapa.Keys != {} || mapb.Keys != {} ==> union(mapa, mapb).Keys != {};
		ensures forall k :: k in mapa.Keys -mapb.Keys ==> mapa[k] == union(mapa, mapb)[k];
		ensures forall k :: k in mapb.Keys - mapa.Keys ==> mapb[k] == union(mapa, mapb)[k];
		ensures forall k :: k in mapa.Keys * mapb.Keys ==>
			mapb[k] == union(mapa, mapb)[k] || mapa[k] == union(mapa, mapb)[k];
	{
		union_preferA(mapa, mapb)
	}
}
