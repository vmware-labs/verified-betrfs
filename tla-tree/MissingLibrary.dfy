module MissingLibrary {

function Last<T>(s:seq<T>) : T  // TODO move to library
    requires 0<|s|
{
    s[|s|-1]
}

function {:opaque} EmptyMap<K(!new),V>(any:V) : (e:map<K,V>)
    ensures e.Keys == {}
{
    map k | k in {} :: any
}

function {:opaque} MapRemove<K,V>(m:map<K,V>, k:K) : (m':map<K,V>)
    ensures m'.Keys == m.Keys - {k}
    ensures forall j :: j in m' ==> m'[j] == m[j]
{
    map j | j in m && j != k :: m[j]
}

function {:opaque} SingletonImap<K,V>(k:K, v:V) : (m:imap<K,V>)
    ensures m.Keys == iset {k}
    ensures m[k] == v
{
    imap j | j == k :: v
}

function {:opaque} MapUnionPreferB<U,T>(mapa: map<U,T>, mapb: map<U,T>) : (mapc:map<U,T>)
    ensures mapc.Keys == mapa.Keys + mapb.Keys;
    ensures forall k :: k in mapb.Keys ==> mapc[k] == mapb[k];
    ensures forall k :: k in mapb.Keys - mapa.Keys ==> mapc[k] == mapb[k];
    ensures forall k :: k in mapa.Keys && !(k in mapb.Keys) ==> mapc[k] == mapa[k]; // no-set-op translation is easier for Dafny
{
    map x : U | (x in mapa.Keys + mapb.Keys) :: if x in mapb then mapb[x] else mapa[x]
}

function {:opaque} ImapUnionPreferB<U,T>(mapa: imap<U,T>, mapb: imap<U,T>) : (mapc:imap<U,T>)
    ensures mapc.Keys == mapa.Keys + mapb.Keys;
    ensures forall k :: k in mapb.Keys ==> mapc[k] == mapb[k];
    ensures forall k :: k in mapb.Keys - mapa.Keys ==> mapc[k] == mapb[k];
    ensures forall k :: k in mapa.Keys && !(k in mapb.Keys) ==> mapc[k] == mapa[k]; // no-set-op translation is easier for Dafny
{
    imap x : U | (x in mapa.Keys + mapb.Keys) :: if x in mapb then mapb[x] else mapa[x]
}

datatype Option<V> = None | Some(value:V)

function max(a:int, b:int) : int
{
    if a>b then a else b
}

} // module
