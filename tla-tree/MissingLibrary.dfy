module MissingLibrary {

function /*{:opaque} XXX*/ Last<T>(s:seq<T>) : T
    requires 0<|s|
{
    s[|s|-1]
}

function {:opaque} EmptyImap<K(!new),V>() : (e:imap<K,V>)
    ensures e.Keys == iset{}
{
    var v :| true;
    imap k | k in {} :: v
}

function {:opaque} EmptyMap<K(!new),V>() : (e:map<K,V>)
    ensures e.Keys == {}
{
    var v :| true;
    map k | k in {} :: v
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

function {:opaque} MemsetSeq<V>(v:V, len:nat) : (s:seq<V>)
    ensures |s| == len
    ensures forall i :: 0<=i<len ==> s[i] == v
{
    if len == 0 then [] else MemsetSeq(v, len-1) + [v]
}

} // module

