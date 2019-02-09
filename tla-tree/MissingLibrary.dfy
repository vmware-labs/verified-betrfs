module MissingLibrary {

function Last<T>(s:seq<T>) : T  // TODO move to library
    requires 0<|s|
{
    s[|s|-1]
}

function {:opaque} MapRemove<K,V>(m:map<K,V>, k:K) : (m':map<K,V>)
    ensures m'.Keys == m.Keys - {k}
    ensures forall j :: j in m' ==> m'[j] == m[j]
{
    map j | j in m && j != k :: m[j]
}

} // module
