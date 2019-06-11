module MissingLibrary {


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

