lemma disjointness_lemma(a:set<int>, b:set<int>)
    requires a * b == {};
    ensures forall k :: k in a + b && k in b ==> !(k in a);
{
    forall k | k in a + b && k in b
        ensures !(k in a)
    {
        var intersection := a * b;
        if k in a {
            assert k in intersection;
        }
    }
}

function mapunion(a:map<int, int>, b:map<int, int>) : map<int, int>
    requires a.Keys * b.Keys == {};
    ensures a.Keys + b.Keys == mapunion(a, b).Keys;
    ensures forall k :: k in a.Keys ==> a[k] == mapunion(a,b)[k];
    ensures forall k :: k in b.Keys ==> b[k] == mapunion(a,b)[k];
{
    var c := map k| k in a.Keys + b.Keys :: if k in a.Keys then a[k] else b[k];
    disjointness_lemma(a.Keys, b.Keys);
    c
}
