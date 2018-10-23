function domain(m:map<int, int>) : set<int>
{
    set k | k in m
}

lemma disjointness_lemma3(a:set<int>, b:set<int>)
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
    requires domain(a) * domain(b) == {};
    ensures domain(a) + domain(b) == domain(mapunion(a, b));
    ensures forall k :: k in domain(a) ==> a[k] == mapunion(a,b)[k];
    ensures forall k :: k in domain(b) ==> b[k] == mapunion(a,b)[k];
{
    var c := map k| k in domain(a) + domain(b) :: if k in domain(a) then a[k] else b[k];
    disjointness_lemma3(domain(a), domain(b));
    c
}
