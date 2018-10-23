function domain(m:map<int, int>) : set<int>
{
    set k | k in m
}

function mapunion(a:map<int, int>, b:map<int, int>) : map<int, int>
    requires domain(a) * domain(b) == {};
    ensures domain(a) + domain(b) == domain(mapunion(a, b));
{
    map k| k in domain(a) + domain(b) :: if k in domain(a) then a[k] else b[k]
}

lemma mapunionLemma(a:map<int, int>, b:map<int, int>, c:map<int, int>)
    requires domain(a) * domain(b) == {};
    requires c == mapunion(a, b);
    ensures forall k :: k in domain(a) ==> a[k] == c[k];
    ensures forall k :: k in domain(b) ==> b[k] == c[k];
{
    forall k
        ensures k in domain(b) ==> b[k] == c[k];
    {
        if k in domain(b) {
            if (k in domain(a)) {
                 var intersection := domain(a) * domain(b);
                 assert k in intersection;
                 //assert intersection == {};
                 //assert k in {};
                 //assert false;
            }
            //assert !(k in domain(a));
            //assert c[k] == b[k];
        }
    }
}
