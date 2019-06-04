module Comparator {
    datatype Comparison = Less | Equal | Greater
    datatype Comparator<!V> = Comparator(cmp:(V, V)->Comparison)

    predicate IsValidComparator<V(!new)>(c:Comparator<V>)
    {
        // Reflexivity
        && (forall x :: c.cmp(x, x).Equal?)
        // Assymetry
        && (forall x, y :: !c.cmp(x, y).Less? ==> !c.cmp(y, x).Greater?)
        // Transitivity
        && (forall x, y, z :: c.cmp(x, y).Less? && c.cmp(y, z).Less? ==> c.cmp(x, z).Less?)
        // Equality
        && (forall x, y, z :: c.cmp(x, y).Less? && c.cmp(y, z).Equal? ==> c.cmp(x, z).Less?)
        && (forall x, y, z :: c.cmp(x, y).Equal? && c.cmp(y, z).Less? ==> c.cmp(x, z).Less?)
    }
    
    function method IntComparator() : Comparator<int>
    {
        Comparator((a, b) =>
            if a<b then Less else if a==b then Equal else Greater)
    }

    function method CompareStrings(a:string, b:string) : Comparison
    {
        if |a| == 0 then
            (if |b| == 0 then Equal else Less)
        else
            if |b| == 0 then
               Greater 
            else
                if a[0] == b[0]
                then
                    Equal
                else
                    if a[0] < b[0] then Less else Greater
    }

    function method StringComparator() : Comparator<string>
    {
        Comparator((a, b) => CompareStrings(a, b))
    }

    lemma lemma_ComparatorsValid()
        ensures IsValidComparator(IntComparator())
        ensures IsValidComparator(StringComparator())
    {
    }

}

module Seq {
    import opened C : Comparator
    datatype S<!V> = S(cmp:Comparator<V>, contents: seq<V>)

    predicate Valid(s: S) {
        IsValidComparator(s.cmp)
    }

    function Contents<V>(s: S) : multiset<V>
        decreases |s.contents|
    {
        multiset(s.contents)
    }

    method New<V>(cmp:Comparator<V>) returns (s: S)
        requires IsValidComparator(cmp);
        ensures Valid(s)
        ensures Contents(s) == multiset{}
    {
        return S(cmp, []);
    }

    method Insert<V>(s:S, value:V) returns (updated: S)
        requires Valid(s)
        ensures Valid(updated)
        ensures Contents(updated) == Contents(s) + multiset{value};
    {
        return S(s.cmp, s.contents + [value]);
    }

    method Contains<V(==)>(s: S, value: V) returns (present: bool)
        requires Valid(s)
        ensures present == (value in Contents(s))
    {
        return value in s.contents;
    }

    method Biggest<V>(s:S) returns (biggest: V)
        requires Valid(s)
        requires Contents(s) != multiset{}
        ensures forall x :: x in Contents(s) ==> !s.cmp.cmp(x, biggest).Greater?
    {
        var cmp := s.cmp.cmp;
        biggest := s.contents[0];
        var i := 1;
        while (i < |s.contents|)
            invariant i <= |s.contents|;
            invariant forall x :: x in s.contents[..i]
                ==> !cmp(x, biggest).Greater?;
        {
            if (cmp(biggest, s.contents[i]).Less?) {
                biggest := s.contents[i];
            }
            ghost var j := i + 1;
            i := i + 1;
        }
    }

    // Pleasant public constructors.
    method NewIntSeq() returns (s: S<int>)
        ensures Valid(s);
    {
        lemma_ComparatorsValid();
        s := New(IntComparator());
    }

    method NewStringSeq() returns (s: S<string>)
        ensures Valid(s);
    {
        lemma_ComparatorsValid();
        s := New(StringComparator());
    }
}

method Main() {
    var intSeq := Seq.NewIntSeq();
    intSeq := Seq.Insert(intSeq, 7);
    intSeq := Seq.Insert(intSeq, 3);
    intSeq := Seq.Insert(intSeq, 7);
    var x1 := Seq.Contains(intSeq, 3);
    var x2 := Seq.Contains(intSeq, 17);
    var x3 := Seq.Contains(intSeq, 7);
    var x4 := Seq.Biggest(intSeq);
    print x1, " ", x2, " ", x3, " ", x4;
    print "\n";

    var strSeq := Seq.NewStringSeq();
    strSeq := Seq.Insert(strSeq, "a");
    strSeq := Seq.Insert(strSeq, "bob");
    strSeq := Seq.Insert(strSeq, "baby");
    strSeq := Seq.Insert(strSeq, "b");
    strSeq := Seq.Insert(strSeq, "bingo");
    var x5 := Seq.Contains(strSeq, "a");
    var x6 := Seq.Biggest(strSeq);
    print x5, " ", x6, "\n";
}
