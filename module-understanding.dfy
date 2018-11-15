//abstract module ImmutableSet {
//    method New<V>() returns (tree: Node)
//        requires Valid(tree)
//        ensures Contents(tree) == multiset{}
//
//    method Insert(tree:Node, value:Value) returns (updated: Node)
//        requires Valid(tree)
//        ensures Valid(updated)
//        ensures Contents(updated) == Contents(tree) + multiset{value};
//
//    method Contains(tree: Node, value: Value) returns (present: bool)
//        requires Valid(tree)
//        ensures present == (value in Contents(tree))
//}

abstract module Comparator {
    predicate method lt<V>(a: V, b:V)

    predicate method lte<V>(a: V, b: V)
}

abstract module Seq {
    import C : Comparator
    datatype S<V> = S(contents: seq<V>)

    predicate Valid(s: S) {
        true
    }

    function Contents<V>(s: S) : multiset<V>
        decreases |s.contents|
    {
        multiset(s.contents)
    }

    method BaseNew<V>() returns (s: S)
        ensures Valid(s)
        ensures Contents(s) == multiset{}
    {
        return S([]);
    }

    method Insert<V>(s:S, value:V) returns (updated: S)
        requires Valid(s)
        ensures Valid(updated)
        ensures Contents(updated) == Contents(s) + multiset{value};
    {
        return S(s.contents + [value]);
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
        ensures forall x :: x in Contents(s) ==> C.lte(x, biggest)
    {
        biggest := s.contents[0];
        var i := 1;
        while (i < |s.contents|)
            invariant forall x :: x in multiset(s.contents[i..i])
                ==> C.lte(x, biggest);
        {
            if (C.lt(biggest, s.contents[i])) {
                biggest := s.contents[i];
            }
        }
    }
}

module IntComparator refines Comparator {
    predicate method lt<V>(a: int, b:int) {
        a < b
    }

    predicate method lte(a: int, b: int) {
        a <= b
    }
}

module IntSeq refines Seq {
    import C = IntComparator 
    method New() returns (s: S<int>)
    {
        s := BaseNew<int>();
    }
}

module StrComparator refines Comparator {
    predicate method lt(a: string, b:string) {
        a < b
    }

    predicate method lte(a: string, b: string) {
        a <= b
    }
}

module StrSeq refines Seq {
    import C = StrComparator 
    method New() returns (s: S<string>)
    {
        s := BaseNew<string>();
    }
}

method Main() {
    var intSeq := IntSeq.New();
    intSeq := IntSeq.Insert(intSeq, 7);
    intSeq := IntSeq.Insert(intSeq, 3);
    intSeq := IntSeq.Insert(intSeq, 7);
    var x1 := IntSeq.Contains(intSeq, 3);
    var x2 := IntSeq.Contains(intSeq, 17);
    var x3 := IntSeq.Contains(intSeq, 7);
    print x1, x2, x3;
    print "\n";

    var strSeq := StrSeq.New();
    strSeq := Seq.Insert(strSeq, "a");
    strSeq := Seq.Insert(strSeq, "b");
    var x4 := Seq.Contains(strSeq, "a");
    print x4;
}
