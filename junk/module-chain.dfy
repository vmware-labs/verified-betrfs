module Comparator {
    datatype Comparison = Less | Equal | Greater
    datatype Comparator<!V> = Comparator(cmp:(V, V)->Comparison)
}

module ADT {
    import opened C : Comparator

    datatype Struct<!V> = Struct(cmp:Comparator<V>, value: V)

    method New<V>(cmp:Comparator<V>, value: V) returns (s: Struct)
    {
        s := Struct(cmp, value);
    }

    
}

module IntConcreteComparator {
    import opened ADT : ADT

    function method IntCompare(a: int, b: int) : ADT.C.Comparison
    {
        if a<b then ADT.C.Less else if a==b then ADT.C.Equal else ADT.C.Greater
    }

    function method IntComparator() : ADT.C.Comparator<int>
    {
        ADT.C.Comparator(IntCompare)
    }
}

module IntADT {
    import opened CC : IntConcreteComparator

    method NewIntADT() returns (s: CC.ADT.Struct<int>)
    {
        var cmp : CC.ADT.C.Comparator := IntComparator();
        var cmp2 : ADT.C.Comparator := cmp;
        s := CC.ADT.New(cmp2, 0);
    }
}
