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
    import opened C : Comparator

    function method IntComparator() : Comparator<int>
    {
        Comparator((a, b) =>
            if a<b then Less else if a==b then Equal else Greater)
    }
}

module IntADT {
    import opened ADT : ADT
    import opened CC : IntConcreteComparator

    method NewIntADT() returns (s: Struct<int>)
    {
        var cmp : CC.C.Comparator := IntComparator();
        var cmp2 : ADT.C.Comparator := cmp;
        s := New(cmp2, 0);
    }
}
