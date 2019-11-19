

module SetBijectivity {
  lemma BijectivityImpliesEqualCardinality<A, B>(setA: set<A>, setB: set<B>, relation: iset<(A, B)>)
    requires forall a :: a in setA ==> exists b :: b in setB && (a, b) in relation
    requires forall a1, a2, b :: a1 in setA && a2 in setA && b in setB && (a1, b) in relation && (a2, b) in relation ==> a1 == a2
    requires forall b :: b in setB ==> exists a :: a in setA && (a, b) in relation
    requires forall a, b1, b2 :: b1 in setB && b2 in setB && a in setA && (a, b1) in relation && (a, b2) in relation ==> b1 == b2
    ensures |setA| == |setB|
  {
    if |setA| == 0 {
    } else {
      var a :| a in setA;
      var b :| b in setB && (a, b) in relation;
      var setA' := setA - {a};
      var setB' := setB - {b};
      BijectivityImpliesEqualCardinality(setA', setB', relation);
    }
  }
}
