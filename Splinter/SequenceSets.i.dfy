// TODO move into lib someday
module SequenceSetsMod {
  predicate SequenceSubset<T>(a:seq<T>, b:seq<T>)
  {
    forall i | 0<=i<|a| :: a[i] in b
  }

  function Members<T>(a: seq<T>) : set<T>
  {
    set e | e in a
  }

  function ArbitrarySequentialization<T>(a: set<T>) : (b: seq<T>)
    ensures |b| == |a|
    //ensures forall x :: x in a <==> x in b
    ensures Members(b) == a
  {
    if |a|==0
    then []
    else
      var x :| x in a;
      ArbitrarySequentialization(a - {x}) + [x]
  }
}
