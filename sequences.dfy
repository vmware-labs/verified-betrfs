module Sequences {
  function method Last<E>(run: seq<E>) : E
    requires |run| > 0;
  {
    run[|run|-1]
  }

  function method Set<T>(run: seq<T>) : set<T> {
    set x : T | x in multiset(run)
  }
  
  function method ISet<T>(run: seq<T>) : iset<T> {
    iset x : T | x in multiset(run)
  }
  
  predicate NoDupes<T>(a: seq<T>) {
    (forall i, j :: 0 <= i < |a| && 0 <= j < |a| && i != j ==> a[i] != a[j])
  }

  lemma DisjointConcatenation<T>(a: seq<T>, b: seq<T>)
    requires NoDupes(a);
    requires NoDupes(b);
    requires multiset(a) !! multiset(b);
    ensures NoDupes(a + b);
  {
    var c := a + b;
    if |c| > 1 {
      assert forall i, j :: i != j && 0 <= i < |a| && |a| <= j < |c| ==>
        c[i] in multiset(a) && c[j] in multiset(b) && c[i] != c[j]; // Observe
    }
  }

  function IndexOf<T>(s: seq<T>, e: T) : int
    requires e in s;
    ensures 0 <= IndexOf(s,e) < |s|;
    ensures s[IndexOf(s,e)] == e;
  {
    var i :| 0 <= i < |s| && s[i] == e;
    i
  }
  
  function method Apply<E,R>(f: (E -> R), run: seq<E>) : seq<R>
  {
    if |run| == 0 then []
    else  [f(run[0])] + Apply(f, run[1..])
  }
  
  function method FoldLeft<A,E>(f: (A, E) -> A, init: A, run: seq<E>) : A
  {
    if |run| == 0 then init
    else FoldLeft(f, f(init, run[0]), run[1..])
  }
}
