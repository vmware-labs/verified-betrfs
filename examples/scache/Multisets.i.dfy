module MultisetUtil {
  function Count<A>(fn: A ~> bool, s: multiset<A>) : nat

  function Sum<A>(fn: A ~> int, s: multiset<A>) : int

  lemma Count_ge_1<A>(fn: A -> bool, s: multiset<A>, v: A)
  requires fn(v)
  requires v in s
  ensures Count(fn, s) >= 1

  lemma Count_ge_2<A>(fn: A -> bool, s: multiset<A>, v: A, w: A)
  requires fn(v)
  requires fn(w)
  requires v in s
  requires w in s
  requires v != w
  ensures Count(fn, s) >= 2

  lemma get_nonzero_elem<A>(fn: A -> int, s: multiset<A>)
  returns (v: A)
  requires Sum(fn, s) != 0
  ensures v in s
  ensures fn(v) != 0

  lemma get_true_elem<A>(fn: A -> bool, s: multiset<A>)
  returns (v: A)
  requires Count(fn, s) != 0
  ensures v in s
  ensures fn(v)

  lemma get_2_true_elems<A>(fn: A -> bool, s: multiset<A>)
  returns (v: A, w: A)
  requires Count(fn, s) >= 2
  ensures multiset{v, w} <= s
  ensures fn(v)
  ensures fn(w)

  lemma SumAdditive<A>(fn: A -> int, s: multiset<A>, t: multiset<A>)
  ensures Sum(fn, s) + Sum(fn, t) == Sum(fn, s + t)

  lemma SumMultiset1<A>(fn: A -> int, v: A)
  ensures Sum(fn, multiset{v}) == fn(v)

  lemma CountAdditive<A>(fn: A -> bool, s: multiset<A>, t: multiset<A>)
  ensures Count(fn, s) + Count(fn, t) == Count(fn, s + t)

  lemma CountMultiset1<A>(fn: A -> bool, v: A)
  ensures fn(v) ==> Count(fn, multiset{v}) == 1
  ensures !fn(v) ==> Count(fn, multiset{v}) == 0

  lemma CountSubset<A>(fn: A -> bool, fn2: A -> bool, t: multiset<A>)
  requires forall x: A :: fn(x) ==> fn2(x)
  ensures Count(fn, t) <= Count(fn2, t)

}
