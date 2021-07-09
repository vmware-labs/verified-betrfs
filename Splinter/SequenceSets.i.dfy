// TODO move into lib someday
module SequenceSetsMod {
  predicate SequenceSubset<T>(a:seq<T>, b:seq<T>)
  {
    forall i | 0<=i<|a| :: a[i] in b
  }
}
