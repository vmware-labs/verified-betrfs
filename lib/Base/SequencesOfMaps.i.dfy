include "Sequences.i.dfy"
include "Maps.i.dfy"

module SequencesOfMaps {
  import opened Sequences
  import opened Maps

  function FoldMaps<K, V>(run: seq<map<K, V>>) : (out: map<K, V>)
  {
    FoldRight((a, e) => MapUnion(a, e), map[], run)
  }

  lemma FoldMapsSubset<K, V>(run: seq<map<K, V>>)
    ensures forall i | 0 <= i < |run| :: run[i].Keys <= FoldMaps(run).Keys
  {
    forall i | 0 <= i < |run| 
    ensures run[i].Keys <= FoldMaps(run).Keys
    {
      if i !=0 {
        FoldMapsSubset(run[1..]);  
      }
    }
  }
}

