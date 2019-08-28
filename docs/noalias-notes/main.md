---
title:  'This is the title: it contains a colon'

header-includes: |
    ```{=latex}
    \usepackage{times}
    \usepackage[hscale=0.8,vscale=0.82]{geometry}
    \lstset
    { %Formatting for code in appendix
    basicstyle=\footnotesize\ttfamily,
    numberstyle=\ttfamily,
    numbers=left,
    frame=l,
    framexleftmargin=2pt,
    morekeywords={requires,ensures,forall,modifies,predicate,method,function},
    showstringspaces=false,
    breaklines=true,
    }
    ```

bibliography: biblio.bib
csl: acm-sig-proceedings-long-author-list.csl
...

# Introduction

Dafny is a language for program verification.

# Dafny's heap model

# Shortcomings

## Possible aliasing (deep)

### Example 1

```
HeapState(
        persistentIndirectionTable: MutIndirectionTable,
        frozenIndirectionTable: Option<MutIndirectionTable>,
        ephemeralIndirectionTable: MutIndirectionTable)

predicate Inv()
  ...
  && persistentIndirectionTable.Repr !! ephemeralIndirectionTable.Repr !! (if frozenIndirectionTable.Some? then frozenIndirectionTable.value.Repr else {})
```

Awkward when mixed with ADTs (`Option`). Line 



### Example 2

```
method ModifiesEphemeralTable
  ensures forall r | r in s.ephemeralIndirectionTable.Repr ::
      fresh(r) || r in old(s.ephemeralIndirectionTable.Repr)
  modifies s.ephemeralIndirectionTable.Repr
```

## Deep const-ness

### Example 3

```
datatype Entry<V> = Entry((K, V)) | Empty

// neither this, nor its contents will change
var table: array<Entry<V>> := hashTable.ToArray();
ghost var tableSeq := table[..];

var result := array<(K, V)>;

var i: uint64 := 0;
while i < table.Length
...
invariant table[..] == tableSeq // <-- this would be unncessary if table wasn't "mut"
...
invariant EntriesInTable(table[..i]) == result[..i]
{
	...
}
```





## Summary

You can't trust the errors until heap reasoning resolved (and feedback is confused with non-heap errors).

Heap reasoning unnecessary in most cases (no aliasing).

# Related work

RedLeaf: [@DBLP:conf/hotos/NarayananBRRB19]

SPARK: [@DBLP:journals/corr/abs-1805-05576]

Prusti: [@AstrauskasMuellerPoliSummers19]

Oxide: [@DBLP:journals/corr/abs-1903-00982]