include "../lib/sequences.dfy"
include "../lib/total_order.dfy"
include "../lib/lexical.dfy"

abstract module SSTable {
  import LO: Lexical_Order
  import opened Sequences
  import IntOrder = Integer_Order

  type String = LO.Element
  type Symbol = LO.Entry.Element
    
  datatype SSTable = SSTable(starts: seq<int>, strings: String)

  function method Start(sstable: SSTable, i: int) : int
    requires 0 <= i < |sstable.starts|
  {
    sstable.starts[i]
  }
  
  function method End(sstable: SSTable, i: int) : int
    requires 0 <= i < |sstable.starts|
  {
    if i < |sstable.starts|-1 then
      sstable.starts[i+1]
    else
      |sstable.strings|
  }
  
  function method TableEntry(sstable: SSTable, i: int) : String
    requires Start.requires(sstable, i)
    requires End.requires(sstable, i)
    requires 0 <= Start(sstable, i) <= End(sstable, i) <= |sstable.strings|
  {
    sstable.strings[Start(sstable, i)..End(sstable, i)]
  }
  
  predicate WFSSTable(sstable: SSTable) {
    && 0 < |sstable.starts|
    && sstable.starts[0] == 0
    && IntOrder.IsStrictlySorted(sstable.starts)
    && 0 <= Last(sstable.starts) < |sstable.strings|
  }

  function DropLastString(sstable: SSTable) : (result: SSTable)
    requires WFSSTable(sstable)
    requires 1 < |sstable.starts|
    ensures WFSSTable(result)
  {
    IntOrder.reveal_IsStrictlySorted();
    var newstarts := DropLast(sstable.starts);
    var newstrings := sstable.strings[..Last(sstable.starts)];
    SSTable(newstarts, newstrings)
  }
  
  function Interpretation(sstable: SSTable) : (result: seq<String>)
    requires WFSSTable(sstable)
    ensures |result| == |sstable.starts|
    decreases |sstable.starts|
  {
    IntOrder.reveal_IsStrictlySorted();
    if |sstable.starts| == 1 then
      [ sstable.strings ]
    else
      Interpretation(DropLastString(sstable)) + [TableEntry(sstable, |sstable.starts|-1)]
  }

  lemma TableEntryIsCorrect(sstable: SSTable, i: int)
    requires TableEntry.requires(sstable, i)
    requires Interpretation.requires(sstable)
    ensures TableEntry(sstable, i) == Interpretation(sstable)[i]
    decreases |sstable.starts|
  {
    if |sstable.starts| == 1 {
    } else if i == |sstable.starts|-1 {      
    } else {
      IntOrder.reveal_IsStrictlySorted();
      TableEntryIsCorrect(SSTable(DropLast(sstable.starts), sstable.strings[..Last(sstable.starts)]), i);
    }
  }

  method IndexOfSmallestGTE(sstable: SSTable, key: String) returns (index: int)
    requires WFSSTable(sstable)
    requires LO.IsSorted(Interpretation(sstable))
    ensures 0 <= index <= |sstable.starts|
    ensures forall i :: 0 <= i < index ==> LO.lt(TableEntry(sstable, i), key)
    ensures LO.lte(key, TableEntry(sstable, index))
    ensures forall i :: index < i < |sstable.starts| ==> LO.lt(key, TableEntry(sstable, i))
  {
    
  }
  
  // method Merge(sstable1: SSTable, sstable2: SSTable) returns (result: SSTable)
  //   requires WFSSTable(sstable1)
  //   requires WFSSTable(sstable2)
  //   requires LO.IsSorted(Interpretation(sstable1))
  //   requires LO.IsSorted(Interpretation(sstable2))
  //   ensures WFSSTable(result)
  //   ensures LO.IsSorted(Interpretation(result))
  // {
  // }
}
