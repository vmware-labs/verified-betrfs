// Copyright 2018-2021 VMware, Inc.
// SPDX-License-Identifier: MIT

include "../Base/sequences.i.dfy"
include "../Base/total_order.i.dfy"
  
module PackedSeqSeq {
  import opened Sequences
  import Integer_Order

  datatype PackedSeqSeq<Symbol> = PackedSeqSeq(starts: seq<nat>, seqs: seq<Symbol>)

  predicate WF(pss: PackedSeqSeq) {
    if 0 == |pss.starts| then
      |pss.seqs| == 0
    else
      && pss.starts[0] == 0
      && Integer_Order.IsSorted(pss.starts)
      && Last(pss.starts) <= |pss.seqs|
  }

  function EmptyPackedSeqSeq<Symbol>() : (empty: PackedSeqSeq<Symbol>)
    ensures WF(empty)
  {
    PackedSeqSeq([], [])
  }
    
  function NumSeqs(pss: PackedSeqSeq) : nat
    requires WF(pss)
  {
    |pss.starts|
  }
  
  function Boundary(pss: PackedSeqSeq, i: nat) : (b: nat)
    requires WF(pss)
    requires i <= NumSeqs(pss)
    ensures 0 <= b <= |pss.seqs|
  {
    if i < |pss.starts| then
      Integer_Order.IsSortedImpliesLte(pss.starts, i, |pss.starts|-1);
      pss.starts[i]
    else |pss.seqs|
  }

  lemma BoundariesLte(pss: PackedSeqSeq, i: nat, j: nat)
    requires WF(pss)
    requires i <= j <= NumSeqs(pss)
    ensures Boundary(pss, i) <= Boundary(pss, j)
  {
    Integer_Order.reveal_IsSorted();
  }
  
  function Index<Symbol>(pss: PackedSeqSeq, i: nat) : seq<Symbol>
    requires WF(pss)
    requires i < NumSeqs(pss)
  {
    BoundariesLte(pss, i, i+1);
    pss.seqs[Boundary(pss, i)..Boundary(pss, i+1)]
  }

  function Prefix(pss: PackedSeqSeq, len: nat) : (prefix: PackedSeqSeq)
    requires WF(pss)
    requires len <= NumSeqs(pss)
    ensures WF(prefix)
    ensures NumSeqs(prefix) == len
  {
    if len == 0 then
      EmptyPackedSeqSeq()
    else if len == NumSeqs(pss) then
      pss
    else 
      Integer_Order.SortedSubsequence(pss.starts, 0, len);
      Integer_Order.IsSortedImpliesLte(pss.starts, len-1, len);
      PackedSeqSeq(pss.starts[..len], pss.seqs[..Boundary(pss, len)])
  }
  
  function {:opaque} I<Symbol>(pss: PackedSeqSeq) : (interp: seq<seq<Symbol>>)
    requires WF(pss)
    ensures |interp| == NumSeqs(pss)
    decreases NumSeqs(pss)
  {
    if NumSeqs(pss) == 0 then
      []
    else
      I(Prefix(pss, NumSeqs(pss)-1)) + [Index(pss, NumSeqs(pss)-1)]
  }

  function SubStarts(pss: PackedSeqSeq, start: nat, end: nat) : (substarts: seq<int>)
    requires WF(pss)
    requires start <= end <= NumSeqs(pss)
  {
    Apply(x => x - Boundary(pss, start), pss.starts[start..end])
  }

  lemma SubStartsNat(pss: PackedSeqSeq, start: nat, end: nat)
    requires WF(pss)
    requires start <= end <= NumSeqs(pss)
    ensures Integer_Order.IsSorted(SubStarts(pss, start, end))
    ensures forall i :: 0 <= i < |SubStarts(pss, start, end)| ==> 0 <= SubStarts(pss, start, end)[i]
  {
    Integer_Order.reveal_IsSorted();
  }
  
  function SubSeqSeq<Symbol>(pss: PackedSeqSeq<Symbol>, start: nat, end: nat) : (sub: PackedSeqSeq<Symbol>)
    requires WF(pss)
    requires start <= end <= NumSeqs(pss)
    ensures WF(sub)
    // ensures I(sub) == I(pss)[start..end]
  {
    var substarts := SubStarts(pss, start, end);
    SubStartsNat(pss, start, end);
    BoundariesLte(pss, start, end);
    var newseqs := pss.seqs[Boundary(pss, start)..Boundary(pss, end)];
    PackedSeqSeq(substarts, newseqs)
  }
}
