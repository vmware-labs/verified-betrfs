// Copyright 2018-2021 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, and University of Washington
// SPDX-License-Identifier: BSD-2-Clause

include "../../lib/Base/Option.s.dfy"
include "../../lib/Base/Maps.i.dfy"


module GenericDisk {
  import opened Options
  import opened Maps

  //////////////////////////////////////////////////////////////////
  // jonh fought for too long trying to make address type a (module) parameter,
  // and eventually gave up (see branch splinter-journal-auaddress-module-disaster).
  // So for now we're just going to hardcode the AU-address-shape assumptions up
  // too high in the refinement stack. :v(
  type AU = nat
  type Page = nat

  function PageCount() : nat

  datatype Address = Address(au: AU, page: Page) {
    predicate WF() {
      && page < PageCount()
    }

    function FirstPage() : Address
    {
      Address(au, 0)
    }

    function NextPage() : Address
    {
      Address(au, page+1)
    }
  }

  function MinAddr(a: Address, b: Address) : Address
	{
    if a.au < b.au then a
    else if a.au > b.au then b
    else if a.page <= b.page then a else b
	}

  function ToAUs(addrs: set<Address>) : set<AU>
  {
    set addr | addr in addrs :: addr.au
  }

  //////////////////////////////////////////////////////////////////

  type Block(!new, ==)
  function Parse<T>(block: Block) : T
  function Marshal<T>(t: T) : Block
  lemma ParseAxiom<T>(t: T)
    ensures Parse(Marshal(t)) == t

  type Pointer = Option<Address>
  type Ranking = map<Address, nat>  // Used by Linked* layers to show acyclicity.

  datatype DiskView = DiskView(entries: map<Address, Block>)
  {
    predicate IsSubDisk(bigger: DiskView)
    {
      IsSubMap(entries, bigger.entries)
    }

    predicate AgreesWithDisk(other: DiskView)
    {
      MapsAgree(entries, other.entries)
    }
    
    predicate Tight()
    {
      forall other:DiskView | other.IsSubDisk(this) :: other == this
    }

    predicate IsNondanglingPointer(ptr: Pointer)
    {
      ptr.Some? ==> ptr.value in entries
    }

    function {:opaque} MergeDisk(other: DiskView) : (out: DiskView)
      // ensure result is sound -- keys and their values must come from one of these places
      ensures forall addr | addr in out.entries 
        :: || (addr in entries && out.entries[addr] == entries[addr])
           || (addr in other.entries && out.entries[addr] == other.entries[addr])
      // ensure result is complete -- result must contain all the keys
      ensures entries.Keys <= out.entries.Keys
      ensures other.entries.Keys <= out.entries.Keys
    {
      DiskView.DiskView(MapUnion(entries, other.entries))
    }
  }

  // check journal linked layer
  // safety: induction based
  // TLA lets you write predicate over infinite sequence of state
  // - spec (accepts a set of execution)
  // - safety (also accept a set of execution)

  // liveness:
  // - you have to write different statements (much easier to understand if you look at sets of 
  // executions and not a collapsed state)
  // - proof also take advantage of the conciseness of high order description
  // - you can't tell liveness unless you can see the infinite sequence of behaviors
  //  (any finite sequence cannot invalidate that)

  // performance properties are all safety properties
  // - bounded steps before actions take place
  // the proof you need to write still has the shape of a liveness proof

  // 



}

