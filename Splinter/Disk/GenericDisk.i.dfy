// Copyright 2018-2021 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, and University of Washington
// SPDX-License-Identifier: BSD-2-Clause

include "../../lib/Base/Option.s.dfy"
include "../../lib/Base/Maps.i.dfy"

abstract module AddressTypeMod {
  type Address(!new, ==)
}

module GenericDisk(address: AddressTypeMod) {
  import opened Options
  import opened Maps

  type Block(!new, ==)
  function Parse<T>(block: Block) : T
  function Marshal<T>(t: T) : Block
  lemma ParseAxiom<T>(t: T)
    ensures Parse(Marshal(t)) == t

  type Address = address.Address
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
  }
}

