// Copyright 2018-2021 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, and University of Washington
// SPDX-License-Identifier: BSD-2-Clause

include "../Disk/GenericDisk.i.dfy"
include "../../lib/Base/Maps.i.dfy"

module MiniAllocatorMod {
  import opened GenericDisk
  import opened Maps

  datatype PageAllocator = PageAllocator(
    observed: set<Address>, // pages reachable from superblock Repr
    reserved: set<Address> // pages reachable from stack ref
  ) {
    predicate WF(au: AU) {
      // && observed !! reserved // does not have to be disjoint, cow case
      && |observed + reserved| <= PageCount()
      && (forall addr | addr in observed + reserved :: addr.WF())
      && (forall addr | addr in observed + reserved:: addr.au == au)
    }

    predicate FreeAddr(addrs: set<Address>) {
      && (forall addr | addr in addrs :: addr.WF())
      && addrs !! (observed + reserved)
    }

    // get a stack reference
    function Reserve(addrs: set<Address>) : PageAllocator
      requires FreeAddr(addrs)
    {
      PageAllocator(observed, reserved + addrs)
    }

    // done with / returns a stack reference 
    function UnReserve(addrs: set<Address>) : PageAllocator
      requires addrs <= reserved
    {
      PageAllocator(observed, reserved - addrs)
    }

    function Observe(addrs: set<Address>) : PageAllocator
    {
      PageAllocator(observed+addrs, reserved)
    }

    function Unobserve(addrs: set<Address>) : PageAllocator
      requires addrs <= observed
    {
      PageAllocator(observed-addrs, reserved)
    }

    function UnobserveAll() : PageAllocator
    {
      Unobserve(observed)
    }

    function Free(addrs: set<Address>) : PageAllocator
      requires addrs <= observed + reserved 
    {
      PageAllocator(observed-addrs, reserved-addrs)
    }

    predicate NoObservedPages() {
      && observed == {}
    }

    predicate NoOutstandingRefs () { // is this a bad name?
      && reserved == {}
    }
  }

  datatype MiniAllocator = MiniAllocator(allocs: map<AU, PageAllocator>) {
    predicate WF() {
      && forall au | au in allocs :: allocs[au].WF(au)
    }

    function AddAUs(aus: set<AU>) : MiniAllocator
      requires aus !! allocs.Keys
    {
      var newAllocs := map addr | addr in aus + allocs.Keys :: 
        if addr in allocs then allocs[addr] else PageAllocator({}, {});
      MiniAllocator(newAllocs)
    }

    // mini allocator's job is to allocate freespace and manage reserved pages
    // as long as there are no reserved pages, it can be safely removed from the mini allocator
    predicate CanRemove(au: AU) {
      && au in allocs
      && allocs[au].NoOutstandingRefs() 
    }

    // predicate FreeOnRemove(au: AU) {
    //   && alloc.observed == {}
    // }

    // a set of AUs that belongs to the frozen freeset
    function NotObservedAUs() : set<AU>
    {
      set au | au in allocs && allocs[au].NoObservedPages() :: au
    }

    // b+tree wouldn't do this
    // journal use it to unobserve discarded AUs at once
    function UnobserveAUs(aus: set<AU>) : MiniAllocator
      requires aus <= allocs.Keys
    {
      MiniAllocator(map au | au in allocs :: 
        if au in aus then allocs[au].UnobserveAll() else allocs[au])
    }

    predicate CanAllocate(addr: Address)
    {
      && addr.au in allocs
      && allocs[addr.au].FreeAddr({addr})
    }

    function AllocateAndObserve(addr: Address) : MiniAllocator
      requires CanAllocate(addr)
    {
      var result := allocs[addr.au].Observe({addr});
      MiniAllocator(allocs[addr.au := result])
    }

    // remove AUs from the mini allocator
    function Prune(aus: set<AU>) : MiniAllocator
      requires forall au | au in aus :: CanRemove(au)
    {
      MiniAllocator(MapRestrict(allocs, set au | au in allocs.Keys - aus))
    }

    // All AUs = freeset AUs !! RC AUs !! Unobserved MiniAllocator AUs
  }
}

// frozen freeset = freeset + unobserved AUs 
// Allocated Unobserved = not in freeset, reachable from a stack reference
// Observed = reachable from superblock


