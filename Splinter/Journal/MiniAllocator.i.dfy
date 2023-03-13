// Copyright 2018-2021 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, and University of Washington
// SPDX-License-Identifier: BSD-2-Clause

include "../Disk/GenericDisk.i.dfy"
include "../../lib/Base/Maps.i.dfy"

module MiniAllocatorMod {
  import opened Maps
  import opened Options
  import opened GenericDisk

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

    predicate MaxFreeAddr(addr: Address) 
      requires FreeAddr({addr})
    {
      forall freeAddr | FreeAddr({freeAddr}) :: MaxAddr(addr, freeAddr) == addr
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

  datatype MiniAllocator = MiniAllocator(allocs: map<AU, PageAllocator>, curr: Option<AU>) {
    predicate WF() {
      && forall au | au in allocs :: allocs[au].WF(au)
      && curr.Some? ==> curr.value in allocs
    }

    function AddAUs(aus: set<AU>) : MiniAllocator
      requires aus !! allocs.Keys
    {
      var newAllocs := map addr | addr in aus + allocs.Keys :: 
        if addr in allocs then allocs[addr] else PageAllocator({}, {});
      MiniAllocator(newAllocs, curr)
    }

    // mini allocator's job is to allocate freespace and manage reserved pages
    // as long as there are no reserved pages, it can be safely removed from the mini allocator
    predicate CanRemove(au: AU) {
      && au in allocs
      && allocs[au].NoOutstandingRefs() 
    }

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
      var newcurr := if curr.Some? && curr.value in aus then None else curr;
      MiniAllocator(map au | au in allocs :: 
        if au in aus then allocs[au].UnobserveAll() else allocs[au], newcurr)
    }

    predicate CanAllocate(addr: Address)
    {
      && addr.au in allocs
      && allocs[addr.au].FreeAddr({addr})
      && (curr.Some? ==> addr.au == curr.value)
      && (curr.None? ==> allocs[addr.au].NoObservedPages() && allocs[addr.au].NoOutstandingRefs())
    }

    predicate MaxAddr(addr: Address) 
    {
      && CanAllocate(addr)
      && var alloc := if curr.None? then allocs[addr.au] else allocs[curr.value];
      && alloc.MaxFreeAddr(addr)
    }

    function AllocateAndObserve(addr: Address) : MiniAllocator
      requires CanAllocate(addr)
    {
      var result := allocs[addr.au].Observe({addr});
      MiniAllocator(allocs[addr.au := result], Some(addr.au))
    }

    // no longer allocating from the current AU unless all of its pages become free
    // probably don't need this as journal unobserve all pages at once
    // function SealCurrentAU() : MiniAllocator
    //   requires curr.Some?
    // {
    //   MiniAllocator(allocs, None)
    // }

    // remove AUs from the mini allocator
    function Prune(aus: set<AU>) : MiniAllocator
      requires forall au | au in aus :: CanRemove(au)
    {
      var newAllocs := MapRestrict(allocs, set au | au in allocs.Keys - aus);
      var newCurr := if curr.Some? && curr.value in aus then None else curr;
      MiniAllocator(newAllocs, newCurr)
    }

    // All AUs = freeset AUs !! RC AUs !! Unobserved MiniAllocator AUs
  }
}

// frozen freeset = freeset + unobserved AUs 
// Allocated Unobserved = not in freeset, reachable from a stack reference
// Observed = reachable from superblock


