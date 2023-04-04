// Copyright 2018-2021 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, and University of Washington
// SPDX-License-Identifier: BSD-2-Clause

include "../Disk/GenericDisk.i.dfy"
include "../../lib/Base/Maps.i.dfy"
include "../../lib/Base/Sets.i.dfy"

module MiniAllocatorMod {
  import opened Maps
  import opened Sets
  import opened Options
  import opened GenericDisk

  datatype PageAllocator = PageAllocator(
    observed: set<Address>, // pages reachable from superblock Repr
    reserved: set<Address>, // pages reachable from stack ref
    au: AU
  ) {
    predicate WF() {
      // && observed !! reserved // does not have to be disjoint, cow case
      // && |observed + reserved| <= PageCount()
      && (forall addr | addr in observed + reserved :: addr.WF())
      && (forall addr | addr in observed + reserved:: addr.au == au)
    }

    predicate FreeAddr(addr: Address) {
      && addr.WF() 
      && addr.au == au
      && addr !in (observed + reserved)
    }

    // get a stack reference
    function Reserve(addrs: set<Address>) : (out: PageAllocator)
      requires WF()
      requires forall addr | addr in addrs :: FreeAddr(addr)
      ensures out.WF()
    {
      PageAllocator(observed, reserved + addrs, au)
    }

    // done with / returns a stack reference 
    function UnReserve(addrs: set<Address>) : (out: PageAllocator)
      requires WF()
      requires addrs <= reserved
      ensures out.WF()
    {
      PageAllocator(observed, reserved - addrs, au)
    }

    function Observe(addrs: set<Address>) : (out: PageAllocator)
      requires WF()
      requires forall addr | addr in addrs :: addr.WF() && addr.au == au
      ensures out.WF()
    {
      PageAllocator(observed+addrs, reserved, au)
    }

    function Unobserve(addrs: set<Address>) : (out: PageAllocator)
      requires WF()
      requires addrs <= observed
      ensures out.WF()
    {
      PageAllocator(observed-addrs, reserved, au)
    }

    function UnobserveAll() : (out: PageAllocator)
      requires WF()
      ensures out.WF()
    {
      Unobserve(observed)
    }

    function Free(addrs: set<Address>) : (out: PageAllocator)
      requires WF()
      requires addrs <= observed + reserved 
      ensures out.WF()
    {
      PageAllocator(observed-addrs, reserved-addrs, au)
    }

    predicate NoObservedPages() {
      && observed == {}
    }

    predicate NoOutstandingRefs () {
      && reserved == {}
    }

    predicate AllPagesAllocated () {
      && |reserved + observed| == PageCount()
    }

    predicate AllPagesFree() {
      && NoObservedPages()
      && NoOutstandingRefs()
    }
  }

  function EmptyMiniAllocator() : MiniAllocator {
    MiniAllocator(map[], None)
  }

  datatype MiniAllocator = MiniAllocator(
    allocs: map<AU, PageAllocator>, 
    curr: Option<AU>) 
  {
    predicate WF() {
      && (forall au | au in allocs :: allocs[au].WF() && allocs[au].au == au)
      && (curr.Some? ==> curr.value in allocs)
    }

    function GetAllReserved() : (out: set<Address>) {
      UnionSetOfSets(set au: AU | au in allocs :: allocs[au].reserved)
    }

    function GetAllReservedAU() : (out: set<AU>) {
      set au | au in allocs && allocs[au].reserved != {} :: au
    }

    function AddAUs(aus: set<AU>) : (out: MiniAllocator)
      requires WF()
      requires aus !! allocs.Keys
      ensures out.WF()
    {
      var newAllocs := map au | au in aus + allocs.Keys :: 
        if au in allocs then allocs[au] else PageAllocator({}, {}, au);
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
    function UnobserveAUs(aus: set<AU>) : (out: MiniAllocator)
      requires WF()
      requires aus <= allocs.Keys
      ensures out.WF()
    {
      var newcurr := if curr.Some? && curr.value in aus then None else curr;
      MiniAllocator(map au | au in allocs :: 
        if au in aus then allocs[au].UnobserveAll() else allocs[au], newcurr)
    }

    predicate CanAllocate(addr: Address)
    {
      && addr.au in allocs
      && allocs[addr.au].FreeAddr(addr)
    }

    function AllocateAndObserve(addr: Address) : (out: MiniAllocator)
      requires WF()
      requires CanAllocate(addr)
      ensures out.WF()
    {
      var result := allocs[addr.au].Observe({addr});
      var newCurr := if allocs[addr.au].AllPagesAllocated() then None else Some(addr.au);
      MiniAllocator(allocs[addr.au := result], newCurr)
    }

    function Allocate(addr: Address) : (out: MiniAllocator)
      requires WF()
      requires CanAllocate(addr)
      ensures out.WF()
    {
      var result := allocs[addr.au].Reserve({addr});
      var newCurr := if allocs[addr.au].AllPagesAllocated() then None else Some(addr.au);
      MiniAllocator(allocs[addr.au := result], newCurr)
    }

    // no longer allocating from the current AU unless all of its pages become free
    // probably don't need this as journal unobserve all pages at once
    // function SealCurrentAU() : MiniAllocator
    //   requires curr.Some?
    // {
    //   MiniAllocator(allocs, None)
    // }

    // remove AUs from the mini allocator
    function Prune(aus: set<AU>) : (out: MiniAllocator)
      requires WF()
      requires forall au | au in aus :: CanRemove(au)
      ensures out.WF()
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


