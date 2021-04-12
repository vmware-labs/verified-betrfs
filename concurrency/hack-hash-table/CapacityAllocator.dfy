include "../framework/Mutex.s.dfy"
include "HTResource.i.dfy"
include "Main.s.dfy"

module CapacityAllocator {
  import opened Options
  import opened NativeTypes
  import opened HTResource
  import opened KeyValueType
  import opened Mutexes
  import ARS = HTResource

  linear datatype AllocatorBin = AllocatorBin(
    count: uint32,
    linear resource: HTResource.R)

  type AllocatorMutex = Mutex<AllocatorBin>
  type AllocatorMutexTable = seq<AllocatorMutex>

  function BinInv(bin: AllocatorBin): bool
  {
    && Valid(bin.resource)
    && bin.resource == R(unitTable(), bin.count as nat, multiset{}, multiset{})
  }

  function BinCount(): (c: nat)
    ensures c > 0

  function method BinCountImpl(): (c: uint32)
    ensures c as nat == BinCount()

  predicate Inv(o: AllocatorMutexTable) {
    && |o| == BinCount()
    && (forall i | 0 <= i < BinCount()
      :: o[i].inv == BinInv)
  }

  datatype Splitted = Splitted(r': HTResource.R, ri: HTResource.R)

  function Split(r: HTResource.R, amount:nat) : Splitted
    requires r.R?;
    requires r.table == unitTable()
    requires r.insert_capacity >= amount
    requires r.tickets == multiset{}
    requires r.stubs == multiset{}
  {
    var r' := R(r.table, r.insert_capacity - amount, multiset{}, multiset{});
    var ri := R(r.table, amount, multiset{}, multiset{});
    Splitted(r', ri)
  }

  predicate CapPreInit(s: HTResource.R) {
    && s.R?
    && s.table == unitTable()
    && s.insert_capacity == FixedSize() - 1
    && s.tickets == multiset{}
    && s.stubs == multiset{}
  }

  method init(linear in_r: ARS.R)
  returns (mt: AllocatorMutexTable, linear out_r: ARS.R)
  requires CapPreInit(in_r)
  ensures Inv(mt)
  // ensures out_r == unit()
  {
    linear var remaining_r := in_r;
    mt := [];

    var i: uint32 := 0;
    var quotient: uint32 := FixedSizeImpl() / BinCountImpl();
    // var remainder: uint32 := FixedSizeImpl() % BinCountImpl();
    var allocated_amount :uint32 := 0;
    var unallocated_amount :uint32 := FixedSizeImpl() - 1;

    while i < BinCountImpl()
      invariant i as int == |mt| <= BinCount()
      invariant forall j:nat | j < i as int :: mt[j].inv == BinInv
      invariant remaining_r.R?
      invariant remaining_r.insert_capacity == unallocated_amount as int
      invariant unallocated_amount as nat + allocated_amount as nat == FixedSizeImpl() as nat - 1
      invariant remaining_r.table == unitTable()
      invariant remaining_r.tickets == multiset{}
      invariant remaining_r.stubs == multiset{}
    {
      var amount := if unallocated_amount < quotient then unallocated_amount else quotient;

      ghost var splitted := Split(remaining_r, amount as nat);
      linear var ri;
      remaining_r, ri := ARS.split(remaining_r, splitted.r', splitted.ri);
      var m := new_mutex(AllocatorBin(amount, ri), BinInv);
  
      allocated_amount := allocated_amount + amount;
      unallocated_amount := unallocated_amount - amount;
      mt := mt + [m];
      i := i + 1;


    }

    out_r := remaining_r;
    // assert out_r == unit();
  }
}

