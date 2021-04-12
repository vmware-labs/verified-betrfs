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

  function AllowedSize(): (s: nat)
    ensures 0 < s < FixedSize()

  function method AllowedSizeImpl(): (s: uint32)
    ensures s as nat == AllowedSize()
    
  predicate CapPreInit(s: HTResource.R) {
    && s.R?
    && s.table == unitTable()
    && s.insert_capacity == AllowedSize()
    && s.tickets == multiset{}
    && s.stubs == multiset{}
  }

  lemma test(a: nat, b: nat, q: nat, r: nat)
    requires b >= 1
    requires q == a / b
    requires r == a % b

    ensures r + q <= a;
  {
    assert a == q * b + r; 
    assert r + q <= a;
  }

  method init(linear in_r: ARS.R)
  returns (mt: AllocatorMutexTable, linear out_r: ARS.R)
  requires CapPreInit(in_r)
  // ensures Inv(mt)
  // ensures out_r == unit()
  {
    linear var remaining_r := in_r;

    var total_amount :uint32 := AllowedSizeImpl();
    var bin_count := BinCountImpl();
    mt := [];

    var quotient :uint32 := total_amount / bin_count;
    var reaminder :uint32 := total_amount % bin_count;
    test(total_amount as nat, bin_count as nat, quotient as nat, reaminder as nat);

    var allocated_sum: nat := 0;
    var i: uint32 := 0;

    while i < bin_count
      invariant i == 0 ==> allocated_sum == 0;
      invariant i > 0 ==> (allocated_sum == quotient as nat * i as nat + reaminder as nat);
      invariant allocated_sum <= total_amount as nat;

      // invariant i as int == |mt| <= BinCount()
      // invariant forall j:nat | j < i as int :: mt[j].inv == BinInv
      // invariant remaining_r.R?
      // invariant remaining_r.insert_capacity == total_amount as nat - allocated_sum
      // invariant remaining_r.table == unitTable()
      // invariant remaining_r.tickets == multiset{}
      // invariant remaining_r.stubs == multiset{}
    {
      var amount := if i == 0 then quotient + reaminder else quotient;
      allocated_sum := allocated_sum + amount as nat;

      // ghost var splitted := Split(remaining_r, amount as nat);
      // linear var ri;
      // remaining_r, ri := ARS.split(remaining_r, splitted.r', splitted.ri);
      // var m := new_mutex(AllocatorBin(amount, ri), BinInv);
      // mt := mt + [m];

      i := i + 1;

      assert allocated_sum <= total_amount as nat by {
        calc <=
        {
          allocated_sum;
          quotient as nat * i as nat + reaminder as nat;
          {
            assert i <= bin_count;
          }
          quotient as nat * bin_count as nat + reaminder as nat;
          total_amount as nat;
        }
      }
    } 

    out_r := remaining_r;
  }
}

