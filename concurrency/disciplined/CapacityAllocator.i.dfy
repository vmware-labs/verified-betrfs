include "ConcurrencyTools.s.dfy"
include "../../lib/Checksums/Nonlinear.i.dfy"
include "ShardedHashTable.i.dfy"
//include "VerificationObligation.s.dfy"

// we need to import this open to destructure AllocatorBin: dafny doesn't support qualified names in this context
module CapacityAllocatorTypes {
  import opened NativeTypes
  import opened ShardedHashTable

  linear datatype AllocatorBin = AllocatorBin(
    count: uint32,
    // NB there's a modularity problem here. Maybe we need to pull the capacity concept
    // out of the ShardedHashTable so we can refer to it here?
    glinear resource: ShardedHashTable.Variables)
}

// separate module to avoid name collision
module CapacityAllocator {
  import opened Options
  import opened NativeTypes
  import opened ShardedHashTable
  import opened KeyValueType
  import opened Mutexes
  import opened NonlinearLemmas
  import SHT = ShardedHashTable
  import opened CapacityAllocatorTypes

  type AllocatorMutex = Mutex<AllocatorBin>
  type AllocatorMutexTable = seq<AllocatorMutex>

  function BinInv(bin: AllocatorBin): bool
  {
    && Valid(bin.resource)
    && bin.resource == Variables(unitTable(), bin.count as nat, multiset{}, multiset{})
  }

  function BinCount(): (c: nat)
    ensures c > 0

  function method BinCountImpl(): (c: uint32)
    ensures c as nat == BinCount()

  predicate Inv(o: AllocatorMutexTable)
  {
    && |o| == BinCount()
    && (forall i | 0 <= i < BinCount() :: o[i].inv == BinInv)
  }

  datatype Splitted = Splitted(v': ShardedHashTable.Variables, vi: ShardedHashTable.Variables)

  function Split(v: ShardedHashTable.Variables, amount:nat) : Splitted
    requires v.Variables?;
    requires v.table == unitTable()
    requires v.insert_capacity >= amount
    requires v.tickets == multiset{}
    requires v.stubs == multiset{}
  {
    var v' := Variables(v.table, v.insert_capacity - amount, multiset{}, multiset{});
    var vi := Variables(v.table, amount, multiset{}, multiset{});
    Splitted(v', vi)
  }

  function method CapacityImpl(): (s: uint32)
    ensures s as nat == Capacity()
    
  predicate CapPreInit(s: ShardedHashTable.Variables)
  {
    && s.Variables?
    && s.table == unitTable()
    && s.insert_capacity == Capacity()
    && s.tickets == multiset{}
    && s.stubs == multiset{}
  }

  method {:noNLarith} init(glinear in_r: SHT.Variables)
  returns (mt: AllocatorMutexTable, glinear out_r: SHT.Variables)
  requires CapPreInit(in_r)
  ensures Inv(mt)
  ensures out_r == unit()
  {
    glinear var remaining_r := in_r;

    var total_amount :uint32 := CapacityImpl();
    var bin_count := BinCountImpl();
    mt := [];


    div_leq_numerator(total_amount as int, bin_count as int);
    var quotient :uint32 := total_amount / bin_count;
    var reaminder :uint32 := total_amount % bin_count;
    div_plus_mod_bound(total_amount as nat, bin_count as nat);

    var allocated_sum: nat := 0;
    var i: uint32 := 0;

    while i < bin_count
      invariant i == 0 ==> allocated_sum == 0;
      invariant i > 0 ==> (allocated_sum == quotient as nat * i as nat + reaminder as nat);

      invariant i as int == |mt| <= BinCount()
      invariant forall j:nat | j < i as int :: mt[j].inv == BinInv
      invariant remaining_r.Variables?
      invariant remaining_r.insert_capacity == total_amount as nat - allocated_sum
      invariant remaining_r.table == unitTable()
      invariant remaining_r.tickets == multiset{}
      invariant remaining_r.stubs == multiset{}
    {
      if i > 0 {
        calc >= {
          remaining_r.insert_capacity - quotient as int;
          total_amount as int - allocated_sum - quotient as int;
          total_amount as int - quotient as int * i as int - reaminder as int - quotient as int;
          {
            assert i <= bin_count - 1;
            mul_le_right(quotient as int, i as int, bin_count as int - 1);
          }
          total_amount as nat - quotient as nat * (bin_count - 1) as nat - reaminder as nat - quotient as int;
          {
            distributive_left(quotient as int, bin_count as int - 1, 1);
          }
          total_amount as nat - quotient as nat * bin_count as nat - reaminder as nat;
          {
            div_mul_plus_mod(total_amount as int, bin_count as int);
          }
          0;
        }

        assert remaining_r.insert_capacity >= quotient as nat;
      }

      ghost var prev_sum := allocated_sum;
      var amount := if i == 0 then quotient + reaminder else quotient;
      allocated_sum := allocated_sum + amount as nat;

      ghost var splitted := Split(remaining_r, amount as nat);
      glinear var vi;
      remaining_r, vi := SHT.split(remaining_r, splitted.v', splitted.vi);
      assert BinInv(AllocatorBin(amount, vi));
      var m := new_mutex(AllocatorBin(amount, vi), BinInv);
      mt := mt + [m];

      i := i + 1;

      assert i > 0;

      if i > 1 {
        calc == {
          allocated_sum;
          prev_sum + quotient as nat;
          quotient as nat * (i - 1) as nat + reaminder as nat + quotient as nat;
          {
            assert quotient as nat * (i - 1) as nat + quotient as nat == i as nat * quotient as nat by {
              distributive_right(i as int - 1, 1, quotient as int);
            }
          }
          quotient as nat * i as nat + reaminder as nat;
        }
      }
    } 

    calc == {
      allocated_sum;
      quotient as nat * bin_count as nat + reaminder as nat;
      {
        div_mul_plus_mod(total_amount as int, bin_count as int);
      }
      total_amount as nat;
    }

    out_r := remaining_r;
  }
}

