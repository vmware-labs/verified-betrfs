include "../framework/Ptrs.s.dfy"
include "../framework/GlinearMap.s.dfy"
include "../Math/Nonlinear.i.dfy"

module MemSplit {
  import opened Ptrs
  import opened NativeTypes
  import opened NonlinearLemmas
  import opened GlinearMap

  predicate has_single<V>(pta: PointsToArray<V>, width: nat,
      pta_seq: map<nat, PointsToArray<V>>, i: nat)
  {
    && i in pta_seq
    && 0 <= i * width * sizeof<V>() as int < 0x1_0000_0000_0000_0000
    && 0 <= pta.ptr.as_nat() + i * width * sizeof<V>() as int < 0x1_0000_0000_0000_0000
    && pta_seq[i].ptr == ptr_add(pta.ptr,
          (i * width * sizeof<V>() as int) as uint64)
    && |pta_seq[i].s| == width
  }

  predicate is_split<V>(pta: PointsToArray<V>, width: nat, num: nat,
      pta_seq: map<nat, PointsToArray<V>>)
  {
    forall i | 0 <= i < num :: has_single(pta, width, pta_seq, i)
  }

  predicate ind_has_single<V>(ptr: Ptr, m: map<nat, PointsTo<V>>, i: nat)
  {
    && i in m
    && 0 <= i * sizeof<V>() as int < 0x1_0000_0000_0000_0000
    && 0 <= ptr.as_nat() + i * sizeof<V>() as int < 0x1_0000_0000_0000_0000
    && m[i].ptr == ptr_add(ptr, (i * sizeof<V>() as int) as uint64)
  }

  predicate is_ind_split<V>(ptr: Ptr, m: map<nat, PointsTo<V>>, num: nat)
  {
    forall i | 0 <= i < num :: ind_has_single(ptr, m, i)
  }

  glinear method glmap_take_range<V>(glinear m: map<nat, V>, ghost a: nat, ghost b: nat)
  returns (glinear m': map<nat, V>, glinear f: map<nat, V>)
  requires forall i | a <= i < b :: i in m
  ensures forall i | !(a <= i < b) && i in m :: i in m' && m'[i] == m[i]
  ensures forall i | 0 <= i < b-a :: i in f && f[i] == m[a + i]
  {
    if b <= a {
      m' := m;
      f := glmap_empty();
    } else {
      m', f := glmap_take_range(m, a, b-1);
      glinear var x;
      m', x := glmap_take(m', b-1);
      f := glmap_insert(f, b-a-1, x);
    }
  }

  glinear method inds_split<V>(
      ghost pta: PointsToArray<V>,
      glinear m: map<nat, PointsTo<V>>,
      ghost width: nat, ghost num: nat)
  returns (glinear pta_seq: map<nat, PointsToArray<V>>)
  requires num * width >= 0
  requires width > 0
  requires is_ind_split(pta.ptr, m, num * width)
  ensures is_split(pta, width, num, pta_seq)
  decreases num
  {
    if num == 0 {
      pta_seq := glmap_empty();
      dispose_anything(m);
    } else {
      assert 0 <= (num-1) * width by { mul_ge_0(width, num-1); }
      assert 0 <= num * width;
      assert (num-1) * width < num * width by { distributive_right_sub(num, 1, width); }

      forall i | width*(num-1) <= i < width*num ensures i in m
      {
        assert ind_has_single(pta.ptr, m, i);
      }

      glinear var m', pts := glmap_take_range(m, width*(num-1), width*num);

      forall i | 0 <= i < width*(num-1) ensures ind_has_single(pta.ptr, m', i)
      {
        assert ind_has_single(pta.ptr, m, i);
      }

      glinear var pta_seq' := inds_split(pta, m', width, num-1);

      assert 0 <= ((num-1) * width * sizeof<V>() as int) < 0x1_0000_0000_0000_0000
        && 0 <= pta.ptr.as_nat() + ((num-1) * width * sizeof<V>() as int)
          < 0x1_0000_0000_0000_0000
      by {
        assert ind_has_single(pta.ptr, m, (num-1) * width);
      }
      var last_ptr := ptr_add(pta.ptr,
          ((num-1) * width * sizeof<V>() as int) as uint64);

      forall i | 0 <= i < width
      ensures i in pts
      ensures pts[i].ptr.as_nat() == last_ptr.as_nat() + i * sizeof<V>() as nat
      {
        assert num * width - (num - 1) * width == width
          by { distributive_right_sub(num, 1, width); }
        assert (num-1) * width * sizeof<V>() as int + i * sizeof<V>() as int
            == ((num-1) * width + i) * sizeof<V>() as int
        by {
          distributive_right((num-1)*width, i, sizeof<V>() as int);
        }
        assert pts[i] == m[(num-1) * width + i];
        assert ind_has_single(pta.ptr, m, (num-1) * width + i);
      }

      glinear var last_pta := individual_to_array(last_ptr, width, pts);
      pta_seq := glmap_insert(pta_seq', num-1, last_pta);

      forall i | 0 <= i < num
      ensures has_single(pta, width, pta_seq, i)
      {
        if i == num - 1 {
          assert has_single(pta, width, pta_seq, i);
        } else {
          assert has_single(pta, width, pta_seq', i);
          assert has_single(pta, width, pta_seq, i);
        }
      }
    }
  }

  glinear method mem_split<V>(glinear pta: PointsToArray<V>, ghost width: nat, ghost num: nat)
  returns (glinear pta_seq: map<nat, PointsToArray<V>>)
  requires width * num == |pta.s|
  requires width > 0
  ensures is_split(pta, width, num, pta_seq)
  {
    glinear var m := array_to_individual(pta);
    forall i | 0 <= i < |pta.s| ensures ind_has_single(pta.ptr, m, i)
    {
      mul_ge_0(i, sizeof<V>() as int);
      ptrs_eq(m[i].ptr, ptr_add(pta.ptr, (i * sizeof<V>() as int) as uint64));
    }
    pta_seq := inds_split(pta, m, width, num);
  }
}
