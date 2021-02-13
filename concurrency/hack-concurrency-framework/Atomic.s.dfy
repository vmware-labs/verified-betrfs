module AtomicSpec {
  type {:extern} Atomic<V, G>

  predicate {:extern} atomic_inv<V, G>(atomic: Atomic<V, G>, v: V, g: G)

  method {:extern} new_atomic<V, G>(v: V, ghost g: G,
      inv: (V, G) -> bool)
  returns (a: Atomic<V, G>)
  requires inv(v, g)
  ensures forall v1, g1 :: atomic_inv(a, v1, g1) <==> inv(v1, g1)

  
  // atomic fetch-and-add-1

  predicate fetch_add_1(cur_value: int, new_value: int, ret: int)
  {
    && new_value == cur_value + 1
    && ret == cur_value
  }

  method {:extern} atomic_fetch_add_1<G, H, H'>(
      atomic: Atomic<int, G>,
      linear ghost h: H,
      ghost fn: 
        (int, int, int, linear G, linear H) ~> linear (linear G, linear H')
  returns (ret: int,
      ghost cur_value: int,
      ghost new_value: int,
      ghost ret: int,
      ghost g: G,
      ghost linear h': H)
  requires forall new_value, ret :: fetch_add_1(cur_value, new_value, ret) && atomic_inv(atomic, cur_value, g) ==> fn.requires(cur_value, new_value, ret, g, h)
  requires forall new_value, ret :: fetch_add_1(cur_value, new_value, ret) ==> atomic_inv(atomic, cur_value, g) ==> atomic_inv(atomic, new_value, fn(cur_value, new_value, ret, g, h).0)
  ensures fetch_add_1(cur_value, new_value, ret)
  ensures atomic_inv(atomic, cur_value, g)
  ensures h' == fn(cur_value, new_value, ret, g, h).1
  //{
  // C++ impl:
  // std::atomic::fetch_add
  //}
}
