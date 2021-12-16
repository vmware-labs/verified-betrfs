include "../../lib/Lang/NativeTypes.s.dfy"
include "../Math/Math.i.dfy"

module Constants {
  import opened NativeTypes
  import NonlinearLemmas
  import Math

  function method PLATFORM_CACHELINE_SIZE_64(): uint64 { 64 }
  function method ENTRIES_PER_BATCH_32(): uint32 { 64 }

  datatype PreConfig = PreConfig(
    cache_size: uint32,
    num_disk_pages: uint64,
    pages_per_extent: uint64
  )
  {
    predicate WF() {
      && cache_size as int % PLATFORM_CACHELINE_SIZE_64() as int == 0
      && cache_size as int % ENTRIES_PER_BATCH_32() as int == 0
      && cache_size as int > 0
      && cache_size as int < 0x4000_0000
      && 0 < num_disk_pages as int < 0x1_0000_0000_0000
      && pages_per_extent != 0
      && pages_per_extent <= 0x1_0000
    }
  }

  datatype Config = Config(
    cache_size: uint32,
    num_disk_pages: uint64,

    pages_per_extent: uint64,

    batch_capacity: uint64,
    cacheline_capacity: uint64
  )
  {
    predicate WF() {
      && cacheline_capacity != 0
      && pages_per_extent != 0
      && pages_per_extent <= 0x1_0000
      && cache_size as int == cacheline_capacity as int * PLATFORM_CACHELINE_SIZE_64() as int
      && cache_size as int == batch_capacity as int * ENTRIES_PER_BATCH_32() as int
      && cache_size as int * RC_WIDTH < 0x1_0000_0000
      && num_disk_pages as int * 4096 < 0x1000_0000_0000_0000
      && 0 < num_disk_pages as int
    }
  }

  method fromPreConfig(pre: PreConfig) returns (config: Config)
  requires pre.WF()
  ensures config.WF()
  {
    config := Config(pre.cache_size, pre.num_disk_pages, pre.pages_per_extent,
        pre.cache_size as uint64 / ENTRIES_PER_BATCH_32() as uint64,
        pre.cache_size as uint64 / PLATFORM_CACHELINE_SIZE_64());
  }

  ghost const RC_WIDTH := 4;

  ghost const CHUNK_SIZE := 64;
  ghost const CLEAN_AHEAD := 512;

  ghost const NUM_IO_SLOTS := 256;
  ghost const AIO_HAND_BATCH_SIZE := 32;

  function method CHUNK_SIZE_32(): uint32 { 64 }
  function method AIO_HAND_BATCH_SIZE_64(): uint64 { 32 }
  function method NUM_IO_SLOTS_64(): uint64 { 256 }
  function method DEFAULT_MAX_IO_EVENTS_64(): uint64 { 32 }
  function method RC_WIDTH_64(): uint64 { 4 }
  function method CLEAN_AHEAD_64(): uint64 { 512 }

  function method {:opaque} rc_index(config: Config, j: uint64, i: uint32) : (k: uint64)
  requires config.WF()
  requires 0 <= j as int < RC_WIDTH as int
  requires 0 <= i as int < config.cache_size as int
  ensures 0 <= k as int < RC_WIDTH as int * config.cache_size as int
  {
    NonlinearLemmas.mod_bound(i as int, config.cacheline_capacity as int);
    Math.div_bound(i as int, config.cacheline_capacity as int);
    Math.mod_div_transpose_bound(i as int, config.cacheline_capacity as int,
        PLATFORM_CACHELINE_SIZE_64() as int);
    NonlinearLemmas.mul_le_left(j as int, config.cache_size as int, RC_WIDTH as int - 1);

    //var cacheline_capacity := config.cache_size / PLATFORM_CACHELINE_SIZE_64() as uint32;
    //assert cacheline_capacity as int == CACHELINE_CAPACITY();
    var rc_number := (i % config.cacheline_capacity as uint32) * PLATFORM_CACHELINE_SIZE_64() as uint32
        + (i / config.cacheline_capacity as uint32);
    (j as uint32 * config.cache_size + rc_number) as uint64
  }

  lemma inverse_rc_index(config: Config, k: int)
  returns (j: int, i: int)
  requires config.WF()
  requires 0 <= k as int < RC_WIDTH as int * config.cache_size as int
  ensures 0 <= j as int < RC_WIDTH as int
  ensures 0 <= i as int < config.cache_size as int
  ensures k == rc_index(config, j as uint64, i as uint32) as int
  {
    j := k / config.cache_size as int;
    var rc_number := k % config.cache_size as int;

    var cacheline_capacity: int := (config.cache_size as int / PLATFORM_CACHELINE_SIZE_64() as int) as int;
    //assert cacheline_capacity as int == CACHELINE_CAPACITY();

    i := (rc_number % (PLATFORM_CACHELINE_SIZE_64() as int)) * cacheline_capacity
        + (rc_number / (PLATFORM_CACHELINE_SIZE_64() as int));

    var rc_number2 := (i % cacheline_capacity) * (PLATFORM_CACHELINE_SIZE_64() as int)
        + (i / cacheline_capacity);

    if j >= RC_WIDTH as int {
      NonlinearLemmas.div_mul_plus_mod(k, config.cache_size as int);
      NonlinearLemmas.mod_bound(k, config.cache_size as int);
      NonlinearLemmas.mul_le_left(RC_WIDTH as int, k / config.cache_size as int,
          config.cache_size as int);
      assert false;
    }
    assert 0 <= j by {
      Math.div_bound(k, config.cache_size as int);
    }

    if i / cacheline_capacity >= PLATFORM_CACHELINE_SIZE_64() as int {
      NonlinearLemmas.div_mul_plus_mod(i, cacheline_capacity);
      NonlinearLemmas.mod_bound(i, cacheline_capacity);
      NonlinearLemmas.mul_le_left(PLATFORM_CACHELINE_SIZE_64() as int,
          i / cacheline_capacity, cacheline_capacity);
    }

    NonlinearLemmas.mod_bound(rc_number, PLATFORM_CACHELINE_SIZE_64() as int);
    Math.div_bound(rc_number, PLATFORM_CACHELINE_SIZE_64() as int);
    Math.mod_div_transpose_bound(rc_number,
        PLATFORM_CACHELINE_SIZE_64() as int,
        config.cacheline_capacity as int);

    NonlinearLemmas.mod_bound(i as int, config.cacheline_capacity as int);
    Math.div_bound(i as int, config.cacheline_capacity as int);
    Math.mod_div_transpose_bound(i as int, config.cacheline_capacity as int,
        PLATFORM_CACHELINE_SIZE_64() as int);

    NonlinearLemmas.mul_le_left(j as int, config.cache_size as int, RC_WIDTH as int - 1);

    calc {
      rc_number2 % (PLATFORM_CACHELINE_SIZE_64() as int);
      (i / cacheline_capacity);
      {
        Math.lemma_div_multiples_vanish_fancy(
            (rc_number % (PLATFORM_CACHELINE_SIZE_64() as int)),
            (rc_number / (PLATFORM_CACHELINE_SIZE_64() as int)),
            cacheline_capacity);
        NonlinearLemmas.mul_comm(
            (rc_number % (PLATFORM_CACHELINE_SIZE_64() as int)),
            cacheline_capacity);
      }
      rc_number % (PLATFORM_CACHELINE_SIZE_64() as int);
    }

    calc {
      rc_number2 / (PLATFORM_CACHELINE_SIZE_64() as int);
      {
        /*
        Math.lemma_div_multiples_vanish_fancy(
            i % cacheline_capacity, i / cacheline_capacity,
            PLATFORM_CACHELINE_SIZE_64() as int);
        NonlinearLemmas.mul_comm(i % cacheline_capacity,
            PLATFORM_CACHELINE_SIZE_64() as int);
            */
      }
      (i % cacheline_capacity);
      {
        Math.abc_mod(
          (rc_number % (PLATFORM_CACHELINE_SIZE_64() as int)),
          cacheline_capacity,
          (rc_number / (PLATFORM_CACHELINE_SIZE_64() as int)));
      }
      rc_number / (PLATFORM_CACHELINE_SIZE_64() as int);
    }

    calc {
      k;
      {
        NonlinearLemmas.div_mul_plus_mod(k, config.cache_size as int);
      }
      (k / config.cache_size as int) * config.cache_size as int + k % config.cache_size as int;
      {
        assert rc_number == rc_number2;
        reveal_rc_index();
      }
      rc_index(config, j as uint64, i as uint32) as int;
    }
  }

  lemma rc_index_inj(config: Config, j1: int, i1: int, j2: int, i2: int)
  requires config.WF()
  requires 0 <= j1 as int < RC_WIDTH as int
  requires 0 <= i1 as int < config.cache_size as int
  requires 0 <= j2 as int < RC_WIDTH as int
  requires 0 <= i2 as int < config.cache_size as int
  ensures rc_index(config, j1 as uint64, i1 as uint32)
      == rc_index(config, j2 as uint64, i2 as uint32) ==> i1 == i2 && j1 == j2
  {
    if rc_index(config, j1 as uint64, i1 as uint32)
      == rc_index(config, j2 as uint64, i2 as uint32)
    {
      reveal_rc_index();

      var rc_number1 := (i1 % config.cacheline_capacity as int) * PLATFORM_CACHELINE_SIZE_64() as int
          + (i1 / config.cacheline_capacity as int);

      Math.mod_div_transpose_bound(i1 as int, config.cacheline_capacity as int,
          PLATFORM_CACHELINE_SIZE_64() as int);

      var rc_number2 := (i2 % config.cacheline_capacity as int) * PLATFORM_CACHELINE_SIZE_64() as int
          + (i2 / config.cacheline_capacity as int);

      Math.mod_div_transpose_bound(i2 as int, config.cacheline_capacity as int,
          PLATFORM_CACHELINE_SIZE_64() as int);

      var k := rc_index(config, j1 as uint64, i1 as uint32) as int;

      calc {
        rc_number1;
        { Math.abc_mod(j1, config.cache_size as int, rc_number1); }
        k % config.cache_size as int;
        { Math.abc_mod(j2, config.cache_size as int, rc_number2); }
        rc_number2;
      }

      Math.ab_div_lt(PLATFORM_CACHELINE_SIZE_64() as int,
          config.cacheline_capacity as int, i1);
      Math.ab_div_lt(PLATFORM_CACHELINE_SIZE_64() as int,
          config.cacheline_capacity as int, i2);

      calc {
        i1 / config.cacheline_capacity as int;
        {
          Math.abc_mod(i1 % config.cacheline_capacity as int,
            PLATFORM_CACHELINE_SIZE_64() as int,
            i1 / config.cacheline_capacity as int);
        }
        rc_number1 % PLATFORM_CACHELINE_SIZE_64() as int;
        rc_number2 % PLATFORM_CACHELINE_SIZE_64() as int;
        i2 / config.cacheline_capacity as int;
      }

      calc {
        i1 % config.cacheline_capacity as int;
        rc_number1 / PLATFORM_CACHELINE_SIZE_64() as int;
        rc_number2 / PLATFORM_CACHELINE_SIZE_64() as int;
        i2 % config.cacheline_capacity as int;
      }

      NonlinearLemmas.div_mul_plus_mod(i1, config.cacheline_capacity as int);
      NonlinearLemmas.div_mul_plus_mod(i2, config.cacheline_capacity as int);

      calc {
        j1;
        {
          Math.lemma_div_multiples_vanish_fancy(j1, rc_number2, config.cache_size as int);
          NonlinearLemmas.mul_comm(j1, config.cache_size as int);
        }
        k / config.cache_size as int;
        {
          Math.lemma_div_multiples_vanish_fancy(j2, rc_number2, config.cache_size as int);
          NonlinearLemmas.mul_comm(j2, config.cache_size as int);
        }
        j2;
      }
    }
  }

}
