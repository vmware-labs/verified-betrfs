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
    pages_per_extent: uint64,
    num_io_slots: uint64
  )
  {
    predicate method WF() {
      && cache_size as uint64 % (PLATFORM_CACHELINE_SIZE_64() * PLATFORM_CACHELINE_SIZE_64()) == 0
      && cache_size % ENTRIES_PER_BATCH_32() == 0
      && cache_size > 0
      && cache_size < 0x4000_0000
      && 0 < num_disk_pages < 0x1_0000_0000_0000
      && pages_per_extent != 0
      && pages_per_extent <= 0x1_0000
      && 0 < num_io_slots <= 0x1_0000
      && num_io_slots % AIO_HAND_BATCH_SIZE_64() == 0
    }
  }

  datatype Config = Config(
    cache_size: uint32,
    num_disk_pages: uint64,

    pages_per_extent: uint64,
    num_io_slots: uint64,

    batch_capacity: uint64,
    cacheline_capacity: uint64
  )
  {
    predicate WF() {
      && cacheline_capacity != 0
      && pages_per_extent != 0
      && pages_per_extent <= 0x1_0000
      && cache_size as int % (PLATFORM_CACHELINE_SIZE_64() as int * PLATFORM_CACHELINE_SIZE_64() as int) == 0
      && cache_size as int == cacheline_capacity as int * PLATFORM_CACHELINE_SIZE_64() as int
      && cache_size as int == batch_capacity as int * ENTRIES_PER_BATCH_32() as int
      && cache_size as int * RC_WIDTH < 0x1_0000_0000
      && num_disk_pages as int * 4096 < 0x1000_0000_0000_0000
      && 0 < num_disk_pages as int
      && 0 < num_io_slots <= 0x1_0000
      && num_io_slots % AIO_HAND_BATCH_SIZE_64() == 0
    }
  }

  method fromPreConfig(pre: PreConfig) returns (config: Config)
  requires pre.WF()
  ensures config.WF()
  {
    config := Config(pre.cache_size, pre.num_disk_pages, pre.pages_per_extent,
        pre.num_io_slots,
        pre.cache_size as uint64 / ENTRIES_PER_BATCH_32() as uint64,
        pre.cache_size as uint64 / PLATFORM_CACHELINE_SIZE_64());
  }

  ghost const RC_WIDTH := 4; // constant

  ghost const CHUNK_SIZE := 64; // constant
  ghost const CLEAN_AHEAD := 512; // constant

  ghost const AIO_HAND_BATCH_SIZE := 32; // constant

  function method CHUNK_SIZE_32(): uint32 { 64 } // constant
  function method AIO_HAND_BATCH_SIZE_64(): uint64 { 32 } // constant
  function method DEFAULT_MAX_IO_EVENTS_64(): uint64 { 32 } // constant
  function method RC_WIDTH_64(): uint64 { 4 } // constant
  function method CLEAN_AHEAD_64(): uint64 { 512 } // constant

  function method {:opaque} ref_internal(i: uint32) : uint32
  {
     var block_modulus := i % (PLATFORM_CACHELINE_SIZE_64() as uint32 * PLATFORM_CACHELINE_SIZE_64() as uint32);
     var column := block_modulus % PLATFORM_CACHELINE_SIZE_64() as uint32;
     var row := block_modulus / PLATFORM_CACHELINE_SIZE_64() as uint32;
     var new_modulus := column * PLATFORM_CACHELINE_SIZE_64() as uint32 + row;
     i - block_modulus + new_modulus
  }

  lemma ref_internal_bound(i: uint32, cache_size: nat)
  requires cache_size % (PLATFORM_CACHELINE_SIZE_64() as int * PLATFORM_CACHELINE_SIZE_64() as int) == 0
  requires 0 <= i as int < cache_size
  ensures 0 <= ref_internal(i) as int < cache_size
  {
     reveal_ref_internal();

     var sqr := (PLATFORM_CACHELINE_SIZE_64() as int * PLATFORM_CACHELINE_SIZE_64() as int);

     var block_modulus := i as int % sqr;
     var column := block_modulus % PLATFORM_CACHELINE_SIZE_64() as int;
     var row := block_modulus / PLATFORM_CACHELINE_SIZE_64() as int;
     var new_modulus := column * PLATFORM_CACHELINE_SIZE_64() as int + row;

     assert (i as int - block_modulus) <= cache_size - sqr
     by {
       calc {
          i as int - block_modulus;
          == { NonlinearLemmas.div_mul_plus_mod(i as int, sqr); }
          (i as int / sqr) * sqr;
          <= {
              if i as int / sqr > cache_size / sqr - 1 {
                  assert i as int / sqr >= cache_size / sqr;
                  calc {
                      i as int;
                      >= { NonlinearLemmas.div_mul_plus_mod(i as int, sqr); }
                      (i as int / sqr) * sqr;
                      >= { NonlinearLemmas.mul_le_left(cache_size as int / sqr, i as int / sqr, sqr); }
                      (cache_size as int / sqr) * sqr;
                      == { NonlinearLemmas.div_mul_plus_mod(cache_size as int, sqr); }
                      cache_size;
                  }
                  assert i as int >= cache_size;
                  assert false;
              }
              NonlinearLemmas.mul_le_left(i as int / sqr, cache_size / sqr - 1, sqr);
          }
          (cache_size / sqr - 1) * sqr;
          == { NonlinearLemmas.distributive_right_sub(cache_size / sqr, 1, sqr); }
          (cache_size / sqr) * sqr - sqr;
          == { NonlinearLemmas.div_mul_plus_mod(cache_size, sqr); }
          cache_size - sqr;
       }
     }

     assert new_modulus < sqr;
  }

  function method {:opaque} rc_index(config: Config, j: uint64, i: uint32) : (k: uint64)
  requires config.WF()
  requires 0 <= j as int < RC_WIDTH as int
  requires 0 <= i as int < config.cache_size as int
  ensures 0 <= k as int < RC_WIDTH as int * config.cache_size as int
  {
    ref_internal_bound(i, config.cache_size as nat);
    NonlinearLemmas.mul_le_left(j as int, config.cache_size as int, RC_WIDTH as int - 1);

    var rc_number := ref_internal(i);
    (j as uint32 * config.cache_size + rc_number) as uint64
  }

  lemma ref_internal_ref_internal(i: uint32)
  ensures ref_internal(ref_internal(i)) == i
  {
    reveal_ref_internal();
    var block_modulus := i as int % (PLATFORM_CACHELINE_SIZE_64() as int * PLATFORM_CACHELINE_SIZE_64() as int);
    var column := block_modulus % PLATFORM_CACHELINE_SIZE_64() as int;
    var row := block_modulus / PLATFORM_CACHELINE_SIZE_64() as int;
    var new_modulus := column * PLATFORM_CACHELINE_SIZE_64() as int + row;
    var i' := i as int - block_modulus + new_modulus;

    assert i' == ref_internal(i) as int;

    var block_modulus' := i' % (PLATFORM_CACHELINE_SIZE_64() as int * PLATFORM_CACHELINE_SIZE_64() as int);

    assert block_modulus' == new_modulus;

    var column' := block_modulus' % PLATFORM_CACHELINE_SIZE_64() as int;
    var row' := block_modulus' / PLATFORM_CACHELINE_SIZE_64() as int;
    var new_modulus' := column' * PLATFORM_CACHELINE_SIZE_64() as int + row';

    assert column == row';
    assert row == column';

    assert i as int == i' - block_modulus' + new_modulus';
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
    i := ref_internal(rc_number as uint32) as int;

    ref_internal_ref_internal(rc_number as uint32);
    ref_internal_bound(rc_number as uint32, config.cache_size as nat);

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

    NonlinearLemmas.mul_le_left(j as int, config.cache_size as int, RC_WIDTH as int - 1);

    calc {
      k;
      {
        NonlinearLemmas.div_mul_plus_mod(k, config.cache_size as int);
      }
      (k / config.cache_size as int) * config.cache_size as int + k % config.cache_size as int;
      {
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

      var rc_number1 := ref_internal(i1 as uint32) as int;
      var rc_number2 := ref_internal(i2 as uint32) as int;

      ref_internal_bound(i1 as uint32, config.cache_size as nat);
      ref_internal_bound(i2 as uint32, config.cache_size as nat);

      var k := rc_index(config, j1 as uint64, i1 as uint32) as int;

      calc {
        i1 as int;
        {
          ref_internal_ref_internal(i1 as uint32);
        }
        ref_internal(rc_number1 as uint32) as int;
        {
          calc {
            rc_number1;
            { Math.abc_mod(j1, config.cache_size as int, rc_number1); }
            k % config.cache_size as int;
            { Math.abc_mod(j2, config.cache_size as int, rc_number2); }
            rc_number2;
          }
        }
        ref_internal(rc_number2 as uint32) as int;
        {
          ref_internal_ref_internal(i2 as uint32);
        }
        i2 as int;
      }

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
