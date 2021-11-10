include "../../lib/Lang/NativeTypes.s.dfy"

module Constants {
  import opened NativeTypes

  const LOG_SIZE: uint64 := 1024 * 1024;
  const WARN_THRESHOLD: uint64 := 0x1000_0000; // 1 << 28

  // Fixed number of replicas (in reference impl, this is variable)
  const NUM_REPLICAS: uint64 := 4;

  // Should be configured to the exact number of threads for best performance
  const MAX_THREADS_PER_REPLICA: uint64 := 256;
  const MAX_PENDING_OPS: uint64 := 1
  const GC_FROM_HEAD: uint64 := MAX_PENDING_OPS * MAX_THREADS_PER_REPLICA;

  // number of reference counts should be equal to the number of expected threads
  function method RC_WIDTH_64() : uint64 { MAX_THREADS_PER_REPLICA }
  ghost const RC_WIDTH := RC_WIDTH_64() as int
}
